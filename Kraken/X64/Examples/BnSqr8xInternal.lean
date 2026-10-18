import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.StateSimp
import Kraken.X64.Examples.BnSqr8xSpec

/-!
# `bn_sqr8x_internal`: BoringSSL multi-precision squaring

In BoringSSL's `x86_64-mont5` (`crypto/fipsmodule/bn/asm/x86_64-mont5.pl`),
`bn_sqr8x_internal` squares an `N`-limb bignum `a` modulo `n` in Montgomery
form. It has a squaring part and a reduction part:

1. Cross-products: `t = Σ_{i<j} a[i]*a[j]*B^(i+j)`, where `B = 2^64`,
   accumulated into a temporary buffer
   `t` on the stack. `.Lsqr4x_1st` initializes the products for the first
   pair of limbs, then each iteration of `.Lsqr4x_outer` takes the next pair of limbs and runs the
   inner loop `.Lsqr4x_inner` over the remaining ones.
2. `.Lsqr4x_shift_n_add`: doubles `t` and adds the diagonal `a[i]*a[i]`.
3. `__bn_sqr8x_reduction` (`.L8x_reduction_loop`, ...): Montgomery reduction of
   `t` by `n`.

The programs below are taken from the generated AT&T source
(`gen/bcm/x86_64-mont5-linux.S`). The `.byte 0x67` prefixes there are only
instruction padding, so they are omitted.

## Status

Verified so far:

* `.Lsqr4x_inner`: termination, no faults, memory safety.
* One two-limb iteration: exact functional
  correctness of both stored limbs and both outgoing carries. The arithmetic
  specification uses natural-number multiplication, quotient, and remainder.
* The complete inner loop: functional
  correctness against a fold of that arithmetic specification over the original
  input and accumulator limbs, for disjoint input and output windows.
* `.Lsqr4x_outer`: termination, no faults, memory safety, and functional
  correctness of the complete nested loop against a pure arithmetic fold over
  the input and accumulator limb arrays. Its postcondition also exposes the
  three words held in registers for the final cross-product phase.
* The first pass: entry setup, a four-limb iteration, the complete loop, and
  carry flushing, with exact arithmetic and memory results.
* The final six cross-products and the two-square diagonal bootstrap.
* The complete four-square diagonal loop and final two-square tail: exact
  doubled cross-product words, added squares, saved carries, and memory updates.
* The eight-limb reduction body and its complete eight-step cancellation loop:
  exact outgoing words, saved coefficients, and next coefficient.
* The complete eight-step tail multiplication loop, including all stored low
  words and the saved carry mask.
* Reduction entry, inter-block additions, branch decisions, carry flushing,
  output stores, and the return fragment.

* The complete reduction CFG, including all cancellation and tail loops.
* The complete `__bn_sqr8x_internal` routine through `ret`:
  `bn_sqr8x_internal_correct` composes the phase contracts with `vcgen`, and
  `bn_sqr8x_internal_safe` derives safety and termination from that contract.

`BnSqr8xContext` records the calling convention and memory assumptions using
`x.length`; `BnSqr8xBlockContext` is its block-count form for implementation proofs.
`bnSqr8xResult` composes the arithmetic folds, and `bnSqr8xPost` specifies the
exact final memory, carry word, and restored registers.
`bn_sqr8x_internal_montgomery_square` connects this result to the integer
equation below for every input satisfying the context. The final conditional
subtraction is outside this routine.

## Numerical contract

`BnSqr8xSpec.lean` states the integer equation independently of these folds. Put
`N = x.length`, `A = BnSqr8x.limbsToNat x`, `M = BnSqr8x.limbsToNat modulus`,
and `R = 2^(64*N)`. The proved equation is `R * Y = A*A + M*Q` for some `Q < R`.
This is Montgomery squaring: the two multiplicands are both `A`.

The `N` little-endian output limbs begin at the **entry** stack pointer plus
`56 + 8*N` bytes. The extra high word is returned in `rax`, so
`Y = limbsToNat(output limbs) + R * rax.toNat`. `bn_sqr8x_internal_output` exposes
that value as `bnSqr8xResultValue`. The final theorem,
`bn_sqr8x_internal_montgomery_square`, establishes `BnSqr8x.MathematicalPost`
directly for the returned machine state.

The arithmetic refinement first proves that the cross-product and diagonal
phases produce exactly `A*A`. It then proves that every reduction pass preserves
the integer equation while accumulating the bounded coefficient `Q`. These
proofs cover arbitrary positive `blocks`; executable examples are additional
checks, not premises of the theorem.

In a triple `⦃ P ⦄ program ⦃ Q; E ⦄`, `Q` describes falling through the end of
`program`, while `E pc s` describes leaving it at address `pc` in state `s`.
Thus `fun _ _ => False` forbids fallthrough. The exit condition `pc = ra`
requires the routine to return to its caller; it does not make the precondition
false or the correctness theorem vacuous.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

attribute [local sym_simp] Option.map_none Option.map_some
attribute [local grind norm]
  Option.map_none Option.map_some
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
  Width.scaleFactor_W8 BitVec.mul_one BitVec.add_zero
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk

/-! ## `.Lsqr4x_inner`

The inner loop of the cross-products. It multiplies a 2-limb pair held in
`(%r14, %r15)` against the remaining limbs of `a`, two limbs (`16` bytes) at a
time, accumulating into `t` with a 2-limb carry chain in
`(%r10, %r11, %r12, %r13)`.

Both pointers `%rsi` (into `a`) and `%rdi` (into `t`) point to the **end** of
their `L`-byte windows, while `%rcx` is initialized from `%rbp = -L`
(`lea (%rbp), %rcx`) and steps upward by `16` bytes per iteration
(`leaq 16(%rcx), %rcx`) until it wraps to `0` (`cmpq $0, %rcx;
jne .Lsqr4x_inner`).

We prove that for any positive multiple `L` of `16` bytes (`L < 2 ^ 63`), one
run of the loop terminates without faulting, reads only within the `L` bytes
before `%rsi` and `%rdi`, and preserves the `L`-byte output region
`[%rdi - L, %rdi)` (while allowing the input region `[%rsi - L, %rsi)` to alias
or overlap other read-only regions via `Mem.SubDom`).
-/

section Sqr4xInner

/-- The 33-instruction body of the `.Lsqr4x_inner` loop of `bn_sqr8x_internal`
(`x86_64-mont5-linux.S`). Initialization, the comparison, and the back edge belong
to the enclosing `sqr4x_inner_prog`.

The perl source (`x86_64-mont5.pl`, the `bn_power5_nohw` section) names the registers as follows:

| perlasm  | register | role in `.Lsqr4x_inner`                                       |
|----------|----------|---------------------------------------------------------------|
| `$aptr`  | `%rsi`   | end of the window of input limbs `a[]`                        |
| `$rptr`  | `%rdi`   | end of the window of the accumulator `t[]`                    |
| `$tptr`  | `%rdi`   | the same as $rptr                                             |
| `$i`     | `%rbp`   | initial negative byte offset `-L` into both windows           |
| `$j`     | `%rcx`   | running negative byte offset, `+16` per iteration up to `0`   |
| `$a0`    | `%r14`   | loop-invariant multiplier limb, applied to the limb just read |
| `$a1`    | `%r15`   | loop-invariant multiplier limb, applied to the previous limb  |
| `$ai`    | `%rbx`   | the limb just read from `($aptr,$j)` / `8($aptr,$j)`          |
| `$A0[0]` | `%r10`   | two-word accumulator/carry of the `$a0` products              |
| `$A0[1]` | `%r11`   | (the two words swap low/high roles each half-iteration)       |
| `$A1[0]` | `%r12`   | two-word accumulator/carry of the `$a1` products              |
| `$A1[1]` | `%r13`   | (likewise)                                                    |
-/
def sqr4x_inner_iteration : Program := parse("
    movq (%rsi,%rcx,1),%rbx
    mulq %r15
    addq %rax,%r13
    movq %rbx,%rax
    movq %rdx,%r12
    adcq $0,%r12
    addq (%rdi,%rcx,1),%r13
    adcq $0,%r12

    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    movq 8(%rsi,%rcx,1),%rbx
    movq %rdx,%r10
    adcq $0,%r10
    addq %r13,%r11
    adcq $0,%r10

    mulq %r15
    addq %rax,%r12
    movq %r11,(%rdi,%rcx,1)
    movq %rbx,%rax
    movq %rdx,%r13
    adcq $0,%r13
    addq 8(%rdi,%rcx,1),%r12
    leaq 16(%rcx),%rcx
    adcq $0,%r13

    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    adcq $0,%rdx
    addq %r12,%r10
    movq %rdx,%r11
    adcq $0,%r11
    movq %r10,-8(%rdi,%rcx,1)
")

/-- The `.Lsqr4x_inner` loop body, comparison, and back edge. -/
def sqr4x_inner_loop : Program :=
  parse(".Lsqr4x_inner:\n") ++ sqr4x_inner_iteration ++ parse("
    cmpq $0,%rcx
    jne .Lsqr4x_inner
")

/-- The inner loop, with index initialization and its comparison and back edge. -/
def sqr4x_inner_prog : Program :=
  parse("
start:
    lea (%rbp),%rcx
") ++ sqr4x_inner_loop

/-! ### The proof -/

/-- The safety invariant: `%rdi` and `%rsi` remain at the end of
the `L`-byte slices, `%rcx` is a negative 16-byte-aligned offset in
`[2 ^ 64 - L, 2 ^ 64)`, the output block `[%rdi - L, %rdi)` is preserved, and
every initially mapped address remains mapped (`Mem.SubDom d.dmem s.dmem`). -/
private abbrev sqr4x_inner_safey (d : MachineData) (L : Nat) (R : DataMem → Prop)
    (s : MachineData) : Prop :=
  let rcx := (s.regs.get64 .rcx).toNat
  s.regs.get64 .rdi = d.regs.get64 .rdi ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  2 ^ 64 - L ≤ rcx ∧ rcx < 2 ^ 64 ∧ rcx % 16 = 0 ∧
  (s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R) ∧
  Mem.SubDom d.dmem s.dmem

/-- Both proofs use the same entry state and labels, with their respective loop
invariants supplied as `I`. -/
private abbrev sqr4x_inner_table (d : MachineData) (I : MachineData → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | ".Lsqr4x_inner", s => I s
  | _, _ => False

/-- The loop variant: the distance `2 ^ 64 - %rcx` remaining until `%rcx` wraps
to `0` at the end of the `L`-byte slice. -/
private abbrev sqr4x_inner_var : Label → MachineData → Nat
  | "start", _ => 2 ^ 64
  | ".Lsqr4x_inner", s => 2 ^ 64 - (s.regs.get64 .rcx).toNat
  | _, _ => 0

variable [layout : _root_.Layout] [validLayout : Executable.ValidLayout (layout sqr4x_inner_prog)]

/-- The ambient code of the example: `sqr4x_inner_prog`, laid out. -/
local instance sqr4x_inner.env : CodeEnv := ⟨layout sqr4x_inner_prog⟩

theorem sqr4x_inner_safe (d : MachineData) (L : Nat)
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 L)
    (h_L_mod : L % 16 = 0) (h_L_pos : 0 < L) (h_L_bound : L < 2 ^ 63)
    (R R₀ : DataMem → Prop)
    (h_t : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R)
    (h_a : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi - BitVec.ofNat 64 L, L)] ⋆ R₀) :
    ⦃ fun s => s = d ⦄
      sqr4x_inner_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R ⦄ := by
  apply MachineWP.cfg (sqr4x_inner_table d (sqr4x_inner_safey d L R)) sqr4x_inner_var
  cfg_cases [sqr4x_inner_prog, sqr4x_inner_loop, sqr4x_inner_iteration]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

theorem sqr4x_inner_terminates_and_safe
    (s₀ : MachineData) (L : Nat)
    (h_rbp : s₀.regs.rbp.toBitVec = 0#64 - BitVec.ofNat 64 L)
    (h_L_mod : L % 16 = 0) (h_L_pos : 0 < L) (h_L_bound : L < 2 ^ 63)
    (R R₀ : DataMem → Prop)
    (h_t : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec - BitVec.ofNat 64 L, L)] ⋆ R)
    (h_a : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rsi.toBitVec - BitVec.ofNat 64 L, L)] ⋆ R₀) :
    Eventually (straightlineStep (layout sqr4x_inner_prog))
      (fun s' => s'.1.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec - BitVec.ofNat 64 L, L)] ⋆ R)
      (s₀, Kraken.Layout.start Directive) :=
  Program.run_of_triple (sqr4x_inner_safe s₀ L h_rbp h_L_mod h_L_pos h_L_bound R R₀ h_t h_a) rfl

-- Keep the arithmetic and body lemmas independent of the enclosing layout.
omit layout validLayout

/-! ## Functional correctness of one iteration

The control-flow proof above deliberately forgets memory contents. To test the
value-level obligations separately, verify one complete body against a pure
arithmetic specification. A small multiply-add lemma accounts for the two carries
of each chain. The machine proof then uses the same instruction specifications as
the safety proof; local normalization lemmas let `finish` match the arithmetic
specification to the instruction results.
-/

open Std Std.ExtHashMap

/-! ### Arithmetic of `mul`, `add`, and `adc` -/

private abbrev mulHi (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.unsigned * b.unsigned) >>> 64)

private theorem mul_wide_eq (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (mulHi a b).toNat = a.toNat * b.toNat := by
  simp [mulHi, BitVec.unsigned_eq, Int.shiftRight_eq_div_pow]
  have h := BitVec.toNat_mul_toNat_lt (x := a) (y := b)
  omega

private abbrev addCarry (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a + b).unsigned != a.unsigned + b.unsigned).toNat

private theorem add_with_carry_eq (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (addCarry a b).toNat = a.toNat + b.toNat := by
  simp [addCarry, BitVec.unsigned_eq, Bool.toNat]
  split <;> omega

private abbrev macLo (a b c t : BitVec 64) := t + (a * b + c)
private abbrev macHi (a b c t : BitVec 64) :=
  (mulHi a b + addCarry (a * b) c) + addCarry t (a * b + c)

private theorem mul_add_words_eq (a b c t : BitVec 64) :
    (macLo a b c t).toNat + 2 ^ 64 * (macHi a b c t).toNat =
      a.toNat * b.toNat + c.toNat + t.toNat := by
  have hp := mul_wide_eq a b
  have h1 := add_with_carry_eq (a * b) c
  have h2 := add_with_carry_eq t (a * b + c)
  have hbound := Nat.mul_le_mul (Nat.le_sub_one_of_lt a.isLt) (Nat.le_sub_one_of_lt b.isLt)
  simp only [macLo, macHi, BitVec.toNat_add]
  omega

private theorem mac_lo (a b c t : BitVec 64) :
    macLo a b c t = BitVec.ofNat 64 ((a.toNat * b.toNat + c.toNat + t.toNat) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have h := mul_add_words_eq a b c t
  simp only [BitVec.toNat_ofNat]
  omega

private theorem mac_hi (a b c t : BitVec 64) :
    macHi a b c t = BitVec.ofNat 64 ((a.toNat * b.toNat + c.toNat + t.toNat) / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have h := mul_add_words_eq a b c t
  simp only [BitVec.toNat_ofNat]
  omega

/-! ### The first store preserves the adjacent accumulator limb -/

private theorem load_after_disjoint_store (m : DataMem) (a b : BitVec 64) (v : Int)
    (hdisj : ∀ i < 8, ∀ j < 8, b + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j) :
    (m.storeInt a 8 v).loadInt b 8 = m.loadInt b 8 := by
  simp only [Mem.loadInt, Mem.loadBytes]
  congr 2
  apply List.map_congr_left
  intro i hi
  have hn : ¬ b + BitVec.ofNat 64 i ∈ (Int.toBytes 8 v).At a := by
    rw [mem_At_iff]
    rintro ⟨j, hj, heq⟩
    exact hdisj i (List.mem_range.mp hi) j (by simpa only [Int.toBytes_length] using hj) heq
  simp only [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, union_eq, getElem?_union,
    getElem?_eq_none hn, Option.none_or]

@[grind =] private theorem load_after_store_next (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt (a + 8) 8 = m.loadInt (a + 8) 8 := by
  apply load_after_disjoint_store
  grind

/-! ### The arithmetic specification and the machine proof -/

/-- Decompose `a * b + c + t` into its low limb and carry in base `2 ^ 64`. -/
def sqr4xMac (a b c t : BitVec 64) : BitVec 64 × BitVec 64 :=
  let n := a.toNat * b.toNat + c.toNat + t.toNat
  (BitVec.ofNat 64 (n % 2 ^ 64), BitVec.ofNat 64 (n / 2 ^ 64))

private theorem sqr4xMac_eq (a b c t : BitVec 64) :
    sqr4xMac a b c t = (macLo a b c t, macHi a b c t) := by
  apply Prod.ext
  · exact (mac_lo a b c t).symm
  · exact (mac_hi a b c t).symm

/-- The two output limbs and the independent carries of the two product chains. -/
structure Sqr4xInnerResult where
  out0 : BitVec 64
  out1 : BitVec 64
  carry0 : BitVec 64
  carry1 : BitVec 64

/-- One two-limb iteration, specified with natural-number multiply-adds.
`previous` is the entry `%rax`, `c0` is `%r11`, and `c1` is `%r13`.
The multipliers `a0` and `a1` come from `%r14` and `%r15`; `x0`, `x1`
and `t0`, `t1` are the two input and accumulator limbs loaded in this iteration. -/
def sqr4xInnerResult (a0 a1 previous c0 c1 x0 x1 t0 t1 : BitVec 64) : Sqr4xInnerResult :=
  let u := sqr4xMac previous a1 c1 t0
  let v := sqr4xMac x0 a0 c0 u.1
  let w := sqr4xMac x0 a1 u.2 t1
  let z := sqr4xMac x1 a0 v.2 w.1
  ⟨v.1, z.1, z.2, w.2⟩

/-- Specialize the arithmetic specification to the iteration's entry state. -/
private abbrev iterationResult (d : MachineData) (x0 x1 t0 t1 : Int) :=
  sqr4xInnerResult (d.regs.get64 .r14) (d.regs.get64 .r15) (d.regs.get64 .rax)
    (d.regs.get64 .r11) (d.regs.get64 .r13)
    (BitVec.ofInt 64 x0) (BitVec.ofInt 64 x1) (BitVec.ofInt 64 t0) (BitVec.ofInt 64 t1)

attribute [local sym_simp] BitVec.zero_add

attribute [local grind unfold] sqr4xInnerResult
attribute [local grind norm]
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev

/-- Functional correctness of a complete two-limb body, for arbitrary input,
multiplier, and carry values. The four load hypotheses also provide memory safety.
Input/output aliasing is allowed: both input limbs are loaded before either store.
The exact memory equality describes both writes and preserves every other byte.

`vcgen` executes the body, then `finish` unfolds the specification and rewrites its
mathematical multiply-adds into word operations using the local normalization rules.
No additional case splitting is needed during the main proof search. -/
theorem sqr4x_inner_iteration_correct [CodeEnv] (d : MachineData) (x0 x1 t0 t1 : Int)
    (h_x0 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx) 8 = some x0)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx + 8) 8 = some x1)
    (h_t0 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx) 8 = some t0)
    (h_t1 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx + 8) 8 = some t1) :
    ⦃ fun s => s = d ⦄ sqr4x_inner_iteration ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r14 = d.regs.get64 .r14 ∧
      s.regs.get64 .r15 = d.regs.get64 .r15 ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x1 ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx + 16 ∧
      s.regs.get64 .r11 = (iterationResult d x0 x1 t0 t1).carry0 ∧
      s.regs.get64 .r13 = (iterationResult d x0 x1 t0 t1).carry1 ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi + d.regs.get64 .rcx) 8
        (iterationResult d x0 x1 t0 t1).out0.toIntOpaque).storeInt
          (d.regs.get64 .rdi + d.regs.get64 .rcx + 8) 8
          (iterationResult d x0 x1 t0 t1).out1.toIntOpaque ⦄ := by
  vcgen [sqr4x_inner_iteration] simplifying_assumptions with
    finish (splits := 0)

private theorem sqr4xMac_parts (a b c t : BitVec 64) :
    (sqr4xMac a b c t).1.toNat + 2 ^ 64 * (sqr4xMac a b c t).2.toNat =
      a.toNat * b.toNat + c.toNat + t.toNat := by
  rw [sqr4xMac_eq]
  exact mul_add_words_eq a b c t

/-- The two stored limbs and the two outgoing carries account for the entire
unbounded integer sum; this is stronger than equality modulo 2 ^ 128. -/
theorem sqr4xInnerResult_arithmetic (a0 a1 previous c0 c1 x0 x1 t0 t1 : BitVec 64) :
    let r := sqr4xInnerResult a0 a1 previous c0 c1 x0 x1 t0 t1
    r.out0.toNat + 2 ^ 64 * r.out1.toNat + 2 ^ 128 * (r.carry0.toNat + r.carry1.toNat) =
      t0.toNat + 2 ^ 64 * t1.toNat +
      (x0.toNat + 2 ^ 64 * x1.toNat) * a0.toNat +
      (previous.toNat + 2 ^ 64 * x0.toNat) * a1.toNat + c0.toNat + c1.toNat := by
  let u := sqr4xMac previous a1 c1 t0
  let v := sqr4xMac x0 a0 c0 u.1
  let w := sqr4xMac x0 a1 u.2 t1
  let z := sqr4xMac x1 a0 v.2 w.1
  have hu := sqr4xMac_parts previous a1 c1 t0
  have hv := sqr4xMac_parts x0 a0 c0 u.1
  have hw := sqr4xMac_parts x0 a1 u.2 t1
  have hz := sqr4xMac_parts x1 a0 v.2 w.1
  change u.1.toNat + 2 ^ 64 * u.2.toNat = _ at hu
  change v.1.toNat + 2 ^ 64 * v.2.toNat = _ at hv
  change w.1.toNat + 2 ^ 64 * w.2.toNat = _ at hw
  change z.1.toNat + 2 ^ 64 * z.2.toNat = _ at hz
  change v.1.toNat + 2 ^ 64 * z.1.toNat + 2 ^ 128 * (z.2.toNat + w.2.toNat) = _
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-! ## Functional correctness of the complete inner loop

The invariant records the reference result after `k` pairs, including the exact
memory contents. Unprocessed accumulator limbs and all input limbs still have
their initial values. The body advances the invariant to `k + 1`; the comparison
then either exits at `k + 1 = n` or takes a back edge with a smaller variant.
-/

/-- The arithmetic carry state and memory after a prefix of the inner loop. -/
structure Sqr4xInnerState where
  previous : BitVec 64
  carry0 : BitVec 64
  carry1 : BitVec 64
  memory : DataMem

/-- Reference computation for `k` pairs of limbs. `x` and `t` are the arrays of
original input and accumulator limbs; `base` is the first output address.
Each step uses the natural-number specification `sqr4xInnerResult`. -/
def sqr4xInnerFold (a0 a1 : BitVec 64) (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xInnerState) : Nat → Sqr4xInnerState
  | 0 => initial
  | k + 1 =>
    let s := sqr4xInnerFold a0 a1 x t base initial k
    let r := sqr4xInnerResult a0 a1 s.previous s.carry0 s.carry1
      (x.getD (2 * k) 0) (x.getD (2 * k + 1) 0) (t.getD (2 * k) 0) (t.getD (2 * k + 1) 0)
    ⟨x.getD (2 * k + 1) 0, r.carry0, r.carry1,
      (s.memory.storeInt (base + BitVec.ofNat 64 (16 * k)) 8 r.out0.toIntOpaque).storeInt
        (base + BitVec.ofNat 64 (16 * k) + 8) 8 r.out1.toIntOpaque⟩

private theorem fold_load_unchanged (a0 a1 : BitVec 64) (x t : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr4xInnerState) (k : Nat) (addr : BitVec 64)
    (hdisj : ∀ i < 8, ∀ j < 16 * k,
      addr + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    (sqr4xInnerFold a0 a1 x t base initial k).memory.loadInt addr 8 =
      initial.memory.loadInt addr 8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sqr4xInnerFold]
    dsimp only
    rw [load_after_disjoint_store]
    · rw [load_after_disjoint_store]
      · apply ih
        intro i hi j hj
        exact hdisj i hi j (by omega)
      · intro i hi j hj
        simpa [BitVec.ofNat_add, BitVec.add_assoc] using
          hdisj i hi (16 * k + j) (by omega)
    · intro i hi j hj
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using
        hdisj i hi (16 * k + (8 + j)) (by omega)

private theorem word_before_disjoint (base : BitVec 64) (k j : Nat)
    (hkj : 16 * k ≤ 8 * j) (hbound : 8 * j + 8 ≤ 2 ^ 64) :
    ∀ i < 8, ∀ l < 16 * k,
      base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 l := by
  grind only [= BitVec.toNat_ofNatLT]

/-- Expected state after `k` of the `n` two-limb iterations, starting with the
entry `%rax`, `%r11`, and `%r13`. The input window starts `16 * n` bytes before
`%rsi`, and the output window starts `16 * n` bytes before `%rdi`. -/
def sqr4xInnerPrefix (d : MachineData) (n : Nat) (x t : List (BitVec 64)) (k : Nat) :
    Sqr4xInnerState :=
  sqr4xInnerFold (d.regs.get64 .r14) (d.regs.get64 .r15) x t
    (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))
    ⟨d.regs.get64 .rax, d.regs.get64 .r11, d.regs.get64 .r13, d.dmem⟩ k

@[local grind =] private theorem prefix_zero (d : MachineData) (n : Nat) (x t : List (BitVec 64)) :
    sqr4xInnerPrefix d n x t 0 =
      ⟨d.regs.get64 .rax, d.regs.get64 .r11, d.regs.get64 .r13, d.dmem⟩ := rfl

/-- Keep a named offset so counter lemmas match before arithmetic normalization. -/
private def innerOffset (n k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (16 * k) - BitVec.ofNat 64 (16 * n)

private abbrev innerMatches (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (k : Nat) (s : MachineData) : Prop :=
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi ∧
  s.regs.get64 .r14 = d.regs.get64 .r14 ∧
  s.regs.get64 .r15 = d.regs.get64 .r15 ∧
  s.regs.get64 .rax = (sqr4xInnerPrefix d n x t k).previous ∧
  s.regs.get64 .rcx = innerOffset n k ∧
  s.regs.get64 .r11 = (sqr4xInnerPrefix d n x t k).carry0 ∧
  s.regs.get64 .r13 = (sqr4xInnerPrefix d n x t k).carry1 ∧
  s.dmem = (sqr4xInnerPrefix d n x t k).memory

/-- Number of completed pairs, recovered from the running byte offset. -/
private def innerIndex (n : Nat) (rcx : BitVec 64) : Nat := n - (2 ^ 64 - rcx.toNat) / 16

private abbrev innerInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  innerIndex n (s.regs.get64 .rcx) < n ∧ innerMatches d n x t (innerIndex n (s.regs.get64 .rcx)) s

/-! ### Limb arrays in memory

An array of limbs `xs` occupies the little-endian bytes
`xs.flatMap fun w => Int.toBytes 8 w.toInt`. A separating conjunction of the two
windows gives every limb load and the bytewise disjointness of the windows. -/

private theorem length_flatMap_limbs (xs : List (BitVec 64)) :
    (xs.flatMap fun w => Int.toBytes 8 w.toInt).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    simp only [List.flatMap_cons, List.length_append, Int.toBytes_length, ih, List.length_cons]
    omega

private theorem limb_of_flatMap (xs : List (BitVec 64)) (j : Nat) (hj : j < xs.length) :
    ((xs.flatMap fun w => Int.toBytes 8 w.toInt).drop (8 * j)).take 8
      = Int.toBytes 8 (xs.getD j 0).toInt := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons w xs ih =>
    cases j with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getD_cons_zero]
      exact List.take_left' (Int.toBytes_length _ _)
    | succ j =>
      rw [List.flatMap_cons, show 8 * (j + 1) = 8 + 8 * j by omega, ← List.drop_drop,
        List.drop_left' (Int.toBytes_length _ _), List.getD_cons_succ]
      exact ih j (by simp only [List.length_cons] at hj; omega)

private theorem load_limb {xs : List (BitVec 64)} {a : BitVec 64} {F : DataMem → Prop}
    {m : DataMem} (h : m =⋆ Eq ((xs.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆ F)
    (hlen : 8 * xs.length < 2 ^ 64) (j : Nat) (hj : j < xs.length) :
    m.loadInt (a + BitVec.ofNat 64 (8 * j)) 8
      = some (Int.ofBytes (Int.toBytes 8 (xs.getD j 0).toInt)) := by
  have hoff : (a + BitVec.ofNat 64 (8 * j) - a).toNat = 8 * j := by
    rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  rw [Mem.loadInt_slice h (by rw [hoff, length_flatMap_limbs]; omega)
    (by rw [length_flatMap_limbs]; omega), hoff, limb_of_flatMap xs j hj]

private theorem sep_At_ne {X T : List UInt8} {a b : BitVec 64} {R : DataMem → Prop}
    {m : DataMem} (h : m =⋆ Eq (X.At a) ⋆ (Eq (T.At b) ⋆ R)) :
    ∀ i < X.length, ∀ j < T.length, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j := by
  intro i hi j hj heq
  obtain ⟨_, _, -, hAB, rfl, _, D, rfl, -, rfl, -⟩ := h
  have hmem : a + BitVec.ofNat 64 i ∈ (X.At a).inter ((T.At b).union D) :=
    mem_inter_iff.2 ⟨(mem_At_iff _ _ _).2 ⟨i, hi, rfl⟩,
      mem_union_iff.2 (Or.inl ((mem_At_iff _ _ _).2 ⟨j, hj, heq⟩))⟩
  rw [hAB] at hmem
  exact not_mem_empty hmem

/-- Every limb of `x` read as an `Int`, as the loads of the loop return it. -/
@[local grind =] private theorem ofInt_limb (v : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toInt)) = v :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v

private theorem prefix_loads (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 16 * n < 2 ^ 63)
    (hxl : x.length = 2 * n) (htl : t.length = 2 * n)
    (hmem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))) ⋆ R))
    (k j : Nat) (hkj : 2 * k ≤ j) (hj : j < 2 * n) :
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 (8 * j)) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toInt)) ∧
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 (8 * j)) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD j 0).toInt)) := by
  constructor
  · rw [sqr4xInnerPrefix, fold_load_unchanged]
    · exact load_limb hmem (by omega) j (by omega)
    · intro i hi l hl
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using
        sep_At_ne hmem (8 * j + i) (by rw [length_flatMap_limbs]; omega) l
          (by rw [length_flatMap_limbs]; omega)
  · rw [sqr4xInnerPrefix, fold_load_unchanged]
    · exact load_limb (by rwa [sep_comm_l] at hmem) (by omega) j (by omega)
    · exact word_before_disjoint _ k j (by omega) (by omega)

private theorem offset_toNat (n k : Nat) (hk : k < n) (hn : 16 * n < 2 ^ 63) :
    (innerOffset n k).toNat = 2 ^ 64 - 16 * (n - k) := by
  simp only [innerOffset, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Counter facts used by `finish`: zero means completion; otherwise the byte
distance gives both the loop variant and the completed-pair index. -/
private theorem offset_facts (n k : Nat) (hk : k ≤ n) (hn : 16 * n < 2 ^ 63) :
    (innerOffset n k = 0#64 ↔ k = n) ∧
    (k < n → (innerOffset n k).toNat = 2 ^ 64 - 16 * (n - k) ∧
      innerIndex n (innerOffset n k) = k) := by
  grind [innerOffset, innerIndex, offset_toNat]

@[local grind =] private theorem offset_initial_index (n : Nat) (hn : 0 < n) (hb : 16 * n < 2 ^ 63) :
    innerIndex n (0#64 - BitVec.ofNat 64 (16 * n)) = 0 := by
  grind only [innerIndex, = BitVec.toNat_ofNatLT]

-- Instantiate the bundled counter facts whenever an offset is encountered.
local grind_pattern offset_facts => innerOffset n k

@[local grind =] private theorem offset_step (n k : Nat) :
    innerOffset n k + 16 = innerOffset n (k + 1) := by
  simp only [innerOffset, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
  grind

/-- On a taken back edge, advance the pair index and decrease the byte-distance
variant. Supplying these conclusions directly avoids speculative arithmetic splits. -/
private theorem offset_continue (n k : Nat) (hk : k < n) (hn : 16 * n < 2 ^ 63)
    (hne : (innerOffset n k + 16).toNat ≠ 0) :
    k + 1 < n ∧ innerIndex n (innerOffset n k + 16) = k + 1 ∧
      2 ^ 64 - (innerOffset n k + 16).toNat < 2 ^ 64 - (innerOffset n k).toNat := by
  grind only [= offset_step, usr offset_facts]

local grind_pattern offset_continue => innerOffset n k + 16

/-- One step of the arithmetic fold, using the same addresses as the assembly. -/
@[local grind =] private theorem prefix_step (d : MachineData) (n : Nat) (x t : List (BitVec 64)) (k : Nat) :
    sqr4xInnerPrefix d n x t (k + 1) =
      let s := sqr4xInnerPrefix d n x t k
      let r := sqr4xInnerResult (d.regs.get64 .r14) (d.regs.get64 .r15)
        s.previous s.carry0 s.carry1
        (x.getD (2 * k) 0) (x.getD (2 * k + 1) 0)
        (t.getD (2 * k) 0) (t.getD (2 * k + 1) 0)
      ⟨x.getD (2 * k + 1) 0, r.carry0, r.carry1,
        (s.memory.storeInt (d.regs.get64 .rdi + innerOffset n k) 8 r.out0.toIntOpaque).storeInt
          (d.regs.get64 .rdi + innerOffset n k + 8) 8 r.out1.toIntOpaque⟩ := by
  simp only [sqr4xInnerPrefix, sqr4xInnerFold, innerOffset]
  congr 3 <;> grind

/-- The next four reads still see the original limbs. Indexing this fact by the
entry counter lets `grind` match it to the current loop state; the frame `R` is
bound by the memory fact, so the lemma fires from the theorem's hypotheses. -/
private theorem prefix_iteration_loads (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 16 * n < 2 ^ 63)
    (hxl : x.length = 2 * n) (htl : t.length = 2 * n)
    (hmem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))) ⋆ R))
    (s : MachineData) (hk : innerIndex n (s.regs.get64 .rcx) < n) :
    let k := innerIndex n (s.regs.get64 .rcx)
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rsi + innerOffset n k) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * k) 0).toInt)) ∧
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rsi + innerOffset n k + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * k + 1) 0).toInt)) ∧
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rdi + innerOffset n k) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (2 * k) 0).toInt)) ∧
    (sqr4xInnerPrefix d n x t k).memory.loadInt
      (d.regs.get64 .rdi + innerOffset n k + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (2 * k + 1) 0).toInt)) := by
  let k := innerIndex n (s.regs.get64 .rcx)
  have h0 := prefix_loads d n x t R hbound hxl htl hmem k (2 * k) (by omega) (by omega)
  have h1 := prefix_loads d n x t R hbound hxl htl hmem k (2 * k + 1) (by omega) (by omega)
  grind only [innerOffset, BitVec.ofNat_add]

-- Fire the load lemma on the loop state's fold, with the frame from the memory fact.
local grind_pattern prefix_iteration_loads =>
  sqr4xInnerPrefix d n x t (innerIndex n (s.regs.get64 .rcx)),
  Std.ExtHashMap.sep (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))))
    (Std.ExtHashMap.sep (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n)))) R) d.dmem

include layout validLayout

/-- Functional correctness of the entire inner loop for `n` pairs of limbs.

The arrays `x` and `t` of `2 * n` limbs are the original input and accumulator
windows, owned in a separating conjunction; ownership provides memory safety and
makes the windows disjoint, so earlier output stores cannot change later input
loads. Addresses may wrap around the address space; the length bound ensures that
distinct offsets within a window do not alias.

The result is the pure arithmetic fold `sqr4xInnerPrefix ... n`, including both
carry chains and every output write. The initial previous limb is the entry
`%rax`; this fragment does not load that limb itself. At subsequent iterations,
the fold takes `previous` from the preceding pair's second input limb.

`MachineWP.cfg` supplies loop induction and termination. `vcgen` processes every
instruction after `cfg_cases` unfolds the program. Local `grind` rules expand the
arithmetic fold and connect the counter to its index and termination measure.
The memory lemma `prefix_iteration_loads` fires on the loop state's fold and the
ownership hypothesis, which supplies the frame.

This proof shares arithmetic and memory lemmas with the one-iteration proof and
shares the label table, variant, and code environment with `sqr4x_inner_correct`.
Its stronger invariant tracks the values that the safety postcondition omits. -/
theorem sqr4x_inner_prog_correct (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 (16 * n))
    (h_pos : 0 < n) (h_bound : 16 * n < 2 ^ 63)
    (h_x_len : x.length = 2 * n) (h_t_len : t.length = 2 * n) (R : DataMem → Prop)
    (h_mem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))) ⋆ R)) :
    ⦃ fun s => s = d ⦄ sqr4x_inner_prog ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r14 = d.regs.get64 .r14 ∧
      s.regs.get64 .r15 = d.regs.get64 .r15 ∧
      s.regs.get64 .rax = (sqr4xInnerPrefix d n x t n).previous ∧
      s.regs.get64 .rcx = 0#64 ∧
      s.regs.get64 .r11 = (sqr4xInnerPrefix d n x t n).carry0 ∧
      s.regs.get64 .r13 = (sqr4xInnerPrefix d n x t n).carry1 ∧
      s.dmem = (sqr4xInnerPrefix d n x t n).memory ⦄ := by
  apply MachineWP.cfg (sqr4x_inner_table d (innerInvariant d n x t)) sqr4x_inner_var
  cfg_cases [sqr4x_inner_prog, sqr4x_inner_loop, sqr4x_inner_iteration]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish (splits := 0)

end Sqr4xInner

/-! ## `.Lsqr4x_outer`

The outer loop of the cross-products (`x86_64-mont5-linux.S`, lines 1431–1534).
Each outer iteration handles the next two limbs of `a`:

1. `.Lsqr4x_outer` (preamble): loads the four edge limbs at negative offsets
   `-32`, `-24`, `-16`, `-8` from `(%rsi, %rbp)`, computes the end of the
   `tp[]` window `56(%rsp, %r9, 2) + %rbp - 32` into `%rdi`, accumulates the
   three startup products into `-24(%rdi, %rbp)`, `-16(%rdi, %rbp)`, and
   `-8(%rdi, %rbp)`, initializes `%rcx := %rbp`, and jumps into `.Lsqr4x_inner`.
2. `.Lsqr4x_inner` + tail: runs `sqr4x_inner_iteration` as `%rcx` steps by `16`
   bytes up to `0`, then stores the two final carry words at `(%rdi)` and
   `8(%rdi)`, advances `%rbp` by `16`, and loops back to `.Lsqr4x_outer` until
   `%rbp` reaches `0`.
-/

section Sqr4xOuter

attribute [local grind norm] Width.scaleFactor_W16

@[local grind norm] private theorem bv_add_zero (x : BitVec 64) : x + 0 = x := BitVec.add_zero x

/-- The 40-instruction preamble at `.Lsqr4x_outer`, ending with `jmp .Lsqr4x_inner`. -/
def sqr4x_outer_preamble : Program := parse("
    movq -32(%rsi,%rbp,1),%r14
    leaq 56(%rsp,%r9,2),%rdi
    movq -24(%rsi,%rbp,1),%rax
    leaq -32(%rdi,%rbp,1),%rdi
    movq -16(%rsi,%rbp,1),%rbx
    movq %rax,%r15

    mulq %r14
    movq -24(%rdi,%rbp,1),%r10
    addq %rax,%r10
    movq %rbx,%rax
    adcq $0,%rdx
    movq %r10,-24(%rdi,%rbp,1)
    movq %rdx,%r11

    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    adcq $0,%rdx
    addq -16(%rdi,%rbp,1),%r11
    movq %rdx,%r10
    adcq $0,%r10
    movq %r11,-16(%rdi,%rbp,1)

    xorq %r12,%r12

    movq -8(%rsi,%rbp,1),%rbx
    mulq %r15
    addq %rax,%r12
    movq %rbx,%rax
    adcq $0,%rdx
    addq -8(%rdi,%rbp,1),%r12
    movq %rdx,%r13
    adcq $0,%r13

    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    adcq $0,%rdx
    addq %r12,%r10
    movq %rdx,%r11
    adcq $0,%r11
    movq %r10,-8(%rdi,%rbp,1)

    leaq (%rbp),%rcx
    jmp .Lsqr4x_inner
")

/-- The 10-instruction tail after `.Lsqr4x_inner` that flushes the carry chain
into `(%rdi)` and `8(%rdi)`, advances `%rbp`, and loops back to `.Lsqr4x_outer`. -/
def sqr4x_outer_tail : Program := parse("
    mulq %r15
    addq %rax,%r13
    adcq $0,%rdx
    addq %r11,%r13
    adcq $0,%rdx

    movq %r13,(%rdi)
    movq %rdx,%r12
    movq %rdx,8(%rdi)

    addq $16,%rbp
    jnz .Lsqr4x_outer
")

/-- The complete `.Lsqr4x_outer` nested loop, entered via `jmp .Lsqr4x_outer`. -/
def sqr4x_outer_prog : Program :=
  parse("
start:
    jmp .Lsqr4x_outer
.Lsqr4x_outer:
") ++ sqr4x_outer_preamble ++ sqr4x_inner_loop ++ sqr4x_outer_tail

/-! ### Memory bounds for outer-loop and inner-loop accesses -/

private theorem inside_of_sub_eq {addr base x : BitVec 64} {M len : Nat}
    (hsub : addr - base = BitVec.ofNat 64 M + x)
    (h : 2 ^ 64 ≤ M + x.toNat ∧ M + x.toNat - 2 ^ 64 + 8 ≤ len) :
    Mem.Blocks.Inside addr 8 [(base, len)] := by
  refine Or.inl ?_
  rw [hsub]
  grind only [= BitVec.toNat_add, = BitVec.toNat_ofNat]

private theorem blocks_inside_a_disp (rsi idx d : BitVec 64) (L : Nat)
    (h_idx_ge : 2 ^ 64 - L ≤ idx.toNat) (h_idx_mod : idx.toNat % 16 = 0)
    (h_L_bound : 2 * L + 64 < 2 ^ 63) (hd : (32#64 + d).toNat ≤ 40) :
    Mem.Blocks.Inside (rsi + idx + d) 8
      [(rsi - BitVec.ofNat 64 (L + 32), L + 32)] :=
  inside_of_sub_eq (M := L + (32#64 + d).toNat) (x := idx)
    (by grind only [= BitVec.ofNat_add, = BitVec.ofNat_toNat, = BitVec.setWidth_eq])
    (by grind)

private theorem blocks_inside_a_inner_0 (rsi rcx : BitVec 64) (L : Nat)
    (h_rcx_ge : 2 ^ 64 - L ≤ rcx.toNat) (h_rcx_mod : rcx.toNat % 16 = 0)
    (h_L_bound : 2 * L + 64 < 2 ^ 63) :
    Mem.Blocks.Inside (rsi + rcx) 8
      [(rsi - BitVec.ofNat 64 (L + 32), L + 32)] :=
  inside_of_sub_eq (M := L + 32) (x := rcx) (by grind) (by grind)

private theorem blocks_inside_tp_idx_disp (base rbp idx d : BitVec 64) (L : Nat)
    (h_rbp_ge : 2 ^ 64 - L ≤ rbp.toNat) (h_idx_ge : rbp.toNat ≤ idx.toNat)
    (h_L_bound : 2 * L + 64 < 2 ^ 63) (hd : (32#64 + d).toNat ≤ 40) :
    Mem.Blocks.Inside (base + rbp + (-32#64) + idx + d) 8
      [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] :=
  inside_of_sub_eq (M := 2 * L + (32#64 + d).toNat) (x := rbp + idx)
    (by grind only [= BitVec.ofNat_add, = BitVec.ofNat_toNat, = BitVec.setWidth_eq])
    (by grind only [= BitVec.toNat_add])

private theorem blocks_inside_tp_inner_0 (base rbp rcx : BitVec 64) (L : Nat)
    (h_rbp_ge : 2 ^ 64 - L ≤ rbp.toNat) (h_rcx_ge : rbp.toNat ≤ rcx.toNat)
    (h_L_bound : 2 * L + 64 < 2 ^ 63) :
    Mem.Blocks.Inside (base + rbp + (-32#64) + rcx) 8
      [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] :=
  inside_of_sub_eq (M := 2 * L + 32) (x := rbp + rcx)
    (by grind only [= BitVec.ofNat_add]) (by grind only [= BitVec.toNat_add])

private theorem blocks_inside_tp_inner_16_sub_8 (base rbp rcx : BitVec 64) (L : Nat)
    (h_rbp_ge : 2 ^ 64 - L ≤ rbp.toNat) (h_rcx_ge : rbp.toNat ≤ rcx.toNat)
    (h_L_bound : 2 * L + 64 < 2 ^ 63) :
    Mem.Blocks.Inside (base + rbp + (-32#64) + (rcx + 16#64) + (-8#64)) 8
      [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] :=
  inside_of_sub_eq (M := 2 * L + 40) (x := rbp + rcx)
    (by grind only [= BitVec.ofNat_add]) (by grind only [= BitVec.toNat_add])

private theorem blocks_inside_tp_tail_0 (base rbp : BitVec 64) (L : Nat)
    (h_rbp_ge : 2 ^ 64 - L ≤ rbp.toNat) (h_L_bound : 2 * L + 64 < 2 ^ 63) :
    Mem.Blocks.Inside (base + rbp + (-32#64)) 8
      [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] :=
  inside_of_sub_eq (M := 2 * L + 32) (x := rbp)
    (by grind only [= BitVec.ofNat_add]) (by grind)

private theorem blocks_inside_tp_tail_8 (base rbp : BitVec 64) (L : Nat)
    (h_rbp_ge : 2 ^ 64 - L ≤ rbp.toNat) (h_L_bound : 2 * L + 64 < 2 ^ 63) :
    Mem.Blocks.Inside (base + rbp + (-32#64) + 8#64) 8
      [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] :=
  inside_of_sub_eq (M := 2 * L + 40) (x := rbp)
    (by grind only [= BitVec.ofNat_add]) (by grind)

local grind_pattern blocks_inside_a_disp =>
  Mem.Blocks.Inside (rsi + idx + d) 8 [(rsi - BitVec.ofNat 64 (L + 32), L + 32)]
local grind_pattern blocks_inside_a_inner_0 =>
  Mem.Blocks.Inside (rsi + rcx) 8 [(rsi - BitVec.ofNat 64 (L + 32), L + 32)]
local grind_pattern blocks_inside_tp_idx_disp =>
  Mem.Blocks.Inside (base + rbp + (-32#64) + idx + d) 8
    [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)]
local grind_pattern blocks_inside_tp_inner_0 =>
  Mem.Blocks.Inside (base + rbp + (-32#64) + rcx) 8
    [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)]
local grind_pattern blocks_inside_tp_inner_16_sub_8 =>
  Mem.Blocks.Inside (base + rbp + (-32#64) + (rcx + 16#64) + (-8#64)) 8
    [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)]
local grind_pattern blocks_inside_tp_tail_0 =>
  Mem.Blocks.Inside (base + rbp + (-32#64)) 8
    [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)]
local grind_pattern blocks_inside_tp_tail_8 =>
  Mem.Blocks.Inside (base + rbp + (-32#64) + 8#64) 8
    [(base - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)]

/-! ### The safety proof -/

/-- The outer-loop safety invariant at `.Lsqr4x_outer`: `%rsi`, `%rsp`, and
`%r9` keep their initial values, `%rbp` is a negative 16-byte-aligned offset in
`[2 ^ 64 - L, 2 ^ 64)`, the `(2 * L + 64)`-byte accumulator `tp[]` ending at
`56(%rsp, %r9, 2)` is preserved, and every initially mapped address remains
mapped (`Mem.SubDom d.dmem s.dmem`). -/
private abbrev sqr4x_outer_safety_outer (d : MachineData) (L : Nat) (R : DataMem → Prop)
    (s : MachineData) : Prop :=
  let rbp := (s.regs.get64 .rbp).toNat
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  2 ^ 64 - L ≤ rbp ∧ rbp < 2 ^ 64 ∧ rbp % 16 = 0 ∧
  (s.dmem =⋆ Mem.Blocks
    [(d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
      BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R) ∧
  Mem.SubDom d.dmem s.dmem

/-- The inner-loop safety invariant at `.Lsqr4x_inner`: in addition to the
outer invariant's conditions, `%rdi` sits at the end of the current `tp[]`
window (`tp_end + %rbp - 32`) and `%rcx` is a negative 16-byte-aligned offset in
`[%rbp, 2 ^ 64)`. -/
private abbrev sqr4x_outer_safety_inner (d : MachineData) (L : Nat) (R : DataMem → Prop)
    (s : MachineData) : Prop :=
  let rbp := (s.regs.get64 .rbp).toNat
  let rcx := (s.regs.get64 .rcx).toNat
  let tp_end := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rdi = tp_end + s.regs.get64 .rbp + (-32#64) ∧
  2 ^ 64 - L ≤ rbp ∧ rbp < 2 ^ 64 ∧ rbp % 16 = 0 ∧
  rbp ≤ rcx ∧ rcx < 2 ^ 64 ∧ rcx % 16 = 0 ∧
  (s.dmem =⋆ Mem.Blocks [(tp_end - BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R) ∧
  Mem.SubDom d.dmem s.dmem

/-- Both outer-loop proofs use the same entry state and labels, with their
respective outer and inner loop invariants supplied as `I_outer` and `I_inner`. -/
private abbrev sqr4x_outer_table (d : MachineData) (I_outer I_inner : MachineData → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | ".Lsqr4x_outer", s => I_outer s
  | ".Lsqr4x_inner", s => I_inner s
  | _, _ => False

/-- Lexicographic variant for the nested loop: the outer remaining distance
`2 ^ 64 - %rbp` dominates, and the inner remaining distance `2 ^ 64 - %rcx`
decreases along `.Lsqr4x_inner`'s self-edge. -/
private abbrev sqr4x_outer_var : Label → MachineData → Nat
  | "start", _ => (2 ^ 64 + 1) ^ 2
  | ".Lsqr4x_outer", s =>
      (2 ^ 64 - (s.regs.get64 .rbp).toNat) * (2 ^ 64 + 1) + 2 ^ 64
  | ".Lsqr4x_inner", s =>
      (2 ^ 64 - (s.regs.get64 .rbp).toNat) * (2 ^ 64 + 1) +
        (2 ^ 64 - (s.regs.get64 .rcx).toNat)
  | _, _ => 0

variable [layout : _root_.Layout] [validLayout : Executable.ValidLayout (layout sqr4x_outer_prog)]

/-- The ambient code of the outer-loop example: `sqr4x_outer_prog`, laid out. -/
local instance sqr4x_outer.env : CodeEnv := ⟨layout sqr4x_outer_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem sqr4x_outer_safe (d : MachineData) (L : Nat)
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 L)
    (h_L_mod : L % 16 = 0) (h_L_pos : 0 < L) (h_L_bound : 2 * L + 64 < 2 ^ 63)
    (R R₀ : DataMem → Prop)
    (h_tp : d.dmem =⋆ Mem.Blocks
      [(d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R)
    (h_a : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi - BitVec.ofNat 64 (L + 32), L + 32)] ⋆ R₀) :
    ⦃ fun s => s = d ⦄
      sqr4x_outer_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks
        [(d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
          BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R ⦄ := by
  apply MachineWP.cfg
    (sqr4x_outer_table d (sqr4x_outer_safety_outer d L R) (sqr4x_outer_safety_inner d L R))
    sqr4x_outer_var
  cfg_cases [sqr4x_outer_prog, sqr4x_outer_preamble, sqr4x_inner_loop, sqr4x_inner_iteration,
    sqr4x_outer_tail]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

theorem sqr4x_outer_terminates_and_safe
    (s₀ : MachineData) (L : Nat)
    (h_rbp : s₀.regs.rbp.toBitVec = 0#64 - BitVec.ofNat 64 L)
    (h_L_mod : L % 16 = 0) (h_L_pos : 0 < L) (h_L_bound : 2 * L + 64 < 2 ^ 63)
    (R R₀ : DataMem → Prop)
    (h_tp : s₀.dmem =⋆ Mem.Blocks
      [(s₀.regs.rsp.toBitVec + s₀.regs.r9.toBitVec * 2#64 + 56#64 -
        BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R)
    (h_a : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rsi.toBitVec - BitVec.ofNat 64 (L + 32), L + 32)] ⋆ R₀) :
    Eventually (straightlineStep (layout sqr4x_outer_prog))
      (fun s' => s'.1.dmem =⋆ Mem.Blocks
        [(s₀.regs.rsp.toBitVec + s₀.regs.r9.toBitVec * 2#64 + 56#64 -
          BitVec.ofNat 64 (2 * L + 64), 2 * L + 64)] ⋆ R)
      (s₀, Kraken.Layout.start Directive) :=
  Program.run_of_triple
    (sqr4x_outer_safe s₀ L h_rbp h_L_mod h_L_pos h_L_bound R R₀ h_tp h_a) rfl

-- Keep the arithmetic and memory lemmas independent of the enclosing layout.
omit layout validLayout

/-! ### Functional correctness of the complete outer loop -/

open Std Std.ExtHashMap

/-- The accumulator limbs and memory after `i` completed outer iterations. -/
structure Sqr4xOuterState where
  limbs : List (BitVec 64)
  memory : DataMem

/-- The carry chain, accumulator limbs, and memory at `.Lsqr4x_inner` during
outer iteration `i`. -/
structure Sqr4xOuterInnerState where
  previous : BitVec 64
  carry0 : BitVec 64
  carry1 : BitVec 64
  limbs : List (BitVec 64)
  memory : DataMem

/-- Reference computation for the `.Lsqr4x_outer` preamble in outer iteration `i`. -/
def sqr4xOuterPreambleStep (x : List (BitVec 64)) (tp_end : BitVec 64) (n i : Nat)
    (st : Sqr4xOuterState) : Sqr4xOuterInnerState :=
  let a0 := x.getD (2 * i) 0
  let a1 := x.getD (2 * i + 1) 0
  let a2 := x.getD (2 * i + 2) 0
  let a3 := x.getD (2 * i + 3) 0
  let p1 := sqr4xMac a1 a0 (st.limbs.getD (4 * i + 1) 0) 0
  let p2 := sqr4xMac a2 a0 p1.2 (st.limbs.getD (4 * i + 2) 0)
  let p3 := sqr4xMac a2 a1 0 (st.limbs.getD (4 * i + 3) 0)
  let p4 := sqr4xMac a3 a0 p2.2 p3.1
  let rbp := innerOffset n i
  let rdi := tp_end + rbp + (-32#64)
  ⟨a3, p4.2, p3.2,
    ((st.limbs.set (4 * i + 1) p1.1).set (4 * i + 2) p2.1).set (4 * i + 3) p4.1,
    ((st.memory.storeInt (rdi + rbp + (-24#64)) 8 p1.1.toIntOpaque).storeInt
      (rdi + rbp + (-16#64)) 8 p2.1.toIntOpaque).storeInt
      (rdi + rbp + (-8#64)) 8 p4.1.toIntOpaque⟩

/-- Reference computation for one `.Lsqr4x_inner` body step at `(i, j)`. -/
def sqr4xOuterInnerStep (x : List (BitVec 64)) (tp_end : BitVec 64) (n i j : Nat)
    (s : Sqr4xOuterInnerState) : Sqr4xOuterInnerState :=
  let a0 := x.getD (2 * i) 0
  let a1 := x.getD (2 * i + 1) 0
  let x0 := x.getD (2 * j + 4) 0
  let x1 := x.getD (2 * j + 5) 0
  let t0 := s.limbs.getD (2 * i + 2 * j + 4) 0
  let t1 := s.limbs.getD (2 * i + 2 * j + 5) 0
  let r := sqr4xInnerResult a0 a1 s.previous s.carry0 s.carry1 x0 x1 t0 t1
  let rdi := tp_end + innerOffset n i + (-32#64)
  ⟨x1, r.carry0, r.carry1,
    (s.limbs.set (2 * i + 2 * j + 4) r.out0).set (2 * i + 2 * j + 5) r.out1,
    (s.memory.storeInt (rdi + innerOffset n j) 8 r.out0.toIntOpaque).storeInt
      (rdi + innerOffset n j + 8) 8 r.out1.toIntOpaque⟩

/-- Reference fold for `k` iterations of `.Lsqr4x_inner` starting at `j = i`. -/
def sqr4xOuterInnerFold (x : List (BitVec 64)) (tp_end : BitVec 64) (n i : Nat)
    (initial : Sqr4xOuterInnerState) : Nat → Sqr4xOuterInnerState
  | 0 => initial
  | k + 1 =>
    sqr4xOuterInnerStep x tp_end n i (i + k)
      (sqr4xOuterInnerFold x tp_end n i initial k)

/-- Reference computation for `sqr4x_outer_tail` at the end of outer iteration `i`. -/
def sqr4xOuterTailStep (x : List (BitVec 64)) (tp_end : BitVec 64) (n i : Nat)
    (s : Sqr4xOuterInnerState) : Sqr4xOuterState :=
  let a1 := x.getD (2 * i + 1) 0
  let tail := sqr4xMac s.previous a1 s.carry1 s.carry0
  let rdi := tp_end + innerOffset n i + (-32#64)
  ⟨(s.limbs.set (2 * i + 2 * n + 4) tail.1).set (2 * i + 2 * n + 5) tail.2,
    (s.memory.storeInt rdi 8 tail.1.toIntOpaque).storeInt (rdi + 8) 8 tail.2.toIntOpaque⟩

/-- Reference fold for `i` outer iterations of `.Lsqr4x_outer`. -/
def sqr4xOuterFold (x : List (BitVec 64)) (tp_end : BitVec 64) (n : Nat)
    (initial : Sqr4xOuterState) : Nat → Sqr4xOuterState
  | 0 => initial
  | i + 1 =>
    let st := sqr4xOuterFold x tp_end n initial i
    let inner := sqr4xOuterInnerFold x tp_end n i
      (sqr4xOuterPreambleStep x tp_end n i st) (n - i)
    sqr4xOuterTailStep x tp_end n i inner

/-- Expected outer state after `i` of the `n` outer iterations. -/
def sqr4xOuterPrefix (d : MachineData) (n : Nat) (x t : List (BitVec 64)) (i : Nat) :
    Sqr4xOuterState :=
  sqr4xOuterFold x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) n ⟨t, d.dmem⟩ i

/-- Expected inner state at pair index `j` (`i ≤ j ≤ n`) during outer iteration `i`. -/
def sqr4xOuterInnerPrefix (d : MachineData) (n : Nat) (x t : List (BitVec 64)) (i j : Nat) :
    Sqr4xOuterInnerState :=
  let tp_end := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64
  sqr4xOuterInnerFold x tp_end n i
    (sqr4xOuterPreambleStep x tp_end n i (sqr4xOuterPrefix d n x t i)) (j - i)

@[local grind =] private theorem outer_prefix_zero_mem (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) :
    (sqr4xOuterPrefix d n x t 0).memory = d.dmem := rfl

private theorem outer_inner_prefix_self_fields (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) (i : Nat) :
    let st := sqr4xOuterPrefix d n x t i
    let s := sqr4xOuterInnerPrefix d n x t i i
    let a0 := x.getD (2 * i) 0
    let a1 := x.getD (2 * i + 1) 0
    let a2 := x.getD (2 * i + 2) 0
    let a3 := x.getD (2 * i + 3) 0
    let p1 := sqr4xMac a1 a0 (st.limbs.getD (4 * i + 1) 0) 0
    let p2 := sqr4xMac a2 a0 p1.2 (st.limbs.getD (4 * i + 2) 0)
    let p3 := sqr4xMac a2 a1 0 (st.limbs.getD (4 * i + 3) 0)
    let p4 := sqr4xMac a3 a0 p2.2 p3.1
    let rbp := innerOffset n i
    let rdi := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 + rbp + (-32#64)
    s.previous = a3 ∧
    s.carry0 = p4.2 ∧
    s.carry1 = p3.2 ∧
    s.memory = ((st.memory.storeInt (rdi + rbp + (-24#64)) 8 p1.1.toIntOpaque).storeInt
      (rdi + rbp + (-16#64)) 8 p2.1.toIntOpaque).storeInt
      (rdi + rbp + (-8#64)) 8 p4.1.toIntOpaque := by
  simp [sqr4xOuterInnerPrefix, sqr4xOuterInnerFold, sqr4xOuterPreambleStep]

private theorem outer_inner_prefix_step (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) (i j : Nat) (hij : i ≤ j) :
    sqr4xOuterInnerPrefix d n x t i (j + 1) =
      sqr4xOuterInnerStep x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) n i j
        (sqr4xOuterInnerPrefix d n x t i j) := by
  simp only [sqr4xOuterInnerPrefix]
  rw [show j + 1 - i = (j - i) + 1 by omega, sqr4xOuterInnerFold,
    show i + (j - i) = j by omega]

private theorem outer_inner_prefix_step_fields (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) (i j : Nat) (hij : i ≤ j) :
    let s := sqr4xOuterInnerPrefix d n x t i j
    let s' := sqr4xOuterInnerPrefix d n x t i (j + 1)
    let r := sqr4xInnerResult (x.getD (2 * i) 0) (x.getD (2 * i + 1) 0)
      s.previous s.carry0 s.carry1
      (x.getD (2 * j + 4) 0) (x.getD (2 * j + 5) 0)
      (s.limbs.getD (2 * i + 2 * j + 4) 0) (s.limbs.getD (2 * i + 2 * j + 5) 0)
    let rdi := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 + innerOffset n i + (-32#64)
    s'.previous = x.getD (2 * j + 5) 0 ∧
    s'.carry0 = r.carry0 ∧
    s'.carry1 = r.carry1 ∧
    s'.memory = (s.memory.storeInt (rdi + innerOffset n j) 8 r.out0.toIntOpaque).storeInt
      (rdi + innerOffset n j + 8) 8 r.out1.toIntOpaque := by
  have h := outer_inner_prefix_step d n x t i j hij
  exact ⟨congrArg Sqr4xOuterInnerState.previous h, congrArg Sqr4xOuterInnerState.carry0 h,
    congrArg Sqr4xOuterInnerState.carry1 h, congrArg Sqr4xOuterInnerState.memory h⟩

private theorem outer_prefix_step (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) (i : Nat) :
    sqr4xOuterPrefix d n x t (i + 1) =
      sqr4xOuterTailStep x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) n i
        (sqr4xOuterInnerPrefix d n x t i n) := rfl

private theorem flatMap_set_limb (xs : List (BitVec 64)) (j : Nat) (v : BitVec 64)
    (hj : j < xs.length) :
    (xs.flatMap fun w => Int.toBytes 8 w.toInt).take (8 * j) ++
      Int.toBytes 8 v.toIntOpaque ++
      (xs.flatMap fun w => Int.toBytes 8 w.toInt).drop (8 * j + 8) =
    (xs.set j v).flatMap fun w => Int.toBytes 8 w.toInt := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons w xs ih =>
    cases j with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, List.take_zero, List.nil_append,
        Nat.zero_add, List.drop_left' (Int.toBytes_length 8 w.toInt), List.set_cons_zero,
        BitVec.toIntOpaque]
    | succ j =>
      simp only [List.flatMap_cons, List.set_cons_succ, List.take_append, Int.toBytes_length]
      rw [List.take_of_length_le (by rw [Int.toBytes_length]; omega),
        show 8 * (j + 1) - 8 = 8 * j by omega,
        show 8 * (j + 1) + 8 = 8 + (8 * j + 8) by omega,
        ← List.drop_drop, List.drop_left' (Int.toBytes_length 8 w.toInt),
        List.append_assoc, List.append_assoc, ← List.append_assoc (List.take (8 * j) _),
        ih j (by simp only [List.length_cons] at hj; omega)]

private theorem load_x_limb {x ts : List (BitVec 64)} {a b addr : BitVec 64} {R : DataMem → Prop}
    {m : DataMem} (j : Nat)
    (h : m =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
      (Eq ((ts.flatMap fun w => Int.toBytes 8 w.toInt).At b) ⋆ R))
    (hlen : 8 * x.length < 2 ^ 64) (hj : j < x.length)
    (haddr : addr = a + BitVec.ofNat 64 (8 * j)) :
    m.loadInt addr 8
      = some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toIntOpaque)) :=
  haddr ▸ load_limb h hlen j hj

private theorem load_tp_limb {x ts : List (BitVec 64)} {a b addr : BitVec 64} {R : DataMem → Prop}
    {m : DataMem} (j : Nat)
    (h : m =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
      (Eq ((ts.flatMap fun w => Int.toBytes 8 w.toInt).At b) ⋆ R))
    (hlen : 8 * ts.length < 2 ^ 64) (hj : j < ts.length)
    (haddr : addr = b + BitVec.ofNat 64 (8 * j)) :
    m.loadInt addr 8
      = some (Int.ofBytes (Int.toBytes 8 (ts.getD j 0).toIntOpaque)) :=
  haddr ▸ load_limb (by rwa [sep_comm_l] at h) hlen j hj

private theorem store_tp_limb {x ts : List (BitVec 64)} {a b addr : BitVec 64} {R : DataMem → Prop}
    {m : DataMem} (j : Nat) (v : BitVec 64)
    (h : m =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
      (Eq ((ts.flatMap fun w => Int.toBytes 8 w.toInt).At b) ⋆ R))
    (hlen : 8 * ts.length < 2 ^ 64) (hj : j < ts.length)
    (haddr : addr = b + BitVec.ofNat 64 (8 * j)) :
    m.storeInt addr 8 v.toIntOpaque =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
      (Eq (((ts.set j v).flatMap fun w => Int.toBytes 8 w.toInt).At b) ⋆ R) := by
  subst haddr
  rw [sep_comm_l] at h ⊢
  have hoff : (b + BitVec.ofNat 64 (8 * j) - b).toNat = 8 * j := by
    rw [BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have hst := Mem.storeInt_slice (addr := b + BitVec.ofNat 64 (8 * j)) (n := 8) h
    (by rw [hoff, length_flatMap_limbs]; omega)
    (by rw [length_flatMap_limbs]; omega) v.toIntOpaque
  rwa [hoff, flatMap_set_limb ts j v hj] at hst

private abbrev outerMemInv (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (R : DataMem → Prop) (ts : List (BitVec 64)) (m : DataMem) : Prop :=
  ts.length = 4 * n + 8 ∧
  m =⋆
    Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
    (Eq ((ts.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (32 * n + 64))) ⋆ R)

private theorem preamble_mem_inv (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 32 * n + 64 < 2 ^ 63) (i : Nat) (hi : i < n)
    (st : Sqr4xOuterState) (hinv : outerMemInv d n x R st.limbs st.memory) :
    let s := sqr4xOuterPreambleStep x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) n i st
    outerMemInv d n x R s.limbs s.memory := by
  obtain ⟨hlen, hmem⟩ := hinv
  dsimp only [sqr4xOuterPreambleStep]
  refine ⟨by simp only [List.length_set, hlen], ?_⟩
  refine store_tp_limb (4 * i + 3) _ ?_ (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
    (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  refine store_tp_limb (4 * i + 2) _ ?_ (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
    (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  exact store_tp_limb (4 * i + 1) _ hmem (by omega) (by omega)
    (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)

private theorem inner_fold_mem_inv (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 32 * n + 64 < 2 ^ 63) (i : Nat) (hi : i < n)
    (initial : Sqr4xOuterInnerState) (hinit : outerMemInv d n x R initial.limbs initial.memory)
    (k : Nat) (hk : i + k ≤ n) :
    let s := sqr4xOuterInnerFold x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) n i initial k
    outerMemInv d n x R s.limbs s.memory := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    obtain ⟨hlen, hmem⟩ := ih (by omega)
    dsimp only [sqr4xOuterInnerFold, sqr4xOuterInnerStep]
    refine ⟨by simp only [List.length_set, hlen], ?_⟩
    refine store_tp_limb (2 * i + 2 * (i + k) + 5) _ ?_ (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
    exact store_tp_limb (2 * i + 2 * (i + k) + 4) _ hmem (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)

private theorem outer_prefix_mem_inv (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 32 * n + 64 < 2 ^ 63) (htl : t.length = 4 * n + 8)
    (hmem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
          BitVec.ofNat 64 (32 * n + 64))) ⋆ R))
    (i : Nat) (hi : i ≤ n) :
    outerMemInv d n x R (sqr4xOuterPrefix d n x t i).limbs (sqr4xOuterPrefix d n x t i).memory := by
  induction i with
  | zero => exact ⟨htl, hmem⟩
  | succ i ih =>
    have hpre := preamble_mem_inv d n x R hbound i (by omega) _ (ih (by omega))
    have hinner_inv : outerMemInv d n x R
        (sqr4xOuterInnerPrefix d n x t i n).limbs (sqr4xOuterInnerPrefix d n x t i n).memory :=
      inner_fold_mem_inv d n x R hbound i (by omega) _ hpre (n - i) (by omega)
    obtain ⟨hlen, hinner⟩ := hinner_inv
    rw [outer_prefix_step]
    dsimp only [sqr4xOuterTailStep]
    refine ⟨by simp only [List.length_set, hlen], ?_⟩
    refine store_tp_limb (2 * i + 2 * n + 5) _ ?_ (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
    exact store_tp_limb (2 * i + 2 * n + 4) _ hinner (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)

private theorem outer_preamble_loads (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 32 * n + 64 < 2 ^ 63)
    (hxl : x.length = 2 * n + 4) (htl : t.length = 4 * n + 8)
    (hmem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
          BitVec.ofNat 64 (32 * n + 64))) ⋆ R))
    (s : MachineData) (hi : innerIndex n (s.regs.get64 .rbp) < n) :
    let i := innerIndex n (s.regs.get64 .rbp)
    let st := sqr4xOuterPrefix d n x t i
    let rbp := innerOffset n i
    let tp_end := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64
    let rdi := tp_end + rbp + (-32#64)
    let a0 := x.getD (2 * i) 0
    let a1 := x.getD (2 * i + 1) 0
    let a2 := x.getD (2 * i + 2) 0
    let p1 := sqr4xMac a1 a0 (st.limbs.getD (4 * i + 1) 0) 0
    let p2 := sqr4xMac a2 a0 p1.2 (st.limbs.getD (4 * i + 2) 0)
    st.memory.loadInt (d.regs.get64 .rsi + rbp + (-32#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * i) 0).toIntOpaque)) ∧
    st.memory.loadInt (d.regs.get64 .rsi + rbp + (-24#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * i + 1) 0).toIntOpaque)) ∧
    st.memory.loadInt (d.regs.get64 .rsi + rbp + (-16#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * i + 2) 0).toIntOpaque)) ∧
    ((st.memory.storeInt (rdi + rbp + (-24#64)) 8 p1.1.toIntOpaque).storeInt
      (rdi + rbp + (-16#64)) 8 p2.1.toIntOpaque).loadInt
        (d.regs.get64 .rsi + rbp + (-8#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * i + 3) 0).toIntOpaque)) ∧
    st.memory.loadInt (rdi + rbp + (-24#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (st.limbs.getD (4 * i + 1) 0).toIntOpaque)) ∧
    st.memory.loadInt (rdi + rbp + (-16#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (st.limbs.getD (4 * i + 2) 0).toIntOpaque)) ∧
    st.memory.loadInt (rdi + rbp + (-8#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (st.limbs.getD (4 * i + 3) 0).toIntOpaque)) := by
  dsimp only
  obtain ⟨hlen, hm⟩ := outer_prefix_mem_inv d n x t R hbound htl hmem
    (innerIndex n (s.regs.get64 .rbp)) (by omega)
  have hm1 := store_tp_limb
    (addr := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 +
      innerOffset n (innerIndex n (s.regs.get64 .rbp)) + (-32#64) +
      innerOffset n (innerIndex n (s.regs.get64 .rbp)) + (-24#64))
    (4 * innerIndex n (s.regs.get64 .rbp) + 1)
    (sqr4xMac (x.getD (2 * innerIndex n (s.regs.get64 .rbp) + 1) 0)
      (x.getD (2 * innerIndex n (s.regs.get64 .rbp)) 0)
      ((sqr4xOuterPrefix d n x t (innerIndex n (s.regs.get64 .rbp))).limbs.getD
        (4 * innerIndex n (s.regs.get64 .rbp) + 1) 0) 0).1
    hm (by omega) (by omega)
    (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  have hm2 := store_tp_limb
    (addr := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 +
      innerOffset n (innerIndex n (s.regs.get64 .rbp)) + (-32#64) +
      innerOffset n (innerIndex n (s.regs.get64 .rbp)) + (-16#64))
    (4 * innerIndex n (s.regs.get64 .rbp) + 2)
    (sqr4xMac (x.getD (2 * innerIndex n (s.regs.get64 .rbp) + 2) 0)
      (x.getD (2 * innerIndex n (s.regs.get64 .rbp)) 0)
      (sqr4xMac (x.getD (2 * innerIndex n (s.regs.get64 .rbp) + 1) 0)
        (x.getD (2 * innerIndex n (s.regs.get64 .rbp)) 0)
        ((sqr4xOuterPrefix d n x t (innerIndex n (s.regs.get64 .rbp))).limbs.getD
          (4 * innerIndex n (s.regs.get64 .rbp) + 1) 0) 0).2
      ((sqr4xOuterPrefix d n x t (innerIndex n (s.regs.get64 .rbp))).limbs.getD
        (4 * innerIndex n (s.regs.get64 .rbp) + 2) 0)).1
    hm1 (by simp only [List.length_set]; omega) (by simp only [List.length_set]; omega)
    (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact load_x_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_x_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_x_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_x_limb _ hm2 (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_tp_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_tp_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_tp_limb _ hm (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)

local grind_pattern outer_preamble_loads =>
  sqr4xOuterPrefix d n x t (innerIndex n (s.regs.get64 .rbp)),
  Std.ExtHashMap.sep (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))))
    (Std.ExtHashMap.sep (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (32 * n + 64)))) R) d.dmem

private theorem outer_inner_loads (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hbound : 32 * n + 64 < 2 ^ 63)
    (hxl : x.length = 2 * n + 4) (htl : t.length = 4 * n + 8)
    (hmem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
          BitVec.ofNat 64 (32 * n + 64))) ⋆ R))
    (s : MachineData)
    (hij : innerIndex n (s.regs.get64 .rbp) ≤ innerIndex n (s.regs.get64 .rcx))
    (hj : innerIndex n (s.regs.get64 .rcx) < n) :
    let i := innerIndex n (s.regs.get64 .rbp)
    let j := innerIndex n (s.regs.get64 .rcx)
    let st := sqr4xOuterInnerPrefix d n x t i j
    let rdi := (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) + innerOffset n i + (-32#64)
    st.memory.loadInt (d.regs.get64 .rsi + innerOffset n j) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + 4) 0).toIntOpaque)) ∧
    st.memory.loadInt (d.regs.get64 .rsi + innerOffset n j + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + 5) 0).toIntOpaque)) ∧
    st.memory.loadInt (rdi + innerOffset n j) 8 =
      some (Int.ofBytes (Int.toBytes 8 (st.limbs.getD (2 * i + 2 * j + 4) 0).toIntOpaque)) ∧
    st.memory.loadInt (rdi + innerOffset n j + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (st.limbs.getD (2 * i + 2 * j + 5) 0).toIntOpaque)) ∧
    (st.memory.loadInt rdi 8).isSome = true ∧
    (st.memory.loadInt (rdi + 8) 8).isSome = true := by
  dsimp only
  have hpre := preamble_mem_inv d n x R hbound (innerIndex n (s.regs.get64 .rbp)) (by omega) _
    (outer_prefix_mem_inv d n x t R hbound htl hmem (innerIndex n (s.regs.get64 .rbp)) (by omega))
  have hinv_j : outerMemInv d n x R
      (sqr4xOuterInnerPrefix d n x t (innerIndex n (s.regs.get64 .rbp)) (innerIndex n (s.regs.get64 .rcx))).limbs
      (sqr4xOuterInnerPrefix d n x t (innerIndex n (s.regs.get64 .rbp)) (innerIndex n (s.regs.get64 .rcx))).memory :=
    inner_fold_mem_inv d n x R hbound (innerIndex n (s.regs.get64 .rbp)) (by omega) _ hpre
      (innerIndex n (s.regs.get64 .rcx) - innerIndex n (s.regs.get64 .rbp)) (by omega)
  obtain ⟨hlen_j, hm_j⟩ := hinv_j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact load_x_limb _ hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_x_limb _ hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_tp_limb _ hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · exact load_tp_limb _ hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)
  · rw [load_tp_limb (2 * innerIndex n (s.regs.get64 .rbp) + 2 * n + 4) hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)]; rfl
  · rw [load_tp_limb (2 * innerIndex n (s.regs.get64 .rbp) + 2 * n + 5) hm_j (by omega) (by omega)
      (by simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]; grind)]; rfl

local grind_pattern outer_inner_loads =>
  sqr4xOuterInnerPrefix d n x t (innerIndex n (s.regs.get64 .rbp)) (innerIndex n (s.regs.get64 .rcx)),
  Std.ExtHashMap.sep (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))))
    (Std.ExtHashMap.sep (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (32 * n + 64)))) R) d.dmem

private theorem storeInt_loadInt_isSome (m : DataMem) (a b : BitVec 64) (v : Int)
    (h : (m.loadInt b 8).isSome = true) :
    ((m.storeInt a 8 v).loadInt b 8).isSome = true :=
  Mem.SubDom.loadInt_isSome (Mem.SubDom.storeInt (Mem.SubDom.refl m) a 8 v) h

local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

private abbrev outerInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  let i := innerIndex n (s.regs.get64 .rbp)
  i < n ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rbp = innerOffset n i ∧
  s.zmms = d.zmms ∧
  s.dmem = (sqr4xOuterPrefix d n x t i).memory

private abbrev outerInnerInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  let i := innerIndex n (s.regs.get64 .rbp)
  let j := innerIndex n (s.regs.get64 .rcx)
  let st := sqr4xOuterInnerPrefix d n x t i j
  i < n ∧ i ≤ j ∧ j < n ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rbp = innerOffset n i ∧
  s.regs.get64 .rcx = innerOffset n j ∧
  s.regs.get64 .rdi =
    (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64) + innerOffset n i + (-32#64) ∧
  s.regs.get64 .r14 = x.getD (2 * i) 0 ∧
  s.regs.get64 .r15 = x.getD (2 * i + 1) 0 ∧
  s.regs.get64 .rax = st.previous ∧
  s.regs.get64 .r11 = st.carry0 ∧
  s.regs.get64 .r13 = st.carry1 ∧
  s.zmms = d.zmms ∧
  s.dmem = st.memory

@[local grind norm] private theorem Sqr4xInnerResult.out0_mk (o0 o1 c0 c1) :
    (Sqr4xInnerResult.mk o0 o1 c0 c1).out0 = o0 := rfl
@[local grind norm] private theorem Sqr4xInnerResult.out1_mk (o0 o1 c0 c1) :
    (Sqr4xInnerResult.mk o0 o1 c0 c1).out1 = o1 := rfl
@[local grind norm] private theorem Sqr4xInnerResult.carry0_mk (o0 o1 c0 c1) :
    (Sqr4xInnerResult.mk o0 o1 c0 c1).carry0 = c0 := rfl
@[local grind norm] private theorem Sqr4xInnerResult.carry1_mk (o0 o1 c0 c1) :
    (Sqr4xInnerResult.mk o0 o1 c0 c1).carry1 = c1 := rfl

private theorem bound_16_of_32 (n : Nat) (h : 32 * n + 64 < 2 ^ 63) : 16 * n < 2 ^ 63 := by
  omega

local grind_pattern bound_16_of_32 => 32 * n + 64
local grind_pattern offset_facts => innerOffset n k

private theorem offset_done (n k : Nat) (hk : k < n) (hn : 16 * n < 2 ^ 63)
    (hz : innerOffset n k + 16 = 0#64) :
    k + 1 = n := by
  have h := (offset_facts n (k + 1) (by omega) hn).1
  rw [← offset_step] at h
  exact h.mp hz

private theorem outer_offset_continue (n k : Nat) (hk : k < n) (hn : 16 * n < 2 ^ 63)
    (hne : innerOffset n k + 16 ≠ 0#64) :
    k + 1 < n ∧ innerIndex n (innerOffset n k + 16) = k + 1 ∧
      (2 ^ 64 - (innerOffset n k + 16).toNat) * (2 ^ 64 + 1) + 2 ^ 64 <
        (2 ^ 64 - (innerOffset n k).toNat) * (2 ^ 64 + 1) := by
  have hc := offset_continue n k hk hn (by intro h; exact hne (BitVec.eq_of_toNat_eq h))
  refine ⟨hc.1, hc.2.1, ?_⟩
  have h1 := (offset_facts n k (by omega) hn).2 hk
  have h2 := (offset_facts n (k + 1) (by omega) hn).2 hc.1
  rw [offset_step, h2.1, h1.1]
  omega

@[local grind =] private theorem ofInt_limb_opaque (v : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v.toIntOpaque)) = v :=
  ofInt_limb v

@[local grind norm] private theorem bv_zero_add (x : BitVec 64) : 0 + x = x := BitVec.zero_add x
@[local grind norm] private theorem bv_sub_zero (x : BitVec 64) : x - 0 = x := BitVec.sub_zero x

@[local grind =] private theorem add_16_innerOffset (n k : Nat) :
    16 + innerOffset n k = innerOffset n k + 16 :=
  BitVec.add_comm _ _

@[local grind =] private theorem load_after_store_24_16 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt (a + (-24#64)) 8 v).loadInt (a + (-16#64)) 8 = m.loadInt (a + (-16#64)) 8 := by
  apply load_after_disjoint_store; grind

@[local grind =] private theorem load_after_store_24_8 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt (a + (-24#64)) 8 v).loadInt (a + (-8#64)) 8 = m.loadInt (a + (-8#64)) 8 := by
  apply load_after_disjoint_store; grind

@[local grind =] private theorem load_after_store_16_8 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt (a + (-16#64)) 8 v).loadInt (a + (-8#64)) 8 = m.loadInt (a + (-8#64)) 8 := by
  apply load_after_disjoint_store; grind

@[local grind =] private theorem offset_zero (n : Nat) :
    innerOffset n 0 = 0#64 - BitVec.ofNat 64 (16 * n) := rfl

private theorem outer_prefix_step_mem (d : MachineData) (n : Nat)
    (x t : List (BitVec 64)) (i j k : Nat) (hik : i + 1 = k) (hj : j + 1 = n) :
    let s := sqr4xOuterInnerPrefix d n x t i (j + 1)
    let tail := sqr4xMac s.previous (x.getD (2 * i + 1) 0) s.carry1 s.carry0
    let rdi := d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 + innerOffset n i + (-32#64)
    (sqr4xOuterPrefix d n x t k).memory =
      (s.memory.storeInt rdi 8 tail.1.toIntOpaque).storeInt (rdi + 8) 8 tail.2.toIntOpaque := by
  subst hik hj; rfl


private theorem outer_inner_fold_length (x : List (BitVec 64)) (base : BitVec 64)
    (n i : Nat) (initial : Sqr4xOuterInnerState) (k : Nat) :
    (sqr4xOuterInnerFold x base n i initial k).limbs.length = initial.limbs.length := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [sqr4xOuterInnerFold, sqr4xOuterInnerStep, List.length_set] using ih

private theorem outer_fold_length (x : List (BitVec 64)) (base : BitVec 64)
    (n : Nat) (initial : Sqr4xOuterState) (i : Nat) :
    (sqr4xOuterFold x base n initial i).limbs.length = initial.limbs.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simpa only [sqr4xOuterFold, sqr4xOuterTailStep, List.length_set,
      outer_inner_fold_length, sqr4xOuterPreambleStep] using ih

private theorem outer_final_words (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (i j : Nat) (hi : i + 1 = n) (hj : j + 1 = n) (ht : t.length = 4 * n + 8) :
    let st := sqr4xOuterInnerPrefix d n x t i j
    let r := sqr4xInnerResult (x.getD (2 * i) 0) (x.getD (2 * i + 1) 0)
      st.previous st.carry0 st.carry1 (x.getD (2 * j + 4) 0) (x.getD (2 * j + 5) 0)
      (st.limbs.getD (2 * i + 2 * j + 4) 0) (st.limbs.getD (2 * i + 2 * j + 5) 0)
    let tail := sqr4xMac (x.getD (2 * j + 5) 0) (x.getD (2 * i + 1) 0) r.carry1 r.carry0
    let done := sqr4xOuterPrefix d n x t n
    done.limbs.getD (4 * n + 1) 0 = r.out1 ∧
      done.limbs.getD (4 * n + 2) 0 = tail.1 ∧
      done.limbs.getD (4 * n + 3) 0 = tail.2 := by
  have hij : i = j := by omega
  subst j
  have hlen : (sqr4xOuterInnerPrefix d n x t i i).limbs.length = 4 * n + 8 := by
    simp only [sqr4xOuterInnerPrefix, outer_inner_fold_length, sqr4xOuterPreambleStep,
      List.length_set, sqr4xOuterPrefix, outer_fold_length]
    exact ht
  rw [← hi] at hlen
  dsimp only
  rw [← hi, outer_prefix_step, outer_inner_prefix_step d (i + 1) x t i i (by omega)]
  simp only [sqr4xOuterTailStep, sqr4xOuterInnerStep]
  simp (discharger := omega) only [List.getD_eq_getElem?_getD, List.getElem?_set,
    List.length_set, ite_eq_left, ite_eq_right, Option.getD_some, and_self]

attribute [local irreducible] sqr4xMac innerIndex innerOffset sqr4xOuterPrefix sqr4xOuterInnerPrefix
attribute [local sym_simp] Option.map_none BitVec.zero_add BitVec.sub_zero CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind unfold] sqr4xInnerResult
attribute [local grind norm]
  sqr4xMac_eq Kraken.Fold.fst_mk Kraken.Fold.snd_mk
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.xor_self BitVec.zero_add BitVec.sub_zero
  CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind =] ofInt_limb offset_initial_index offset_step

local grind_pattern offset_continue => innerOffset n k + 16
local grind_pattern offset_done => innerOffset n k + 16
local grind_pattern outer_offset_continue => innerOffset n k + 16
local grind_pattern outer_inner_prefix_self_fields =>
  sqr4xOuterInnerPrefix d n x t i i, sqr4xOuterPrefix d n x t i
local grind_pattern outer_inner_prefix_step_fields =>
  sqr4xOuterInnerPrefix d n x t i j, innerOffset n j + 16
local grind_pattern outer_prefix_step_mem =>
  (sqr4xOuterPrefix d n x t k).memory, sqr4xOuterInnerPrefix d n x t i j

local grind_pattern outer_final_words =>
  sqr4xOuterInnerPrefix d n x t i j, sqr4xOuterPrefix d n x t n

include layout validLayout

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Functional correctness of the complete `.Lsqr4x_outer` nested loop for `n`
outer iterations (`2 * n + 4` input limbs in `x` and `4 * n + 8` accumulator
limbs in `t`). -/
theorem sqr4x_outer_prog_correct (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 (16 * n))
    (h_pos : 0 < n) (h_bound : 32 * n + 64 < 2 ^ 63)
    (h_x_len : x.length = 2 * n + 4) (h_t_len : t.length = 4 * n + 8) (R : DataMem → Prop)
    (h_mem : d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
      (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
        (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
          BitVec.ofNat 64 (32 * n + 64))) ⋆ R)) :
    ⦃ fun s => s = d ⦄ sqr4x_outer_prog ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rbp = 0#64 ∧
      s.regs.get64 .rcx = 0#64 ∧
      s.zmms = d.zmms ∧
      s.regs.get64 .r10 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 1) 0 ∧
      s.regs.get64 .r13 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 2) 0 ∧
      s.regs.get64 .r12 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 3) 0 ∧
      s.dmem = (sqr4xOuterPrefix d n x t n).memory ⦄ := by
  apply MachineWP.cfg
    (sqr4x_outer_table d (outerInvariant d n x t) (outerInnerInvariant d n x t))
    sqr4x_outer_var
  cfg_cases [sqr4x_outer_prog, sqr4x_outer_preamble, sqr4x_inner_loop, sqr4x_inner_iteration,
    sqr4x_outer_tail]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

end Sqr4xOuter

section Sqr8xInternal

/-! ### Remaining instructions of `__bn_sqr8x_internal`

Source: BoringSSL `gen/bcm/x86_64-mont5-linux.S`, revision
`572a4c68475d284b34675f45ddbb9c158ef3c2ae`, with CET disabled. Alignment directives
and standalone operand/address-size padding prefixes are omitted as in the inner/outer models.
The final conditional subtraction is in the separate `__bn_post4x_internal`.
-/

def sqr4x_first_preamble : Program := parse("
    leaq 32(%r10),%rbp
    leaq (%rsi,%r9,1),%rsi
    movq %r9,%rcx
    movq -32(%rsi,%rbp,1),%r14
    leaq 56(%rsp,%r9,2),%rdi
    movq -24(%rsi,%rbp,1),%rax
    leaq -32(%rdi,%rbp,1),%rdi
    movq -16(%rsi,%rbp,1),%rbx
    movq %rax,%r15
    mulq %r14
    movq %rax,%r10
    movq %rbx,%rax
    movq %rdx,%r11
    movq %r10,-24(%rdi,%rbp,1)
    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    adcq $0,%rdx
    movq %r11,-16(%rdi,%rbp,1)
    movq %rdx,%r10
    movq -8(%rsi,%rbp,1),%rbx
    mulq %r15
    movq %rax,%r12
    movq %rbx,%rax
    movq %rdx,%r13
    leaq (%rbp),%rcx
    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    movq %rdx,%r11
    adcq $0,%r11
    addq %r12,%r10
    adcq $0,%r11
    movq %r10,-8(%rdi,%rcx,1)
    jmp .Lsqr4x_1st
")

def sqr4x_first_iteration : Program := parse("
    movq (%rsi,%rcx,1),%rbx
    mulq %r15
    addq %rax,%r13
    movq %rbx,%rax
    movq %rdx,%r12
    adcq $0,%r12
    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    movq 8(%rsi,%rcx,1),%rbx
    movq %rdx,%r10
    adcq $0,%r10
    addq %r13,%r11
    adcq $0,%r10
    mulq %r15
    addq %rax,%r12
    movq %rbx,%rax
    movq %r11,(%rdi,%rcx,1)
    movq %rdx,%r13
    adcq $0,%r13
    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    movq 16(%rsi,%rcx,1),%rbx
    movq %rdx,%r11
    adcq $0,%r11
    addq %r12,%r10
    adcq $0,%r11
    mulq %r15
    addq %rax,%r13
    movq %rbx,%rax
    movq %r10,8(%rdi,%rcx,1)
    movq %rdx,%r12
    adcq $0,%r12
    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    movq 24(%rsi,%rcx,1),%rbx
    movq %rdx,%r10
    adcq $0,%r10
    addq %r13,%r11
    adcq $0,%r10
    mulq %r15
    addq %rax,%r12
    movq %rbx,%rax
    movq %r11,16(%rdi,%rcx,1)
    movq %rdx,%r13
    adcq $0,%r13
    leaq 32(%rcx),%rcx
    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    movq %rdx,%r11
    adcq $0,%r11
    addq %r12,%r10
    adcq $0,%r11
    movq %r10,-8(%rdi,%rcx,1)
")

def sqr4x_first_tail : Program := parse("
    mulq %r15
    addq %rax,%r13
    leaq 16(%rbp),%rbp
    adcq $0,%rdx
    addq %r11,%r13
    adcq $0,%rdx
    movq %r13,(%rdi)
    movq %rdx,%r12
    movq %rdx,8(%rdi)
    jmp .Lsqr4x_outer
")

/-- Complete the six cross-products of the final four input limbs. -/
def sqr4x_final_products : Program := parse("
    movq -32(%rsi),%r14
    leaq 56(%rsp,%r9,2),%rdi
    movq -24(%rsi),%rax
    leaq -32(%rdi,%rbp,1),%rdi
    movq -16(%rsi),%rbx
    movq %rax,%r15
    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    movq %rdx,%r11
    adcq $0,%r11
    mulq %r14
    addq %rax,%r11
    movq %rbx,%rax
    movq %r10,-24(%rdi)
    movq %rdx,%r10
    adcq $0,%r10
    addq %r13,%r11
    movq -8(%rsi),%rbx
    adcq $0,%r10
    mulq %r15
    addq %rax,%r12
    movq %rbx,%rax
    movq %r11,-16(%rdi)
    movq %rdx,%r13
    adcq $0,%r13
    mulq %r14
    addq %rax,%r10
    movq %rbx,%rax
    movq %rdx,%r11
    adcq $0,%r11
    addq %r12,%r10
    adcq $0,%r11
    movq %r10,-8(%rdi)
    mulq %r15
    addq %rax,%r13
    movq -16(%rsi),%rax
    adcq $0,%rdx
    addq %r11,%r13
    adcq $0,%rdx
    movq %r13,(%rdi)
    movq %rdx,%r12
    movq %rdx,8(%rdi)
    mulq %rbx
    addq $16,%rbp
    xorq %r14,%r14
    subq %r9,%rbp
    xorq %r15,%r15
    addq %r12,%rax
    adcq $0,%rdx
    movq %rax,8(%rdi)
    movq %rdx,16(%rdi)
    movq %r15,24(%rdi)
")

/-- The first two diagonal squares, before the repeated four-square loop. -/
def sqr4x_shift_preamble : Program := parse("
    movq -16(%rsi,%rbp,1),%rax
    leaq 56(%rsp),%rdi
    xorq %r10,%r10
    movq 8(%rdi),%r11
    leaq (%r14,%r10,2),%r12
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r13
    shrq $63,%r11
    orq %r10,%r13
    movq 16(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq 24(%rdi),%r11
    adcq %rax,%r12
    movq -8(%rsi,%rbp,1),%rax
    movq %r12,(%rdi)
    adcq %rdx,%r13
    leaq (%r14,%r10,2),%rbx
    movq %r13,8(%rdi)
    sbbq %r15,%r15
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r8
    shrq $63,%r11
    orq %r10,%r8
    movq 32(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq 40(%rdi),%r11
    adcq %rax,%rbx
    movq 0(%rsi,%rbp,1),%rax
    movq %rbx,16(%rdi)
    adcq %rdx,%r8
    leaq 16(%rbp),%rbp
    movq %r8,24(%rdi)
    sbbq %r15,%r15
    leaq 64(%rdi),%rdi
    jmp .Lsqr4x_shift_n_add
")

/-- Finish the cross-products and initialize the diagonal-square loop. -/
def sqr4x_final_cross_products : Program :=
  sqr4x_final_products ++ sqr4x_shift_preamble

private def sqr4x_shift_lane0 : Program := parse("
    leaq (%r14,%r10,2),%r12
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r13
    shrq $63,%r11
    orq %r10,%r13
    movq -16(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq -8(%rdi),%r11
    adcq %rax,%r12
    movq -8(%rsi,%rbp,1),%rax
    movq %r12,-32(%rdi)
    adcq %rdx,%r13
    leaq (%r14,%r10,2),%rbx
    movq %r13,-24(%rdi)
    sbbq %r15,%r15
")

private def sqr4x_shift_lane1 : Program := parse("
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r8
    shrq $63,%r11
    orq %r10,%r8
    movq 0(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq 8(%rdi),%r11
    adcq %rax,%rbx
    movq 0(%rsi,%rbp,1),%rax
    movq %rbx,-16(%rdi)
    adcq %rdx,%r8
    leaq (%r14,%r10,2),%r12
    movq %r8,-8(%rdi)
    sbbq %r15,%r15
")

private def sqr4x_shift_lane2 : Program := parse("
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r13
    shrq $63,%r11
    orq %r10,%r13
    movq 16(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq 24(%rdi),%r11
    adcq %rax,%r12
    movq 8(%rsi,%rbp,1),%rax
    movq %r12,0(%rdi)
    adcq %rdx,%r13
    leaq (%r14,%r10,2),%rbx
    movq %r13,8(%rdi)
    sbbq %r15,%r15
")

private def sqr4x_shift_lane3 : Program := parse("
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r8
    shrq $63,%r11
    orq %r10,%r8
    movq 32(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq 40(%rdi),%r11
    adcq %rax,%rbx
    movq 16(%rsi,%rbp,1),%rax
    movq %rbx,16(%rdi)
    adcq %rdx,%r8
    movq %r8,24(%rdi)
    sbbq %r15,%r15
")

def sqr4x_shift_iteration : Program :=
  sqr4x_shift_lane0 ++ sqr4x_shift_lane1 ++ sqr4x_shift_lane2 ++ sqr4x_shift_lane3 ++ parse("leaq 64(%rdi),%rdi")

def sqr4x_shift_tail : Program := parse("
    leaq (%r14,%r10,2),%r12
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r13
    shrq $63,%r11
    orq %r10,%r13
    movq -16(%rdi),%r10
    movq %r11,%r14
    mulq %rax
    negq %r15
    movq -8(%rdi),%r11
    adcq %rax,%r12
    movq -8(%rsi),%rax
    movq %r12,-32(%rdi)
    adcq %rdx,%r13
    leaq (%r14,%r10,2),%rbx
    movq %r13,-24(%rdi)
    sbbq %r15,%r15
    shrq $63,%r10
    leaq (%rcx,%r11,2),%r8
    shrq $63,%r11
    orq %r10,%r8
    mulq %rax
    negq %r15
    adcq %rax,%rbx
    adcq %rdx,%r8
    movq %rbx,-16(%rdi)
    movq %r8,-8(%rdi)
    movq %xmm2,%rbp
")

def sqr8x_reduction_setup : Program := parse("
    xorq %rax,%rax
    leaq (%r9,%rbp,1),%rcx
    leaq 56(%rsp,%r9,2),%rdx
    movq %rcx,8(%rsp)
    leaq 56(%rsp,%r9,1),%rdi
    movq %rdx,16(%rsp)
    negq %r9
    jmp .L8x_reduction_loop
")

def sqr8x_reduction_entry : Program := parse("
    leaq (%rdi,%r9,1),%rdi
    movq 0(%rdi),%rbx
    movq 8(%rdi),%r9
    movq 16(%rdi),%r10
    movq 24(%rdi),%r11
    movq 32(%rdi),%r12
    movq 40(%rdi),%r13
    movq 48(%rdi),%r14
    movq 56(%rdi),%r15
    movq %rax,(%rdx)
    leaq 64(%rdi),%rdi
    movq %rbx,%r8
    imulq 40(%rsp),%rbx
    movq 0(%rbp),%rax
    movl $8,%ecx
    jmp .L8x_reduce
")


/-- Set up reduction and enter its first eight-word cancellation block. -/
def sqr8x_reduction_preamble : Program :=
  sqr8x_reduction_setup ++ parse(".L8x_reduction_loop:") ++ sqr8x_reduction_entry

/-- Cancel the least significant word before propagating into the next seven. -/
def sqr8x_reduce_cancel : Program := parse("
    mulq %rbx
    movq 8(%rbp),%rax
    negq %r8
    movq %rdx,%r8
    adcq $0,%r8
")

def sqr8x_reduce_iteration : Program := sqr8x_reduce_cancel ++ parse("
    mulq %rbx
    addq %rax,%r9
    movq 16(%rbp),%rax
    adcq $0,%rdx
    addq %r9,%r8
    movq %rbx,48(%rsp,%rcx,8)
    movq %rdx,%r9
    adcq $0,%r9
    mulq %rbx
    addq %rax,%r10
    movq 24(%rbp),%rax
    adcq $0,%rdx
    addq %r10,%r9
    movq 40(%rsp),%rsi
    movq %rdx,%r10
    adcq $0,%r10
    mulq %rbx
    addq %rax,%r11
    movq 32(%rbp),%rax
    adcq $0,%rdx
    imulq %r8,%rsi
    addq %r11,%r10
    movq %rdx,%r11
    adcq $0,%r11
    mulq %rbx
    addq %rax,%r12
    movq 40(%rbp),%rax
    adcq $0,%rdx
    addq %r12,%r11
    movq %rdx,%r12
    adcq $0,%r12
    mulq %rbx
    addq %rax,%r13
    movq 48(%rbp),%rax
    adcq $0,%rdx
    addq %r13,%r12
    movq %rdx,%r13
    adcq $0,%r13
    mulq %rbx
    addq %rax,%r14
    movq 56(%rbp),%rax
    adcq $0,%rdx
    addq %r14,%r13
    movq %rdx,%r14
    adcq $0,%r14
    mulq %rbx
    movq %rsi,%rbx
    addq %rax,%r15
    movq 0(%rbp),%rax
    adcq $0,%rdx
    addq %r15,%r14
    movq %rdx,%r15
    adcq $0,%r15
")

private def sqr8x_add_high : Program := parse("
    adcq 8(%rdi),%r9
    adcq 16(%rdi),%r10
    adcq 24(%rdi),%r11
    adcq 32(%rdi),%r12
    adcq 40(%rdi),%r13
    adcq 48(%rdi),%r14
    adcq 56(%rdi),%r15
")

private def sqr8x_add_words : Program := parse("adcq 0(%rdi),%r8") ++ sqr8x_add_high
private def sqr8x_add_words_no_carry : Program := parse("addq 0(%rdi),%r8") ++ sqr8x_add_high


def sqr8x_reduce_tail : Program := parse("
    leaq 64(%rbp),%rbp
    xorq %rax,%rax
    movq 16(%rsp),%rdx
    cmpq 8(%rsp),%rbp
    jae .L8x_no_tail
") ++ sqr8x_add_words_no_carry ++ parse("
    sbbq %rsi,%rsi
    movq 112(%rsp),%rbx
    movl $8,%ecx
    movq 0(%rbp),%rax
    jmp .L8x_tail
")

def sqr8x_tail_iteration : Program := parse("
    mulq %rbx
    addq %rax,%r8
    movq 8(%rbp),%rax
    movq %r8,(%rdi)
    movq %rdx,%r8
    adcq $0,%r8
    mulq %rbx
    addq %rax,%r9
    movq 16(%rbp),%rax
    adcq $0,%rdx
    addq %r9,%r8
    leaq 8(%rdi),%rdi
    movq %rdx,%r9
    adcq $0,%r9
    mulq %rbx
    addq %rax,%r10
    movq 24(%rbp),%rax
    adcq $0,%rdx
    addq %r10,%r9
    movq %rdx,%r10
    adcq $0,%r10
    mulq %rbx
    addq %rax,%r11
    movq 32(%rbp),%rax
    adcq $0,%rdx
    addq %r11,%r10
    movq %rdx,%r11
    adcq $0,%r11
    mulq %rbx
    addq %rax,%r12
    movq 40(%rbp),%rax
    adcq $0,%rdx
    addq %r12,%r11
    movq %rdx,%r12
    adcq $0,%r12
    mulq %rbx
    addq %rax,%r13
    movq 48(%rbp),%rax
    adcq $0,%rdx
    addq %r13,%r12
    movq %rdx,%r13
    adcq $0,%r13
    mulq %rbx
    addq %rax,%r14
    movq 56(%rbp),%rax
    adcq $0,%rdx
    addq %r14,%r13
    movq %rdx,%r14
    adcq $0,%r14
    mulq %rbx
    movq 40(%rsp,%rcx,8),%rbx
    addq %rax,%r15
    adcq $0,%rdx
    addq %r15,%r14
    movq 0(%rbp),%rax
    movq %rdx,%r15
    adcq $0,%r15
")

def sqr8x_tail_advance : Program := parse("
    leaq 64(%rbp),%rbp
    movq 16(%rsp),%rdx
    cmpq 8(%rsp),%rbp
    jae .L8x_tail_done
    movq 112(%rsp),%rbx
    negq %rsi
    movq 0(%rbp),%rax
") ++ sqr8x_add_words ++ parse("
    sbbq %rsi,%rsi
    movl $8,%ecx
    jmp .L8x_tail
")

def sqr8x_tail_carry : Program := parse("
    xorq %rax,%rax
    addq (%rdx),%r8
    adcq $0,%r9
    adcq $0,%r10
    adcq $0,%r11
    adcq $0,%r12
    adcq $0,%r13
    adcq $0,%r14
    adcq $0,%r15
    adcq $0,%rax
    negq %rsi
")


def sqr8x_reduction_finish : Program := parse("
") ++ sqr8x_add_words ++ parse("
    adcq $0,%rax
    movq -8(%rbp),%rcx
    xorq %rsi,%rsi
    movq %xmm2,%rbp
    movq %r8,0(%rdi)
    movq %r9,8(%rdi)
    movq %xmm3,%r9
    movq %r10,16(%rdi)
    movq %r11,24(%rdi)
    movq %r12,32(%rdi)
    movq %r13,40(%rdi)
    movq %r14,48(%rdi)
    movq %r15,56(%rdi)
    leaq 64(%rdi),%rdi
    cmpq %rdx,%rdi
    jb .L8x_reduction_loop
    ret
")


/-- Advance through tail blocks, flush the saved carry, and finish this pass. -/
def sqr8x_tail_finish : Program :=
  sqr8x_tail_advance ++ parse(".L8x_tail_done:") ++ sqr8x_tail_carry ++
  parse(".L8x_no_tail:") ++ sqr8x_reduction_finish

/-- The complete internal routine, including its return. The nested loop reuses
exactly the instruction fragments verified above. -/
def bn_sqr8x_internal_prog : Program :=
  parse("__bn_sqr8x_internal:") ++ sqr4x_first_preamble ++
  parse(".Lsqr4x_1st:") ++ sqr4x_first_iteration ++
  parse("cmpq $0,%rcx
    jne .Lsqr4x_1st") ++ sqr4x_first_tail ++
  parse(".Lsqr4x_outer:") ++ sqr4x_outer_preamble ++ sqr4x_inner_loop ++ sqr4x_outer_tail ++
  sqr4x_final_cross_products ++
  parse(".Lsqr4x_shift_n_add:") ++ sqr4x_shift_iteration ++
  parse("addq $32,%rbp
    jnz .Lsqr4x_shift_n_add") ++ sqr4x_shift_tail ++
  parse("__bn_sqr8x_reduction:") ++ sqr8x_reduction_preamble ++
  parse(".L8x_reduce:") ++ sqr8x_reduce_iteration ++
  parse("decl %ecx
    jnz .L8x_reduce") ++ sqr8x_reduce_tail ++
  parse(".L8x_tail:") ++ sqr8x_tail_iteration ++
  parse("decl %ecx
    jnz .L8x_tail") ++ sqr8x_tail_finish

attribute [local sym_simp] BitVec.zero_add
attribute [local grind unfold] sqr4xInnerResult
attribute [local grind norm]
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  Sqr4xInnerResult.out0_mk Sqr4xInnerResult.out1_mk
  Sqr4xInnerResult.carry0_mk Sqr4xInnerResult.carry1_mk

/-- Four first-pass outputs, with the two independent multiplication carries. -/
structure Sqr4xFirstResult where
  out0 : BitVec 64
  out1 : BitVec 64
  out2 : BitVec 64
  out3 : BitVec 64
  carry0 : BitVec 64
  carry1 : BitVec 64

/-- The first pass is two applications of the inner-loop arithmetic, starting
with zero accumulator limbs. It initializes four limbs without reading them. -/
def sqr4xFirstResult (a0 a1 previous c0 c1 x0 x1 x2 x3 : BitVec 64) :
    Sqr4xFirstResult :=
  let r := sqr4xInnerResult a0 a1 previous c0 c1 x0 x1 0 0
  let t := sqr4xInnerResult a0 a1 x1 r.carry0 r.carry1 x2 x3 0 0
  ⟨r.out0, r.out1, t.out0, t.out1, t.carry0, t.carry1⟩

attribute [local irreducible] sqr4xMac
attribute [local grind unfold] sqr4xFirstResult

@[local grind norm] private theorem Sqr4xFirstResult.out0_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).out0 = o0 := rfl
@[local grind norm] private theorem Sqr4xFirstResult.out1_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).out1 = o1 := rfl
@[local grind norm] private theorem Sqr4xFirstResult.out2_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).out2 = o2 := rfl
@[local grind norm] private theorem Sqr4xFirstResult.out3_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).out3 = o3 := rfl
@[local grind norm] private theorem Sqr4xFirstResult.carry0_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).carry0 = c0 := rfl
@[local grind norm] private theorem Sqr4xFirstResult.carry1_mk (o0 o1 o2 o3 c0 c1) :
    (Sqr4xFirstResult.mk o0 o1 o2 o3 c0 c1).carry1 = c1 := rfl

private abbrev firstResult (d : MachineData) (x0 x1 x2 x3 : Int) :=
  sqr4xFirstResult (d.regs.get64 .r14) (d.regs.get64 .r15) (d.regs.get64 .rax)
    (d.regs.get64 .r11) (d.regs.get64 .r13)
    (BitVec.ofInt 64 x0) (BitVec.ofInt 64 x1) (BitVec.ofInt 64 x2) (BitVec.ofInt 64 x3)

attribute [local grind norm] bv_add_zero bv_zero_add

private def firstWindowsDisjoint (a b : BitVec 64) : Prop :=
  ∀ u < 32, ∀ v < 32, a + BitVec.ofNat 64 u ≠ b + BitVec.ofNat 64 v

@[local grind =] private theorem first_prefetch_2_0 (m : DataMem) (a b : BitVec 64) (v : Int)
    (hdisj : firstWindowsDisjoint a b) :
    (m.storeInt (b) 8 v).loadInt (a + 16) 8 = m.loadInt (a + 16) 8 := by
  apply load_after_disjoint_store
  intro k hk l hl
  have h := hdisj (16 + k) (by omega) (0 + l) (by omega)
  grind only [= BitVec.ofNat_add]

@[local grind =] private theorem first_prefetch_3_0 (m : DataMem) (a b : BitVec 64) (v : Int)
    (hdisj : firstWindowsDisjoint a b) :
    (m.storeInt (b) 8 v).loadInt (a + 24) 8 = m.loadInt (a + 24) 8 := by
  apply load_after_disjoint_store
  intro k hk l hl
  have h := hdisj (24 + k) (by omega) (0 + l) (by omega)
  grind only [= BitVec.ofNat_add]

@[local grind =] private theorem first_prefetch_3_1 (m : DataMem) (a b : BitVec 64) (v : Int)
    (hdisj : firstWindowsDisjoint a b) :
    (m.storeInt (b + 8) 8 v).loadInt (a + 24) 8 = m.loadInt (a + 24) 8 := by
  apply load_after_disjoint_store
  intro k hk l hl
  have h := hdisj (24 + k) (by omega) (8 + l) (by omega)
  grind only [= BitVec.ofNat_add]

local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

attribute [local irreducible] firstWindowsDisjoint

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Functional correctness of the four-limb `.Lsqr4x_1st` body. The two
32-byte windows are disjoint because input prefetches overlap output stores. -/
theorem sqr4x_first_iteration_correct [CodeEnv] (d : MachineData) (x0 x1 x2 x3 : Int)
    (h_x0 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx) 8 = some x0)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx + 8) 8 = some x1)
    (h_x2 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx + 16) 8 = some x2)
    (h_x3 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rcx + 24) 8 = some x3)
    (h_t0 : (d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx) 8).isSome = true)
    (h_t1 : (d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx + 8) 8).isSome = true)
    (h_t2 : (d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx + 16) 8).isSome = true)
    (h_t3 : (d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .rcx + 24) 8).isSome = true)
    (hdisj : firstWindowsDisjoint
      (d.regs.get64 .rsi + d.regs.get64 .rcx)
      (d.regs.get64 .rdi + d.regs.get64 .rcx)) :
    ⦃ fun s => s = d ⦄ sqr4x_first_iteration ⦃ fun _ s =>
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.zmms = d.zmms ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r14 = d.regs.get64 .r14 ∧
      s.regs.get64 .r15 = d.regs.get64 .r15 ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x3 ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx + 32 ∧
      s.regs.get64 .r11 = (firstResult d x0 x1 x2 x3).carry0 ∧
      s.regs.get64 .r13 = (firstResult d x0 x1 x2 x3).carry1 ∧
      s.dmem = (((d.dmem.storeInt (d.regs.get64 .rdi + d.regs.get64 .rcx) 8
        (firstResult d x0 x1 x2 x3).out0.toIntOpaque).storeInt
          (d.regs.get64 .rdi + d.regs.get64 .rcx + 8) 8
          (firstResult d x0 x1 x2 x3).out1.toIntOpaque).storeInt
          (d.regs.get64 .rdi + d.regs.get64 .rcx + 16) 8
          (firstResult d x0 x1 x2 x3).out2.toIntOpaque).storeInt
          (d.regs.get64 .rdi + d.regs.get64 .rcx + 24) 8
          (firstResult d x0 x1 x2 x3).out3.toIntOpaque ⦄ := by
  vcgen [sqr4x_first_iteration] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

private theorem addCarry_cancel (a b : BitVec 64) (h : a + b = 0) :
    addCarry a b = BitVec.ofNat 64 (b != 0).toNat := by
  have hzero : b = 0 ↔ a.toNat + b.toNat = 0 := by
    constructor
    · intro hb
      have ha : a = 0 := by simpa [hb] using h
      simp [ha, hb]
    · intro hb
      exact BitVec.eq_of_toNat_eq (by change b.toNat = 0; omega)
  dsimp only [addCarry]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  rw [h]
  change (0 : Int) ≠ ↑a.toNat + ↑b.toNat ↔ b ≠ 0
  rw [← Int.natCast_add]
  simp only [Ne, eq_comm (a := (0 : Int)), Int.natCast_eq_zero]
  exact not_congr hzero.symm

private theorem sqr4xMac_cancel (a b c : BitVec 64)
    (h : a * b + c = 0) :
    (sqr4xMac a b c 0).2 = mulHi a b + BitVec.ofNat 64 (c != 0).toNat := by
  rw [sqr4xMac_eq]
  dsimp only [macHi]
  rw [addCarry_cancel _ _ h]
  simp [addCarry, h]

/-- The Montgomery coefficient cancels the low word. The `neg`/`adc` pair
computes the carry of that cancellation without explicitly adding the low word. -/
theorem sqr8x_reduce_cancel_correct [CodeEnv] (d : MachineData) (m1 : Int)
    (h_load : d.dmem.loadInt (d.regs.get64 .rbp + 8) 8 = some m1)
    (h_cancel : d.regs.get64 .rax * d.regs.get64 .rbx + d.regs.get64 .r8 = 0) :
    ⦃ fun s => s = d ⦄ sqr8x_reduce_cancel ⦃ fun _ s =>
      s.regs.get64 .rax = BitVec.ofInt 64 m1 ∧
      s.regs.get64 .rbx = d.regs.get64 .rbx ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .r8 =
        (sqr4xMac (d.regs.get64 .rax) (d.regs.get64 .rbx) (d.regs.get64 .r8) 0).2 ∧
      s.dmem = d.dmem ⦄ := by
  vcgen [sqr8x_reduce_cancel] simplifying_assumptions with
    finish (splits := 0) [sqr4xMac_cancel
      (d.regs.get64 .rax) (d.regs.get64 .rbx) (d.regs.get64 .r8) h_cancel]

section Sqr4xFirstLoop

/-- A standalone entry to the first cross-product pass. The full routine
enters the same loop from `sqr4x_first_preamble`. -/
def sqr4x_first_prog : Program :=
  parse("first_start:
    leaq (%rbp),%rcx
.Lsqr4x_1st:") ++ sqr4x_first_iteration ++ parse("
    cmpq $0,%rcx
    jne .Lsqr4x_1st
")

private theorem replicate_zero_getD (n i : Nat) :
    (List.replicate n (0 : BitVec 64)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- The first pass uses the existing two-limb reference fold with zero
accumulator addends. One assembly iteration advances that fold twice. -/
private theorem first_prefix_step (d : MachineData) (n : Nat) (x : List (BitVec 64)) (j : Nat) :
    sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) (j + 2) =
      let st := sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
      let r := sqr4xFirstResult (d.regs.get64 .r14) (d.regs.get64 .r15)
        st.previous st.carry0 st.carry1
        (x.getD (2 * j) 0) (x.getD (2 * j + 1) 0)
        (x.getD (2 * j + 2) 0) (x.getD (2 * j + 3) 0)
      ⟨x.getD (2 * j + 3) 0, r.carry0, r.carry1,
        (((st.memory.storeInt (d.regs.get64 .rdi + innerOffset n j) 8 r.out0.toIntOpaque).storeInt
          (d.regs.get64 .rdi + innerOffset n j + 8) 8 r.out1.toIntOpaque).storeInt
          (d.regs.get64 .rdi + innerOffset n j + 16) 8 r.out2.toIntOpaque).storeInt
          (d.regs.get64 .rdi + innerOffset n j + 24) 8 r.out3.toIntOpaque⟩ := by
  rw [show j + 2 = (j + 1) + 1 by omega, prefix_step, prefix_step]
  simp only [replicate_zero_getD, sqr4xFirstResult, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc, innerOffset, BitVec.ofNat_add]
  have haddr : d.regs.get64 .rdi + (BitVec.ofNat 64 (16 * j) + 16#64 - BitVec.ofNat 64 (16 * n)) =
      d.regs.get64 .rdi + (BitVec.ofNat 64 (16 * j) - BitVec.ofNat 64 (16 * n)) + 16 := by grind
  rw [haddr]
  simp only [show ∀ a : BitVec 64, a + 16 + 8 = a + 24 from by intros; grind]

@[local grind =] private theorem offset_step_two (n j : Nat) :
    innerOffset n j + 32 = innerOffset n (j + 2) := by
  simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add]
  grind

local grind_pattern offset_facts => innerOffset n k

private theorem offset_continue_two (n j : Nat) (hj : j + 2 ≤ n)
    (hb : 16 * n < 2 ^ 63) (hne : (innerOffset n j + 32).toNat ≠ 0) :
    j + 2 < n ∧ innerIndex n (innerOffset n j + 32) = j + 2 ∧
    2 ^ 64 - (innerOffset n j + 32).toNat < 2 ^ 64 - (innerOffset n j).toNat := by
  grind only [= offset_step_two, usr offset_facts]

private theorem first_fold_subdom (a0 a1 : BitVec 64) (x t : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr4xInnerState) (j : Nat) :
    Mem.SubDom initial.memory (sqr4xInnerFold a0 a1 x t base initial j).memory := by
  induction j with
  | zero => exact Mem.SubDom.refl _
  | succ j ih => exact (ih.storeInt _ _ _).storeInt _ _ _

private def firstFrame (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) : Prop :=
  d.dmem =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
    (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))) ⋆
    (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))) ⋆ R)

private theorem first_prefix_load (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 16 * n < 2 ^ 63)
    (hxl : x.length = 2 * n) (htl : t.length = 2 * n) (hm : firstFrame d n x t R)
    (j i : Nat) (hj : j + 2 ≤ n) (hi : i < 4) :
    let st := sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
    st.memory.loadInt (d.regs.get64 .rsi + innerOffset n j + BitVec.ofNat 64 (8 * i)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + i) 0).toInt)) ∧
    (st.memory.loadInt (d.regs.get64 .rdi + innerOffset n j + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  have ha (r : Reg64) : d.regs.get64 r + innerOffset n j + BitVec.ofNat 64 (8 * i) =
      d.regs.get64 r - BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 (8 * (2 * j + i)) := by
    simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add]
    grind
  dsimp only
  rw [ha .rsi, ha .rdi]
  constructor
  · rw [sqr4xInnerPrefix, fold_load_unchanged]
    · exact load_limb hm (by omega) (2 * j + i) (by omega)
    · intro k hk l hl
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        sep_At_ne hm (8 * (2 * j + i) + k) (by rw [length_flatMap_limbs]; omega)
          l (by rw [length_flatMap_limbs]; omega)
  · change ((sqr4xInnerFold _ _ _ _ _ ⟨_, _, _, d.dmem⟩ j).memory.loadInt _ 8).isSome = true
    apply Mem.SubDom.loadInt_isSome (m := d.dmem) (first_fold_subdom (d.regs.get64 .r14) (d.regs.get64 .r15)
      x (List.replicate (2 * n) 0) (d.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))
      ⟨d.regs.get64 .rax, d.regs.get64 .r11, d.regs.get64 .r13, d.dmem⟩ j)
    have hload := load_tp_limb (2 * j + i) hm (by omega) (by omega) rfl
    rw [hload]; rfl

private theorem first_prefix_disjoint (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hxl : x.length = 2 * n) (htl : t.length = 2 * n)
    (hm : firstFrame d n x t R) (j : Nat) (hj : j + 2 ≤ n) :
    firstWindowsDisjoint (d.regs.get64 .rsi + innerOffset n j)
      (d.regs.get64 .rdi + innerOffset n j) := by
  unfold firstWindowsDisjoint
  intro u hu v hv
  have h := sep_At_ne hm (16 * j + u) (by rw [length_flatMap_limbs]; omega)
    (16 * j + v) (by rw [length_flatMap_limbs]; omega)
  simp only [innerOffset, BitVec.ofNat_add] at *
  grind

private theorem first_iteration_accesses (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 16 * n < 2 ^ 63)
    (hxl : x.length = 2 * n) (htl : t.length = 2 * n) (hm : firstFrame d n x t R)
    (s : MachineData) (hj : innerIndex n (s.regs.get64 .rcx) + 2 ≤ n) :
    let j := innerIndex n (s.regs.get64 .rcx)
    let st := sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
    let a := d.regs.get64 .rsi + innerOffset n j
    let b := d.regs.get64 .rdi + innerOffset n j
    st.memory.loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j) 0).toInt)) ∧
    st.memory.loadInt (a + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + 1) 0).toInt)) ∧
    st.memory.loadInt (a + 16) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + 2) 0).toInt)) ∧
    st.memory.loadInt (a + 24) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (2 * j + 3) 0).toInt)) ∧
    (st.memory.loadInt b 8).isSome = true ∧
    (st.memory.loadInt (b + 8) 8).isSome = true ∧
    (st.memory.loadInt (b + 16) 8).isSome = true ∧
    (st.memory.loadInt (b + 24) 8).isSome = true ∧ firstWindowsDisjoint a b := by
  dsimp only
  have h0 := first_prefix_load d n x t R hb hxl htl hm _ 0 hj (by decide)
  have h1 := first_prefix_load d n x t R hb hxl htl hm _ 1 hj (by decide)
  have h2 := first_prefix_load d n x t R hb hxl htl hm _ 2 hj (by decide)
  have h3 := first_prefix_load d n x t R hb hxl htl hm _ 3 hj (by decide)
  have hd := first_prefix_disjoint d n x t R hxl htl hm _ hj
  grind only

private abbrev firstInvariant (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (s : MachineData) : Prop :=
  let j := innerIndex n (s.regs.get64 .rcx)
  let st := sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
  j + 2 ≤ n ∧ j % 2 = 0 ∧ s.regs.get64 .rcx = innerOffset n j ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧
  s.zmms = d.zmms ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi ∧
  s.regs.get64 .r14 = d.regs.get64 .r14 ∧
  s.regs.get64 .r15 = d.regs.get64 .r15 ∧
  s.regs.get64 .rax = st.previous ∧
  s.regs.get64 .r11 = st.carry0 ∧
  s.regs.get64 .r13 = st.carry1 ∧ s.dmem = st.memory

private abbrev firstTable (d : MachineData) (n : Nat) (x : List (BitVec 64)) :
    Label → MachineData → Prop
  | "first_start", s => s = d
  | ".Lsqr4x_1st", s => firstInvariant d n x s
  | _, _ => False

private abbrev firstVar : Label → MachineData → Nat
  | "first_start", _ => 2 ^ 64
  | ".Lsqr4x_1st", s => 2 ^ 64 - (s.regs.get64 .rcx).toNat
  | _, _ => 0

attribute [local irreducible] innerOffset innerIndex sqr4xInnerPrefix firstFrame
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
  CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind unfold] sqr4xFirstResult sqr4xInnerResult
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add
  CondCode.interp_nz StatusFlags.zf_from_result
  Sqr4xInnerResult.out0_mk Sqr4xInnerResult.out1_mk
  Sqr4xInnerResult.carry0_mk Sqr4xInnerResult.carry1_mk
  Sqr4xFirstResult.out0_mk Sqr4xFirstResult.out1_mk Sqr4xFirstResult.out2_mk Sqr4xFirstResult.out3_mk
  Sqr4xFirstResult.carry0_mk Sqr4xFirstResult.carry1_mk
attribute [local grind =] ofInt_limb prefix_zero offset_initial_index offset_step_two offset_zero
  first_prefetch_2_0 first_prefetch_3_0 first_prefetch_3_1
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern offset_facts => innerOffset n k
local grind_pattern offset_continue_two => innerOffset n j + 32
local grind_pattern first_prefix_step => innerOffset n j + 32,
  sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
local grind_pattern first_iteration_accesses =>
  innerIndex n (s.regs.get64 .rcx), firstFrame d n x t R

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr4x_first_prog)]
local instance : CodeEnv := ⟨layout sqr4x_first_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Functional correctness of the complete first pass. `n` counts pairs;
its four-limb unrolling requires a positive even number of pairs. -/
theorem sqr4x_first_prog_correct (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 (16 * n))
    (h_pos : 0 < n) (h_even : n % 2 = 0) (h_bound : 16 * n < 2 ^ 63)
    (h_x_len : x.length = 2 * n) (h_t_len : t.length = 2 * n) (R : DataMem → Prop)
    (h_mem : firstFrame d n x t R) :
    ⦃ fun s => s = d ⦄ sqr4x_first_prog ⦃ fun _ s =>
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.zmms = d.zmms ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r14 = d.regs.get64 .r14 ∧
      s.regs.get64 .r15 = d.regs.get64 .r15 ∧
      s.regs.get64 .rcx = 0#64 ∧
      s.regs.get64 .rax = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).previous ∧
      s.regs.get64 .r11 = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).carry0 ∧
      s.regs.get64 .r13 = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).carry1 ∧
      s.dmem = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).memory ⦄ := by
  apply MachineWP.cfg (firstTable d n x) firstVar
  cfg_cases [sqr4x_first_prog, sqr4x_first_iteration]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish (splits := 4) (hom := false) (canonHeartbeats := 5)
end

end Sqr4xFirstLoop

section Sqr4xFirstEnds


/-- The first three cross-product words use the same startup arithmetic as an
outer pass, with zero accumulator addends. -/
def sqr4xFirstPreambleResult (d : MachineData) (n : Nat) (x : List (BitVec 64)) :
    Sqr4xOuterInnerState :=
  sqr4xOuterPreambleStep x (d.regs.get64 .rsp + d.regs.get64 .r9 * 2 + 56) n 0
    ⟨List.replicate (4 * n + 8) 0, d.dmem⟩

private theorem first_preamble_result_fields (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (hr9 : d.regs.get64 .r9 = BitVec.ofNat 64 (16 * n + 32)) :
    let a0 := x.getD 0 0
    let a1 := x.getD 1 0
    let a2 := x.getD 2 0
    let a3 := x.getD 3 0
    let p1 := sqr4xMac a1 a0 0 0
    let p2 := sqr4xMac a2 a0 p1.2 0
    let p3 := sqr4xMac a2 a1 0 0
    let p4 := sqr4xMac a3 a0 p2.2 p3.1
    let r := sqr4xFirstPreambleResult d n x
    r.previous = a3 ∧ r.carry0 = p4.2 ∧ r.carry1 = p3.2 ∧
      r.memory = ((d.dmem.storeInt (d.regs.get64 .rsp + 64) 8 p1.1.toIntOpaque).storeInt
        (d.regs.get64 .rsp + 72) 8 p2.1.toIntOpaque).storeInt
        (d.regs.get64 .rsp + 80) 8 p4.1.toIntOpaque := by
  dsimp only [sqr4xFirstPreambleResult, sqr4xOuterPreambleStep]
  simp only [replicate_zero_getD, Nat.mul_zero, Nat.zero_add]
  grind only [innerOffset, = BitVec.ofNat_add]

@[local grind =] private theorem first_preamble_prefetch (m : DataMem) (a sp : BitVec 64)
    (v w : Int) (hd : firstWindowsDisjoint a (sp + 64)) :
    ((m.storeInt (sp + 64) 8 v).storeInt (sp + 72) 8 w).loadInt (a + 24) 8 =
      m.loadInt (a + 24) 8 := by
  have h := first_prefetch_3_1 (m.storeInt (sp + 64) 8 v) a (sp + 64) w hd
  have he : sp + 64 + 8 = sp + 72 := by grind
  rw [he] at h
  rw [h, first_prefetch_3_0 m a (sp + 64) v hd]

attribute [local irreducible] sqr4xFirstPreambleResult
attribute [local grind norm] MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk
  MachineData.dmem_mk Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8
  Width.scaleFactor_W16 BitVec.mul_one StatusFlags.cf_from_result
  StatusFlags.from_result.Remaining.cf_mk sqr4xMac_eq BitVec.unsigned_eq
  Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
attribute [local grind =] ofInt_limb first_prefetch_3_0 first_prefetch_3_1
local grind_pattern first_preamble_result_fields => sqr4xFirstPreambleResult d n x
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Entry setup and the first three cross-product words. -/
theorem sqr4x_first_preamble_correct [CodeEnv] (d : MachineData) (n : Nat)
    (x : List (BitVec 64))
    (h_r9 : d.regs.get64 .r9 = BitVec.ofNat 64 (16 * n + 32))
    (h_r10 : d.regs.get64 .r10 = -d.regs.get64 .r9)
    (h_x0 : d.dmem.loadInt (d.regs.get64 .rsi + 0) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD 0 0).toInt)))
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD 1 0).toInt)))
    (h_x2 : d.dmem.loadInt (d.regs.get64 .rsi + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD 2 0).toInt)))
    (h_x3 : d.dmem.loadInt (d.regs.get64 .rsi + 24) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD 3 0).toInt)))
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rsp + 64) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rsp + 72) 8).isSome = true)
    (h_o2 : (d.dmem.loadInt (d.regs.get64 .rsp + 80) 8).isSome = true)
    (hd : firstWindowsDisjoint (d.regs.get64 .rsi) (d.regs.get64 .rsp + 64)) :
    ⦃ fun s => s = d ⦄ sqr4x_first_preamble ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_1st" ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.zmms = d.zmms ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi + d.regs.get64 .r9 ∧
      s.regs.get64 .rdi = d.regs.get64 .rsp + d.regs.get64 .r9 + 56 ∧
      s.regs.get64 .rbp = 32 - d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 32 - d.regs.get64 .r9 ∧
      s.regs.get64 .r14 = x.getD 0 0 ∧ s.regs.get64 .r15 = x.getD 1 0 ∧
      s.regs.get64 .rax = (sqr4xFirstPreambleResult d n x).previous ∧
      s.regs.get64 .r11 = (sqr4xFirstPreambleResult d n x).carry0 ∧
      s.regs.get64 .r13 = (sqr4xFirstPreambleResult d n x).carry1 ∧
      s.dmem = (sqr4xFirstPreambleResult d n x).memory ⦄ := by
  vcgen [sqr4x_first_preamble] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

private abbrev firstTailResult (d : MachineData) :=
  sqr4xMac (d.regs.get64 .rax) (d.regs.get64 .r15)
    (d.regs.get64 .r13) (d.regs.get64 .r11)

attribute [local grind norm] MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk
  MachineData.dmem_mk Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8
  BitVec.mul_one StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

/-- Flush the first pass's two carry chains before entering the outer loop. -/
theorem sqr4x_first_tail_correct [CodeEnv] (d : MachineData)
    (h0 : (d.dmem.loadInt (d.regs.get64 .rdi) 8).isSome = true)
    (h1 : (d.dmem.loadInt (d.regs.get64 .rdi + 8) 8).isSome = true) :
    ⦃ fun s => s = d ⦄ sqr4x_first_tail ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_outer" ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp + 16 ∧
      s.regs.get64 .r13 = (firstTailResult d).1 ∧
      s.regs.get64 .r12 = (firstTailResult d).2 ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi) 8 (firstTailResult d).1.toIntOpaque).storeInt
        (d.regs.get64 .rdi + 8) 8 (firstTailResult d).2.toIntOpaque ⦄ := by
  vcgen [sqr4x_first_tail] simplifying_assumptions with finish (splits := 0)

end Sqr4xFirstEnds

section Sqr8xReduceIteration

/-- Eight limbs used by the unrolled Montgomery multiplication blocks. -/
structure Sqr8xWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64

/-- Multiply the modulus block by `q`, add the incoming eight words, discard
its cancelled low word, and retain the outgoing high carry. -/
def sqr8xReduceResult (q : BitVec 64) (m t : Sqr8xWords) : Sqr8xWords :=
  let p0 := sqr4xMac m.w0 q t.w0 0
  let p1 := sqr4xMac m.w1 q t.w1 p0.2
  let p2 := sqr4xMac m.w2 q t.w2 p1.2
  let p3 := sqr4xMac m.w3 q t.w3 p2.2
  let p4 := sqr4xMac m.w4 q t.w4 p3.2
  let p5 := sqr4xMac m.w5 q t.w5 p4.2
  let p6 := sqr4xMac m.w6 q t.w6 p5.2
  let p7 := sqr4xMac m.w7 q t.w7 p6.2
  ⟨p1.1, p2.1, p3.1, p4.1, p5.1, p6.1, p7.1, p7.2⟩

private abbrev reductionWords (d : MachineData) : Sqr8xWords :=
  ⟨d.regs.get64 .r8, d.regs.get64 .r9, d.regs.get64 .r10, d.regs.get64 .r11,
    d.regs.get64 .r12, d.regs.get64 .r13, d.regs.get64 .r14, d.regs.get64 .r15⟩

private abbrev reductionResult (d : MachineData) (m : Sqr8xWords) :=
  sqr8xReduceResult (d.regs.get64 .rbx) m (reductionWords d)

private def readWindowDisjoint (a b : BitVec 64) (n : Nat) : Prop :=
  ∀ i < n, ∀ j < 8, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j

private theorem load_window_after_store (mem : DataMem) (a b : BitVec 64) (v : Int)
    (n i : Nat) (hi : i + 8 ≤ n) (hd : readWindowDisjoint a b n) :
    (mem.storeInt b 8 v).loadInt (a + BitVec.ofNat 64 i) 8 =
      mem.loadInt (a + BitVec.ofNat 64 i) 8 := by
  apply load_after_disjoint_store
  intro j hj k hk
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    hd (i + j) (by omega) k hk

private theorem modulus_loads_after_store (mem : DataMem) (a b : BitVec 64) (v : Int)
    (hd : readWindowDisjoint a b 64) :
    (mem.storeInt b 8 v).loadInt (a + 0) 8 = mem.loadInt (a + 0) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 8) 8 = mem.loadInt (a + 8) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 16) 8 = mem.loadInt (a + 16) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 24) 8 = mem.loadInt (a + 24) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 32) 8 = mem.loadInt (a + 32) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 40) 8 = mem.loadInt (a + 40) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 48) 8 = mem.loadInt (a + 48) 8 ∧
    (mem.storeInt b 8 v).loadInt (a + 56) 8 = mem.loadInt (a + 56) 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact load_window_after_store mem a b v 64 0 (by decide) hd
  · exact load_window_after_store mem a b v 64 8 (by decide) hd
  · exact load_window_after_store mem a b v 64 16 (by decide) hd
  · exact load_window_after_store mem a b v 64 24 (by decide) hd
  · exact load_window_after_store mem a b v 64 32 (by decide) hd
  · exact load_window_after_store mem a b v 64 40 (by decide) hd
  · exact load_window_after_store mem a b v 64 48 (by decide) hd
  · exact load_window_after_store mem a b v 64 56 (by decide) hd

private theorem inverse_load_after_store (mem : DataMem) (a b : BitVec 64) (v : Int)
    (hd : readWindowDisjoint a b 8) :
    (mem.storeInt b 8 v).loadInt a 8 = mem.loadInt a 8 := by
  simpa only [BitVec.add_zero] using
    load_window_after_store mem a b v 8 0 (by decide) hd

attribute [local irreducible] readWindowDisjoint
attribute [local grind unfold] sqr8xReduceResult
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
  List.cons_append List.nil_append
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add
attribute [local grind =] ofInt_limb
local grind_pattern modulus_loads_after_store => mem.storeInt b 8 v, readWindowDisjoint a b 64
local grind_pattern inverse_load_after_store => mem.storeInt b 8 v, readWindowDisjoint a b 8

@[local grind norm] private theorem Sqr8xWords.w0_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w0 = w0 := rfl
@[local grind norm] private theorem Sqr8xWords.w1_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w1 = w1 := rfl
@[local grind norm] private theorem Sqr8xWords.w2_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w2 = w2 := rfl
@[local grind norm] private theorem Sqr8xWords.w3_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w3 = w3 := rfl
@[local grind norm] private theorem Sqr8xWords.w4_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w4 = w4 := rfl
@[local grind norm] private theorem Sqr8xWords.w5_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w5 = w5 := rfl
@[local grind norm] private theorem Sqr8xWords.w6_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w6 = w6 := rfl
@[local grind norm] private theorem Sqr8xWords.w7_mk (w0 w1 w2 w3 w4 w5 w6 w7) :
    (Sqr8xWords.mk w0 w1 w2 w3 w4 w5 w6 w7).w7 = w7 := rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- One full eight-limb Montgomery reduction iteration. Its coefficient is
saved on the stack, and the next coefficient is computed from the next low word.
The bytewise disjointness hypotheses ensure that this save preserves the modulus
and the inverse word read later in the same iteration. -/
theorem sqr8x_reduce_iteration_correct [CodeEnv] (d : MachineData) (m : Sqr8xWords)
    (n0 : BitVec 64)
    (h_rax : d.regs.get64 .rax = m.w0)
    (h_cancel : m.w0 * d.regs.get64 .rbx + d.regs.get64 .r8 = 0)
    (h_m0 : d.dmem.loadInt (d.regs.get64 .rbp + 0) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w0.toInt)))
    (h_m1 : d.dmem.loadInt (d.regs.get64 .rbp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w1.toInt)))
    (h_m2 : d.dmem.loadInt (d.regs.get64 .rbp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w2.toInt)))
    (h_m3 : d.dmem.loadInt (d.regs.get64 .rbp + 24) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w3.toInt)))
    (h_m4 : d.dmem.loadInt (d.regs.get64 .rbp + 32) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w4.toInt)))
    (h_m5 : d.dmem.loadInt (d.regs.get64 .rbp + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w5.toInt)))
    (h_m6 : d.dmem.loadInt (d.regs.get64 .rbp + 48) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w6.toInt)))
    (h_m7 : d.dmem.loadInt (d.regs.get64 .rbp + 56) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w7.toInt)))
    (h_n0 : d.dmem.loadInt (d.regs.get64 .rsp + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 n0.toInt)))
    (h_slot : (d.dmem.loadInt
      (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 48) 8).isSome = true)
    (h_mod_disjoint : readWindowDisjoint (d.regs.get64 .rbp)
      (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 48) 64)
    (h_inv_disjoint : readWindowDisjoint (d.regs.get64 .rsp + 40)
      (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 48) 8) :
    ⦃ fun s => s = d ⦄ sqr8x_reduce_iteration ⦃ fun _ s =>
      s.regs.get64 .rax = m.w0 ∧
      s.regs.get64 .rbx = (reductionResult d m).w0 * n0 ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r8 = (reductionResult d m).w0 ∧
      s.regs.get64 .r9 = (reductionResult d m).w1 ∧
      s.regs.get64 .r10 = (reductionResult d m).w2 ∧
      s.regs.get64 .r11 = (reductionResult d m).w3 ∧
      s.regs.get64 .r12 = (reductionResult d m).w4 ∧
      s.regs.get64 .r13 = (reductionResult d m).w5 ∧
      s.regs.get64 .r14 = (reductionResult d m).w6 ∧
      s.regs.get64 .r15 = (reductionResult d m).w7 ∧
      s.zmms = d.zmms ∧
      s.dmem = d.dmem.storeInt (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 48) 8
        (d.regs.get64 .rbx).toIntOpaque ⦄ := by
  vcgen [sqr8x_reduce_iteration, sqr8x_reduce_cancel] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)
      [sqr4xMac_cancel m.w0 (d.regs.get64 .rbx) (d.regs.get64 .r8) h_cancel]

end Sqr8xReduceIteration

section Sqr8xTailIteration
attribute [local irreducible] readWindowDisjoint
attribute [local grind unfold] sqr8xReduceResult
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
  List.cons_append List.nil_append
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add
attribute [local grind =] ofInt_limb
local grind_pattern modulus_loads_after_store => mem.storeInt b 8 v, readWindowDisjoint a b 64
local grind_pattern inverse_load_after_store => mem.storeInt b 8 v, readWindowDisjoint a b 8

attribute [local grind norm]
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- One eight-word tail multiplication: save the low word, propagate all
seven remaining words and the high carry, and fetch the next saved coefficient. -/
theorem sqr8x_tail_iteration_correct [CodeEnv] (d : MachineData) (m : Sqr8xWords)
    (nextCoefficient : BitVec 64)
    (h_rax : d.regs.get64 .rax = m.w0)
    (h_m0 : d.dmem.loadInt (d.regs.get64 .rbp + 0) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w0.toInt)))
    (h_m1 : d.dmem.loadInt (d.regs.get64 .rbp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w1.toInt)))
    (h_m2 : d.dmem.loadInt (d.regs.get64 .rbp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w2.toInt)))
    (h_m3 : d.dmem.loadInt (d.regs.get64 .rbp + 24) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w3.toInt)))
    (h_m4 : d.dmem.loadInt (d.regs.get64 .rbp + 32) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w4.toInt)))
    (h_m5 : d.dmem.loadInt (d.regs.get64 .rbp + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w5.toInt)))
    (h_m6 : d.dmem.loadInt (d.regs.get64 .rbp + 48) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w6.toInt)))
    (h_m7 : d.dmem.loadInt (d.regs.get64 .rbp + 56) 8 =
      some (Int.ofBytes (Int.toBytes 8 m.w7.toInt)))
    (h_next : d.dmem.loadInt (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 nextCoefficient.toInt)))
    (h_slot : (d.dmem.loadInt (d.regs.get64 .rdi) 8).isSome = true)
    (h_mod_disjoint : readWindowDisjoint (d.regs.get64 .rbp) (d.regs.get64 .rdi) 64)
    (h_coefficient_disjoint : readWindowDisjoint
      (d.regs.get64 .rsp + d.regs.get64 .rcx * 8 + 40) (d.regs.get64 .rdi) 8) :
    ⦃ fun s => s = d ⦄ sqr8x_tail_iteration ⦃ fun _ s =>
      s.regs.get64 .rax = m.w0 ∧
      s.regs.get64 .rbx = nextCoefficient ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi + 8 ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .r8 = (reductionResult d m).w0 ∧
      s.regs.get64 .r9 = (reductionResult d m).w1 ∧
      s.regs.get64 .r10 = (reductionResult d m).w2 ∧
      s.regs.get64 .r11 = (reductionResult d m).w3 ∧
      s.regs.get64 .r12 = (reductionResult d m).w4 ∧
      s.regs.get64 .r13 = (reductionResult d m).w5 ∧
      s.regs.get64 .r14 = (reductionResult d m).w6 ∧
      s.regs.get64 .r15 = (reductionResult d m).w7 ∧
      s.zmms = d.zmms ∧
      s.dmem = d.dmem.storeInt (d.regs.get64 .rdi) 8
        (sqr4xMac m.w0 (d.regs.get64 .rbx) (d.regs.get64 .r8) 0).1.toIntOpaque ⦄ := by
  vcgen [sqr8x_tail_iteration] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end Sqr8xTailIteration

section Sqr8xReduceLoop

/-- Arithmetic state after cancelling a prefix of an eight-word block. -/
structure Sqr8xReduceState where
  words : Sqr8xWords
  coefficient : BitVec 64
  memory : DataMem

/-- The eight cancellation steps save coefficients from the high end of the
64-byte coefficient area downwards, in the order used by the tail loop. -/
def sqr8xReduceFold (m : Sqr8xWords) (n0 sp : BitVec 64) (initial : Sqr8xReduceState) :
    Nat → Sqr8xReduceState
  | 0 => initial
  | k + 1 =>
    let s := sqr8xReduceFold m n0 sp initial k
    let r := sqr8xReduceResult s.coefficient m s.words
    ⟨r, r.w0 * n0,
      s.memory.storeInt (sp + BitVec.ofNat 64 (112 - 8 * k)) 8 s.coefficient.toIntOpaque⟩

def sqr8xReducePrefix (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64) (k : Nat) :
    Sqr8xReduceState :=
  sqr8xReduceFold m n0 (d.regs.get64 .rsp)
    ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ k

private theorem reduce_coefficient_cancels (m0 n0 t0 : BitVec 64)
    (h : m0 * n0 + 1 = 0) : m0 * (t0 * n0) + t0 = 0 := by
  grind (hom := false)

private theorem reduce_prefix_coefficient (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64)
    (h : d.regs.get64 .rbx = d.regs.get64 .r8 * n0) (k : Nat) :
    (sqr8xReducePrefix d m n0 k).coefficient = (sqr8xReducePrefix d m n0 k).words.w0 * n0 := by
  cases k <;> simp only [sqr8xReducePrefix, sqr8xReduceFold, reductionWords] <;> assumption

private theorem reduce_prefix_cancel (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64)
    (h : d.regs.get64 .rbx = d.regs.get64 .r8 * n0) (h0 : m.w0 * n0 + 1 = 0) (k : Nat) :
    m.w0 * (sqr8xReducePrefix d m n0 k).coefficient + (sqr8xReducePrefix d m n0 k).words.w0 = 0 := by
  rw [reduce_prefix_coefficient d m n0 h k]
  exact reduce_coefficient_cancels _ _ _ h0

private theorem reduce_fold_subdom (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) :
    Mem.SubDom initial.memory (sqr8xReduceFold m n0 sp initial k).memory := by
  induction k with
  | zero => exact Mem.SubDom.refl _
  | succ k ih => exact ih.storeInt _ _ _

private theorem reduce_fold_load (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) (addr : BitVec 64)
    (hd : ∀ j < k, ∀ u < 8, ∀ v < 8,
      addr + BitVec.ofNat 64 u ≠ sp + BitVec.ofNat 64 (112 - 8 * j) + BitVec.ofNat 64 v) :
    (sqr8xReduceFold m n0 sp initial k).memory.loadInt addr 8 = initial.memory.loadInt addr 8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [sqr8xReduceFold]
    rw [load_after_disjoint_store]
    · exact ih (by intro j hj; exact hd j (by omega))
    · exact hd k (by omega)

private theorem reduce_prefix_zero (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64) :
    sqr8xReducePrefix d m n0 0 = ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ := rfl

private theorem set_low32 (r : Reg64s) (dst : Reg64) (v : BitVec 32) :
    r.set (.low dst .W32) v = r.set64 dst (v.zeroExtend 64) := rfl

private theorem get_low32 (r : Reg64s) (src : Reg64) :
    r.get (.low src .W32) = (r.get64 src).setWidth 32 := by
  simp only [Reg64s.get, Reg.offset, Reg.base, BitVec.drop, BitVec.take]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_setWidth]

private def reduceCount (j : Nat) : BitVec 64 := BitVec.ofNat 64 (8 - j)
private def reduceIndex (c : BitVec 64) : Nat := 8 - c.toNat

private theorem reduce_counter_facts (j : Nat) (hj : j ≤ 8) :
    (reduceCount j).toNat = 8 - j ∧ reduceIndex (reduceCount j) = j ∧
    (reduceCount j = 0 ↔ j = 8) := by
  simp only [reduceCount, reduceIndex, BitVec.toNat_ofNat]
  have hmod : (8 - j) % 2 ^ 64 = 8 - j := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  constructor
  · rfl
  constructor
  · omega
  · constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega
    · rintro rfl; rfl

private theorem reduce_counter_step (j : Nat) (hj : j < 8) :
    ((reduceCount j).setWidth 32 - 1).zeroExtend 64 = reduceCount (j + 1) ∧
    (((reduceCount j).setWidth 32 - 1).toNat = 0 ↔ j + 1 = 8) ∧
    (reduceCount (j + 1)).toNat < (reduceCount j).toNat := by
  have hh : (((reduceCount j).setWidth 32 - 1) : BitVec 32).toNat = 7 - j := by
    simp only [reduceCount, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine ⟨?_, by omega, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, hh]
    simp only [reduceCount, BitVec.toNat_ofNat]
    omega
  · simp only [reduceCount, BitVec.toNat_ofNat]
    omega

private abbrev Sqr8xWords.get (m : Sqr8xWords) (i : Nat) : BitVec 64 :=
  [m.w0, m.w1, m.w2, m.w3, m.w4, m.w5, m.w6, m.w7].getD i 0

private def reduceFrame (mem : DataMem) (mp sp : BitVec 64) (m : Sqr8xWords) (n0 : BitVec 64) : Prop :=
  (∀ i < 8, mem.loadInt (mp + BitVec.ofNat 64 (8 * i)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (m.get i).toInt))) ∧
  mem.loadInt (sp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 n0.toInt)) ∧
  ∀ j < 8,
    (mem.loadInt (sp + BitVec.ofNat 64 (112 - 8 * j)) 8).isSome = true ∧
    readWindowDisjoint mp (sp + BitVec.ofNat 64 (112 - 8 * j)) 64 ∧
    readWindowDisjoint (sp + 40) (sp + BitVec.ofNat 64 (112 - 8 * j)) 8

private theorem reduce_prefix_frame (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64)
    (hf : reduceFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) m n0)
    (k : Nat) (hk : k ≤ 8) :
    reduceFrame (sqr8xReducePrefix d m n0 k).memory (d.regs.get64 .rbp) (d.regs.get64 .rsp) m n0 := by
  obtain ⟨hm, hn, hs⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [sqr8xReducePrefix, reduce_fold_load]
    · exact hm i hi
    · intro j hj u hu v hv he
      have h := (hs j (by omega)).2.1 (8 * i + u) (by omega) v hv
      simp only [BitVec.ofNat_add, BitVec.add_assoc] at h
      exact h (by simpa only [BitVec.add_assoc] using he)
  · rw [sqr8xReducePrefix, reduce_fold_load]
    · exact hn
    · intro j hj u hu v hv
      exact (hs j (by omega)).2.2 u hu v hv
  · intro j hj
    refine ⟨?_, (hs j hj).2⟩
    exact Mem.SubDom.loadInt_isSome (reduce_fold_subdom m n0 (d.regs.get64 .rsp)
      ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ k) (hs j hj).1

private theorem reduce_frame_loads (mem : DataMem) (mp sp : BitVec 64)
    (m : Sqr8xWords) (n0 : BitVec 64) (h : reduceFrame mem mp sp m n0) :
    mem.loadInt (mp + 0) 8 = some (Int.ofBytes (Int.toBytes 8 m.w0.toInt)) ∧
    mem.loadInt (mp + 8) 8 = some (Int.ofBytes (Int.toBytes 8 m.w1.toInt)) ∧
    mem.loadInt (mp + 16) 8 = some (Int.ofBytes (Int.toBytes 8 m.w2.toInt)) ∧
    mem.loadInt (mp + 24) 8 = some (Int.ofBytes (Int.toBytes 8 m.w3.toInt)) ∧
    mem.loadInt (mp + 32) 8 = some (Int.ofBytes (Int.toBytes 8 m.w4.toInt)) ∧
    mem.loadInt (mp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 m.w5.toInt)) ∧
    mem.loadInt (mp + 48) 8 = some (Int.ofBytes (Int.toBytes 8 m.w6.toInt)) ∧
    mem.loadInt (mp + 56) 8 = some (Int.ofBytes (Int.toBytes 8 m.w7.toInt)) ∧
    mem.loadInt (sp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 n0.toInt)) := by
  exact ⟨h.1 0 (by decide), h.1 1 (by decide), h.1 2 (by decide), h.1 3 (by decide),
    h.1 4 (by decide), h.1 5 (by decide), h.1 6 (by decide), h.1 7 (by decide), h.2.1⟩

private theorem reduce_frame_slot (mem : DataMem) (mp sp : BitVec 64)
    (m : Sqr8xWords) (n0 : BitVec 64) (h : reduceFrame mem mp sp m n0) (j : Nat) (hj : j < 8) :
    (mem.loadInt (sp + reduceCount j * 8 + 48) 8).isSome = true ∧
    readWindowDisjoint mp (sp + reduceCount j * 8 + 48) 64 ∧
    readWindowDisjoint (sp + 40) (sp + reduceCount j * 8 + 48) 8 := by
  have he : sp + reduceCount j * 8 + 48 = sp + BitVec.ofNat 64 (112 - 8 * j) := by
    simp only [reduceCount]
    have hn : 112 - 8 * j = (8 - j) * 8 + 48 := by omega
    rw [hn, BitVec.ofNat_add, BitVec.ofNat_mul]
    simp only [BitVec.add_assoc]
    rfl
  rw [he]
  exact h.2.2 j hj

/-- Eight cancellation iterations; the initial counter is set by the original
reduction entry code. -/
def sqr8x_reduce_prog : Program := parse("reduce_start:\nmovl $8,%ecx\n.L8x_reduce:") ++
  sqr8x_reduce_iteration ++ parse("decl %ecx\njnz .L8x_reduce")

private theorem reduce_view : Program.view sqr8x_reduce_prog =
    ([], [("reduce_start", parse("movl $8,%ecx")),
      (".L8x_reduce", sqr8x_reduce_iteration ++ parse("decl %ecx\njnz .L8x_reduce"))]) := by decide

private abbrev reduceInvariant (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64)
    (s : MachineData) : Prop :=
  let j := reduceIndex (s.regs.get64 .rcx)
  let r := sqr8xReducePrefix d m n0 j
  j < 8 ∧ s.regs.get64 .rcx = reduceCount j ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi ∧
  s.zmms = d.zmms ∧ s.regs.get64 .rax = m.w0 ∧
  s.regs.get64 .rbx = r.coefficient ∧ s.regs.get64 .r8 = r.words.w0 ∧ s.regs.get64 .r9 = r.words.w1 ∧ s.regs.get64 .r10 = r.words.w2 ∧ s.regs.get64 .r11 = r.words.w3 ∧ s.regs.get64 .r12 = r.words.w4 ∧ s.regs.get64 .r13 = r.words.w5 ∧ s.regs.get64 .r14 = r.words.w6 ∧ s.regs.get64 .r15 = r.words.w7 ∧ s.dmem = r.memory

private abbrev reduceTable (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64) :
    Label → MachineData → Prop
  | "reduce_start", s => s = d
  | ".L8x_reduce", s => reduceInvariant d m n0 s
  | _, _ => False

private abbrev reduceVar : Label → MachineData → Nat
  | "reduce_start", _ => 9
  | ".L8x_reduce", s => (s.regs.get64 .rcx).toNat
  | _, _ => 0

private theorem reduce_counter_address (sp : BitVec 64) (j : Nat) (hj : j < 8) :
    sp + reduceCount j * 8 + 48 = sp + BitVec.ofNat 64 (112 - 8 * j) := by
  simp only [reduceCount]
  have hn : 112 - 8 * j = (8 - j) * 8 + 48 := by omega
  rw [hn, BitVec.ofNat_add, BitVec.ofNat_mul]
  simp only [BitVec.add_assoc]
  rfl

@[local grind norm] private theorem reduce_index_initial : reduceIndex 8 = 0 := rfl
@[local grind norm] private theorem reduce_count_initial : reduceCount 0 = 8 := rfl
@[local grind norm] private theorem reduce_count_done : reduceCount 8 = 0 := rfl
@[local grind norm] private theorem Sqr8xReduceState.words_mk (w q m) :
    (Sqr8xReduceState.mk w q m).words = w := rfl
@[local grind norm] private theorem Sqr8xReduceState.coefficient_mk (w q m) :
    (Sqr8xReduceState.mk w q m).coefficient = q := rfl
@[local grind norm] private theorem Sqr8xReduceState.memory_mk (w q m) :
    (Sqr8xReduceState.mk w q m).memory = m := rfl

attribute [local sym_simp] Option.map_none Option.map_some
attribute [local grind norm] Option.map_none Option.map_some
private theorem reduce_counter_next (j : Nat) (hj : j < 8) :
    reduceIndex (((reduceCount j).setWidth 32 - 1).zeroExtend 64) = j + 1 ∧
    (((reduceCount j).setWidth 32 - 1) = 0 ↔ j + 1 = 8) := by
  have h := reduce_counter_step j hj
  have hf := reduce_counter_facts (j + 1) (by omega)
  refine ⟨by rw [h.1]; exact hf.2.1, ?_⟩
  rw [← h.2.1]
  constructor
  · intro hzero
    rw [hzero]
    rfl
  · intro hzero
    apply BitVec.eq_of_toNat_eq
    simpa using hzero

private theorem reduce_prefix_step_fields (d : MachineData) (m : Sqr8xWords)
    (n0 : BitVec 64) (k : Nat) :
    (sqr8xReducePrefix d m n0 (k + 1)).words =
      sqr8xReduceResult (sqr8xReducePrefix d m n0 k).coefficient m (sqr8xReducePrefix d m n0 k).words ∧
    (sqr8xReducePrefix d m n0 (k + 1)).coefficient =
      (sqr8xReduceResult (sqr8xReducePrefix d m n0 k).coefficient m (sqr8xReducePrefix d m n0 k).words).w0 * n0 ∧
    (sqr8xReducePrefix d m n0 (k + 1)).memory =
      (sqr8xReducePrefix d m n0 k).memory.storeInt (d.regs.get64 .rsp + BitVec.ofNat 64 (112 - 8 * k))
        8 (sqr8xReducePrefix d m n0 k).coefficient.toIntOpaque := ⟨rfl, rfl, rfl⟩

private theorem reduce_iteration_prefix (d s : MachineData) (m : Sqr8xWords)
    (n0 : BitVec 64) (k : Nat)
    (hq : s.regs.get64 .rbx = (sqr8xReducePrefix d m n0 k).coefficient)
    (h0 : s.regs.get64 .r8 = (sqr8xReducePrefix d m n0 k).words.w0)
    (h1 : s.regs.get64 .r9 = (sqr8xReducePrefix d m n0 k).words.w1)
    (h2 : s.regs.get64 .r10 = (sqr8xReducePrefix d m n0 k).words.w2)
    (h3 : s.regs.get64 .r11 = (sqr8xReducePrefix d m n0 k).words.w3)
    (h4 : s.regs.get64 .r12 = (sqr8xReducePrefix d m n0 k).words.w4)
    (h5 : s.regs.get64 .r13 = (sqr8xReducePrefix d m n0 k).words.w5)
    (h6 : s.regs.get64 .r14 = (sqr8xReducePrefix d m n0 k).words.w6)
    (h7 : s.regs.get64 .r15 = (sqr8xReducePrefix d m n0 k).words.w7)
    : reductionResult s m = (sqr8xReducePrefix d m n0 (k + 1)).words ∧
      (reductionResult s m).w0 * n0 = (sqr8xReducePrefix d m n0 (k + 1)).coefficient := by
  have hw : reductionWords s = (sqr8xReducePrefix d m n0 k).words := by
    dsimp only [reductionWords]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have hf := reduce_prefix_step_fields d m n0 k
  simp only [reductionResult, hq, hw]
  exact ⟨hf.1.symm, hf.2.1.symm⟩

attribute [local irreducible] sqr8xReducePrefix sqr8xReduceResult reduceCount reduceIndex reduceFrame
attribute [local sym_simp] BitVec.zero_add CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  CondCode.interp_nz StatusFlags.zf_from_result
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
attribute [local grind =] reduce_prefix_zero reduce_counter_address
local grind_pattern reduce_counter_facts => reduceCount j
local grind_pattern reduce_counter_step => (reduceCount j).setWidth 32 - 1
local grind_pattern reduce_counter_next => (reduceCount j).setWidth 32 - 1
local grind_pattern reduce_frame_loads => reduceFrame mem mp sp m n0
local grind_pattern reduce_iteration_prefix => reductionResult s m, sqr8xReducePrefix d m n0 k
local grind_pattern reduce_prefix_step_fields => sqr8xReducePrefix d m n0 k, reduceCount k
local grind_pattern reduce_prefix_frame => sqr8xReducePrefix d m n0 k,
  reduceFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) m n0
local grind_pattern reduce_prefix_cancel => sqr8xReducePrefix d m n0 k
local grind_pattern reduce_frame_slot => reduceFrame mem mp sp m n0, reduceCount j

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr8x_reduce_prog)]
local instance : CodeEnv := ⟨layout sqr8x_reduce_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The complete eight-step low-word cancellation loop, including coefficient
storage, against its arithmetic fold. -/
theorem sqr8x_reduce_prog_correct (d : MachineData) (m : Sqr8xWords) (n0 : BitVec 64)
    (h_rax : d.regs.get64 .rax = m.w0)
    (h_q : d.regs.get64 .rbx = d.regs.get64 .r8 * n0)
    (h_inverse : m.w0 * n0 + 1 = 0)
    (h_mem : reduceFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) m n0) :
    ⦃ fun s => s = d ⦄ sqr8x_reduce_prog ⦃ fun _ s =>
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.zmms = d.zmms ∧ s.regs.get64 .rax = m.w0 ∧ s.regs.get64 .rcx = 0 ∧
      s.regs.get64 .rbx = (sqr8xReducePrefix d m n0 8).coefficient ∧
      s.regs.get64 .r8 = (sqr8xReducePrefix d m n0 8).words.w0
      ∧ s.regs.get64 .r9 = (sqr8xReducePrefix d m n0 8).words.w1
      ∧ s.regs.get64 .r10 = (sqr8xReducePrefix d m n0 8).words.w2
      ∧ s.regs.get64 .r11 = (sqr8xReducePrefix d m n0 8).words.w3
      ∧ s.regs.get64 .r12 = (sqr8xReducePrefix d m n0 8).words.w4
      ∧ s.regs.get64 .r13 = (sqr8xReducePrefix d m n0 8).words.w5
      ∧ s.regs.get64 .r14 = (sqr8xReducePrefix d m n0 8).words.w6
      ∧ s.regs.get64 .r15 = (sqr8xReducePrefix d m n0 8).words.w7 ∧
      s.dmem = (sqr8xReducePrefix d m n0 8).memory ⦄ := by
  apply MachineWP.cfg (reduceTable d m n0) reduceVar
  cfg_cases [reduce_view]
  · vcgen simplifying_assumptions with finish (splits := 0)
  · vcgen [sqr8x_reduce_iteration_correct (m := m) (n0 := n0)] simplifying_assumptions with
      finish (ematch := 12) (splits := 0) (hom := false) (canonHeartbeats := 5)
end

end Sqr8xReduceLoop

section Sqr4xDiagonal

/-- A word addition with an incoming carry bit, specified over natural numbers. -/
def sqr4xAdc (a b : BitVec 64) (carry : Bool) : BitVec 64 × Bool :=
  let z := a.toNat + b.toNat + carry.toNat
  (BitVec.ofNat 64 z, decide (2 ^ 64 ≤ z))

private theorem sqr4xAdc_eq (a b : BitVec 64) (carry : Bool) :
    sqr4xAdc a b carry =
      (a + b + BitVec.ofNat 64 carry.toNat,
        (a + b + BitVec.ofNat 64 carry.toNat).toNat !=
          (a.toNat : Int) + b.toNat + carry.toNat) := by
  have hz : a.toNat + b.toNat + carry.toNat < 2 * 2 ^ 64 := by
    have := a.isLt
    have := b.isLt
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hword : BitVec.ofNat 64 (a.toNat + b.toNat + carry.toNat) =
      a + b + BitVec.ofNat 64 carry.toNat := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [sqr4xAdc, hword, Prod.mk.injEq, true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, bne_iff_ne]
  rw [← hword, BitVec.toNat_ofNat]
  omega

/-- Two doubled cross-product limbs plus one diagonal square. The shift carry
and addition carry remain separate, as in the two chains in the assembly.
The addition carry is saved as a word mask (zero or minus one). -/
structure Sqr4xDiagonalResult where
  lo : BitVec 64
  hi : BitVec 64
  shiftCarry : BitVec 64
  addCarry : BitVec 64

def sqr4xDiagonalResult (x t0 t1 : BitVec 64) (shiftCarry : BitVec 64) (addCarry : BitVec 64) :
    Sqr4xDiagonalResult :=
  let lo := BitVec.ofNat 64 (2 * t0.toNat + shiftCarry.toNat)
  let hi := BitVec.ofNat 64 (2 * t1.toNat + t0.toNat / 2 ^ 63)
  let p := (x * x, mulHi x x)
  let a := sqr4xAdc p.1 lo (addCarry != 0)
  let b := sqr4xAdc p.2 hi a.2
  ⟨a.1, b.1, BitVec.ofNat 64 (t1.toNat / 2 ^ 63), -(BitVec.ofNat 64 b.2.toNat)⟩

private theorem diagonal_double_low (t c : BitVec 64) :
    BitVec.ofNat 64 (2 * t.toNat + c.toNat) = c + t * 2 := by
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat]
  grind

private theorem diagonal_double_high (a b : BitVec 64) :
    BitVec.ofNat 64 (2 * b.toNat + a.toNat / 2 ^ 63) =
      (b * 2) ||| (a.ushiftRight 63) := by
  have hor : (b * 2) ||| (a.ushiftRight 63) = b * 2 + a.ushiftRight 63 := by
    have hc : (a.ushiftRight 63).toNat < 2 := BitVec.toNat_ushiftRight_lt a 63 (by decide)
    have hb : (b * 2).toNat = 2 * (b.toNat % 2 ^ 63) := by
      simp only [BitVec.toNat_mul]
      change (b.toNat * 2) % 2 ^ 64 = 2 * (b.toNat % 2 ^ 63)
      omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_add, hb,
      ← Nat.two_pow_add_eq_or_of_lt (i := 1) hc]
    have := Nat.mod_lt b.toNat (by decide : 0 < 2 ^ 63)
    omega
  rw [hor]
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat]
  rw [BitVec.mul_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := a.isLt
  omega

private theorem diagonal_shift_carry (t : BitVec 64) :
    BitVec.ofNat 64 (t.toNat / 2 ^ 63) = t.ushiftRight 63 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.ushiftRight, BitVec.toNat_ofNatLT,
    Nat.shiftRight_eq_div_pow]
  have := t.isLt
  omega

private abbrev diagonalWordAdc (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  let v := a + b + BitVec.ofNat 64 c.toNat
  (v, (v.toNat : Int) != (a.toNat : Int) + b.toNat + c.toNat)

private theorem sqr4xDiagonalResult_eq (x t0 t1 sc : BitVec 64) (ac : BitVec 64) :
    sqr4xDiagonalResult x t0 t1 sc ac =
      let lo := sc + t0 * 2
      let hi := t1 * 2 ||| t0.ushiftRight 63
      let a := diagonalWordAdc (x * x) lo (ac != 0)
      let b := diagonalWordAdc (mulHi x x) hi a.2
      ⟨a.1, b.1, t1.ushiftRight 63, -(BitVec.ofNat 64 b.2.toNat)⟩ := by
  simp only [sqr4xDiagonalResult, diagonal_double_low, diagonal_double_high, sqr4xAdc_eq, diagonal_shift_carry]

section

private abbrev shiftLaneResult (d : MachineData) :=
  sqr4xDiagonalResult (d.regs.get64 .rax) (d.regs.get64 .r10) (d.regs.get64 .r11)
    (d.regs.get64 .r14) (d.regs.get64 .r15)

attribute [local grind norm] sqr4xDiagonalResult_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub
  Option.map_none Option.map_some
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
@[local grind norm] private theorem Sqr4xDiagonalResult.lo_mk (lo hi shiftCarry addCarry) :
    (Sqr4xDiagonalResult.mk lo hi shiftCarry addCarry).lo = lo := rfl
@[local grind norm] private theorem Sqr4xDiagonalResult.hi_mk (lo hi shiftCarry addCarry) :
    (Sqr4xDiagonalResult.mk lo hi shiftCarry addCarry).hi = hi := rfl
@[local grind norm] private theorem Sqr4xDiagonalResult.shiftCarry_mk (lo hi shiftCarry addCarry) :
    (Sqr4xDiagonalResult.mk lo hi shiftCarry addCarry).shiftCarry = shiftCarry := rfl
@[local grind norm] private theorem Sqr4xDiagonalResult.addCarry_mk (lo hi shiftCarry addCarry) :
    (Sqr4xDiagonalResult.mk lo hi shiftCarry addCarry).addCarry = addCarry := rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr4x_shift_lane0_correct [CodeEnv] (d : MachineData) (t2 t3 x1 : Int)
    (hc : d.regs.get64 .rcx = 0)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + (-16#64)) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + (-8#64)) 8 = some t3)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + (-8#64)) 8 = some x1)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + (-32#64)) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + (-24#64)) 8).isSome = true)
    : ⦃ fun s => s = d ⦄ sqr4x_shift_lane0 ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 0 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x1 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t2 ∧
      s.regs.get64 .r11 = BitVec.ofInt 64 t3 ∧
      s.regs.get64 .r14 = (shiftLaneResult d).shiftCarry ∧
      s.regs.get64 .r15 = (shiftLaneResult d).addCarry ∧
      s.regs.get64 .rbx = (shiftLaneResult d).shiftCarry + BitVec.ofInt 64 t2 * 2 ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi + (-32#64)) 8
        (shiftLaneResult d).lo.toIntOpaque).storeInt (d.regs.get64 .rdi + (-24#64)) 8
          (shiftLaneResult d).hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_lane0] simplifying_assumptions with finish (splits := 0) (hom := false) (canonHeartbeats := 5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr4x_shift_lane1_correct [CodeEnv] (d : MachineData) (t2 t3 x1 : Int)
    (hc : d.regs.get64 .rcx = 0)
    (hl : d.regs.get64 .rbx = d.regs.get64 .r14 + d.regs.get64 .r10 * 2)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + 0) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + 8) 8 = some t3)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 0) 8 = some x1)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + (-16#64)) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + (-8#64)) 8).isSome = true)
    : ⦃ fun s => s = d ⦄ sqr4x_shift_lane1 ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 0 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x1 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t2 ∧
      s.regs.get64 .r11 = BitVec.ofInt 64 t3 ∧
      s.regs.get64 .r14 = (shiftLaneResult d).shiftCarry ∧
      s.regs.get64 .r15 = (shiftLaneResult d).addCarry ∧
      s.regs.get64 .r12 = (shiftLaneResult d).shiftCarry + BitVec.ofInt 64 t2 * 2 ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi + (-16#64)) 8
        (shiftLaneResult d).lo.toIntOpaque).storeInt (d.regs.get64 .rdi + (-8#64)) 8
          (shiftLaneResult d).hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_lane1] simplifying_assumptions with finish (splits := 0) (hom := false) (canonHeartbeats := 5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr4x_shift_lane2_correct [CodeEnv] (d : MachineData) (t2 t3 x1 : Int)
    (hc : d.regs.get64 .rcx = 0)
    (hl : d.regs.get64 .r12 = d.regs.get64 .r14 + d.regs.get64 .r10 * 2)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + 16) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + 24) 8 = some t3)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 8) 8 = some x1)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + 0) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + 8) 8).isSome = true)
    : ⦃ fun s => s = d ⦄ sqr4x_shift_lane2 ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 0 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x1 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t2 ∧
      s.regs.get64 .r11 = BitVec.ofInt 64 t3 ∧
      s.regs.get64 .r14 = (shiftLaneResult d).shiftCarry ∧
      s.regs.get64 .r15 = (shiftLaneResult d).addCarry ∧
      s.regs.get64 .rbx = (shiftLaneResult d).shiftCarry + BitVec.ofInt 64 t2 * 2 ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi + 0) 8
        (shiftLaneResult d).lo.toIntOpaque).storeInt (d.regs.get64 .rdi + 8) 8
          (shiftLaneResult d).hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_lane2] simplifying_assumptions with finish (splits := 0) (hom := false) (canonHeartbeats := 5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr4x_shift_lane3_correct [CodeEnv] (d : MachineData) (t2 t3 x1 : Int)
    (hc : d.regs.get64 .rcx = 0)
    (hl : d.regs.get64 .rbx = d.regs.get64 .r14 + d.regs.get64 .r10 * 2)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + 32) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + 40) 8 = some t3)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 16) 8 = some x1)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + 16) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + 24) 8).isSome = true)
    : ⦃ fun s => s = d ⦄ sqr4x_shift_lane3 ⦃ fun _ s =>
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 0 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x1 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t2 ∧
      s.regs.get64 .r11 = BitVec.ofInt 64 t3 ∧
      s.regs.get64 .r14 = (shiftLaneResult d).shiftCarry ∧
      s.regs.get64 .r15 = (shiftLaneResult d).addCarry ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rdi + 16) 8
        (shiftLaneResult d).lo.toIntOpaque).storeInt (d.regs.get64 .rdi + 24) 8
          (shiftLaneResult d).hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_lane3] simplifying_assumptions with finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end

private theorem load_after_word_store (m : DataMem) (a b : BitVec 64) (v : Int)
    (hlo : 8 ≤ (b - a).toNat) (hhi : (b - a).toNat ≤ 2 ^ 64 - 8) :
    (m.storeInt a 8 v).loadInt b 8 = m.loadInt b 8 := by
  apply load_after_disjoint_store
  intro i hi j hj he
  have h : b - a = BitVec.ofNat 64 j - BitVec.ofNat 64 i := by grind
  rw [h] at hlo hhi
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at hlo hhi
  omega

private def shiftWindowsDisjoint (a b : BitVec 64) : Prop :=
  ∀ i < 32, ∀ j < 64, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j

private theorem shift_input_load_after_store (m : DataMem) (a b addr : BitVec 64) (v : Int)
    (i : Nat) (hi : i + 8 ≤ 32) (haddr : (addr - b).toNat + 8 ≤ 64)
    (hd : shiftWindowsDisjoint a b) :
    (m.storeInt addr 8 v).loadInt (a + BitVec.ofNat 64 i) 8 =
      m.loadInt (a + BitVec.ofNat 64 i) 8 := by
  apply load_after_disjoint_store
  intro j hj k hk
  have h := hd (i + j) (by omega) ((addr - b).toNat + k) (by omega)
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  grind only

private theorem shift_input_loads_after_store (m : DataMem) (a b addr : BitVec 64) (v : Int)
    (haddr : (addr - b).toNat + 8 ≤ 64) (hd : shiftWindowsDisjoint a b) :
    (m.storeInt addr 8 v).loadInt a 8 = m.loadInt a 8 ∧
    (m.storeInt addr 8 v).loadInt (a + 8) 8 = m.loadInt (a + 8) 8 ∧
    (m.storeInt addr 8 v).loadInt (a + 16) 8 = m.loadInt (a + 16) 8 ∧
    (m.storeInt addr 8 v).loadInt (a + 24) 8 = m.loadInt (a + 24) 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.add_zero] using shift_input_load_after_store m a b addr v 0 (by decide) haddr hd
  · exact shift_input_load_after_store m a b addr v 8 (by decide) haddr hd
  · exact shift_input_load_after_store m a b addr v 16 (by decide) haddr hd
  · exact shift_input_load_after_store m a b addr v 24 (by decide) haddr hd

private theorem load_after_two_word_stores (m : DataMem) (a b c : BitVec 64) (v w : Int)
    (ha : 8 ≤ (c - a).toNat) (ha' : (c - a).toNat ≤ 2 ^ 64 - 8)
    (hb : 8 ≤ (c - b).toNat) (hb' : (c - b).toNat ≤ 2 ^ 64 - 8) :
    ((m.storeInt a 8 v).storeInt b 8 w).loadInt c 8 = m.loadInt c 8 := by
  rw [load_after_word_store _ b c w hb hb', load_after_word_store m a c v ha ha']

private theorem shift_input_loads_after_two_stores (m : DataMem)
    (a b addr0 addr1 : BitVec 64) (v w : Int)
    (h0 : (addr0 - b).toNat + 8 ≤ 64) (h1 : (addr1 - b).toNat + 8 ≤ 64)
    (hd : shiftWindowsDisjoint a b) :
    ((m.storeInt addr0 8 v).storeInt addr1 8 w).loadInt a 8 = m.loadInt a 8 ∧
    ((m.storeInt addr0 8 v).storeInt addr1 8 w).loadInt (a + 8) 8 = m.loadInt (a + 8) 8 ∧
    ((m.storeInt addr0 8 v).storeInt addr1 8 w).loadInt (a + 16) 8 = m.loadInt (a + 16) 8 ∧
    ((m.storeInt addr0 8 v).storeInt addr1 8 w).loadInt (a + 24) 8 = m.loadInt (a + 24) 8 := by
  have hprev := shift_input_loads_after_store m a b addr0 v h0 hd
  have hnext := shift_input_loads_after_store (m.storeInt addr0 8 v) a b addr1 w h1 hd
  grind only

private def shiftFrameDisjoint (a b : BitVec 64) : Prop :=
  shiftWindowsDisjoint (a + (-8#64)) (b + (-32#64))

private theorem sub_offsets (a b c : BitVec 64) : (a + b) - (a + c) = b - c := by grind
private theorem sub_offset (a b : BitVec 64) : (a + b) - a = b := by grind

private theorem shift_lane0_loads (mem : DataMem) (a b : BitVec 64) (v w : Int)
    (hd : shiftFrameDisjoint a b) :
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (a + (-8#64)) 8 = mem.loadInt (a + (-8#64)) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (a + 0) 8 = mem.loadInt (a + 0) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (a + 8) 8 = mem.loadInt (a + 8) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (a + 16) 8 = mem.loadInt (a + 16) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + (-16#64)) 8 = mem.loadInt (b + (-16#64)) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + (-8#64)) 8 = mem.loadInt (b + (-8#64)) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 0) 8 = mem.loadInt (b + 0) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 8) 8 = mem.loadInt (b + 8) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 16) 8 = mem.loadInt (b + 16) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 24) 8 = mem.loadInt (b + 24) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 32) 8 = mem.loadInt (b + 32) 8 ∧
    ((mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w).loadInt (b + 40) 8 = mem.loadInt (b + 40) 8 := by
  have hi := shift_input_loads_after_two_stores mem (a + (-8#64)) (b + (-32#64))
    (b + (-32#64)) (b + (-24#64)) v w
    (by simp only [sub_offsets]; decide) (by simp only [sub_offsets]; decide) hd
  simp only [BitVec.add_assoc] at hi
  refine ⟨hi.1, ?_, ?_, ?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩⟩⟩⟩
  · simpa using hi.2.1
  · simpa using hi.2.2.1
  · simpa using hi.2.2.2
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide

private theorem shift_lane1_loads (mem : DataMem) (a b : BitVec 64) (v w : Int)
    (hd : shiftFrameDisjoint a b) :
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (a + (-8#64)) 8 = mem.loadInt (a + (-8#64)) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (a + 0) 8 = mem.loadInt (a + 0) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (a + 8) 8 = mem.loadInt (a + 8) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (a + 16) 8 = mem.loadInt (a + 16) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 0) 8 = mem.loadInt (b + 0) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 8) 8 = mem.loadInt (b + 8) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 16) 8 = mem.loadInt (b + 16) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 24) 8 = mem.loadInt (b + 24) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 32) 8 = mem.loadInt (b + 32) 8 ∧
    ((mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w).loadInt (b + 40) 8 = mem.loadInt (b + 40) 8 := by
  have hi := shift_input_loads_after_two_stores mem (a + (-8#64)) (b + (-32#64))
    (b + (-16#64)) (b + (-8#64)) v w
    (by simp only [sub_offsets]; decide) (by simp only [sub_offsets]; decide) hd
  simp only [BitVec.add_assoc] at hi
  refine ⟨hi.1, ?_, ?_, ?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩⟩
  · simpa using hi.2.1
  · simpa using hi.2.2.1
  · simpa using hi.2.2.2
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide

private theorem shift_lane2_loads (mem : DataMem) (a b : BitVec 64) (v w : Int)
    (hd : shiftFrameDisjoint a b) :
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (a + (-8#64)) 8 = mem.loadInt (a + (-8#64)) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (a + 0) 8 = mem.loadInt (a + 0) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (a + 8) 8 = mem.loadInt (a + 8) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (a + 16) 8 = mem.loadInt (a + 16) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (b + 16) 8 = mem.loadInt (b + 16) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (b + 24) 8 = mem.loadInt (b + 24) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (b + 32) 8 = mem.loadInt (b + 32) 8 ∧
    ((mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w).loadInt (b + 40) 8 = mem.loadInt (b + 40) 8 := by
  have hi := shift_input_loads_after_two_stores mem (a + (-8#64)) (b + (-32#64))
    (b + 0) (b + 8) v w
    (by simp only [sub_offsets]; decide) (by simp only [sub_offsets]; decide) hd
  simp only [BitVec.add_assoc] at hi
  refine ⟨hi.1, ?_, ?_, ?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩
  · simpa using hi.2.1
  · simpa using hi.2.2.1
  · simpa using hi.2.2.2
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
  · apply load_after_two_word_stores <;> simp only [sub_offsets] <;> decide
/-- The eight stored words and two carries after four diagonal squares. -/
structure Sqr4xShiftResult where
  words : Sqr8xWords
  shiftCarry : BitVec 64
  addCarry : BitVec 64

def sqr4xShiftResult (x0 x1 x2 x3 : BitVec 64) (t : Sqr8xWords)
    (shiftCarry : BitVec 64) (addCarry : BitVec 64) : Sqr4xShiftResult :=
  let p0 := sqr4xDiagonalResult x0 t.w0 t.w1 shiftCarry addCarry
  let p1 := sqr4xDiagonalResult x1 t.w2 t.w3 p0.shiftCarry p0.addCarry
  let p2 := sqr4xDiagonalResult x2 t.w4 t.w5 p1.shiftCarry p1.addCarry
  let p3 := sqr4xDiagonalResult x3 t.w6 t.w7 p2.shiftCarry p2.addCarry
  ⟨⟨p0.lo, p0.hi, p1.lo, p1.hi, p2.lo, p2.hi, p3.lo, p3.hi⟩, p3.shiftCarry, p3.addCarry⟩

private abbrev shiftResult (d : MachineData) (x1 x2 x3 t2 t3 t4 t5 t6 t7 : Int)
    (sc : BitVec 64) (ac : BitVec 64) : Sqr4xShiftResult :=
  sqr4xShiftResult (d.regs.get64 .rax) (BitVec.ofInt 64 x1)
    (BitVec.ofInt 64 x2) (BitVec.ofInt 64 x3)
    ⟨d.regs.get64 .r10, d.regs.get64 .r11, BitVec.ofInt 64 t2, BitVec.ofInt 64 t3,
      BitVec.ofInt 64 t4, BitVec.ofInt 64 t5, BitVec.ofInt 64 t6, BitVec.ofInt 64 t7⟩ sc ac

attribute [local irreducible] shiftWindowsDisjoint shiftFrameDisjoint sqr4xDiagonalResult
attribute [local grind unfold] sqr4xShiftResult
attribute [local grind norm]
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub
  Option.map_none Option.map_some
local grind_pattern shift_lane0_loads =>
  (mem.storeInt (b + (-32#64)) 8 v).storeInt (b + (-24#64)) 8 w, shiftFrameDisjoint a b
local grind_pattern shift_lane1_loads =>
  (mem.storeInt (b + (-16#64)) 8 v).storeInt (b + (-8#64)) 8 w, shiftFrameDisjoint a b
local grind_pattern shift_lane2_loads =>
  (mem.storeInt (b + 0) 8 v).storeInt (b + 8) 8 w, shiftFrameDisjoint a b
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

@[local grind norm] private theorem Sqr4xShiftResult.words_mk (words shiftCarry addCarry) :
    (Sqr4xShiftResult.mk words shiftCarry addCarry).words = words := rfl
@[local grind norm] private theorem Sqr4xShiftResult.shiftCarry_mk (words shiftCarry addCarry) :
    (Sqr4xShiftResult.mk words shiftCarry addCarry).shiftCarry = shiftCarry := rfl
@[local grind norm] private theorem Sqr4xShiftResult.addCarry_mk (words shiftCarry addCarry) :
    (Sqr4xShiftResult.mk words shiftCarry addCarry).addCarry = addCarry := rfl
attribute [local grind norm]
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- The four-square body of the doubling-and-diagonal loop, including its
prefetches for the following iteration. -/
theorem sqr4x_shift_iteration_correct [CodeEnv] (d : MachineData)
    (x1 x2 x3 x4 t2 t3 t4 t5 t6 t7 t8 t9 : Int) (sc : BitVec 64) (ac : BitVec 64)
    (h_rcx : d.regs.get64 .rcx = 0)
    (h_sc : d.regs.get64 .r14 = sc)
    (h_ac : d.regs.get64 .r15 = ac)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + (-8#64)) 8 = some x1)
    (h_x2 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 0) 8 = some x2)
    (h_x3 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 8) 8 = some x3)
    (h_x4 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 16) 8 = some x4)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + (-16#64)) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + (-8#64)) 8 = some t3)
    (h_t4 : d.dmem.loadInt (d.regs.get64 .rdi + 0) 8 = some t4)
    (h_t5 : d.dmem.loadInt (d.regs.get64 .rdi + 8) 8 = some t5)
    (h_t6 : d.dmem.loadInt (d.regs.get64 .rdi + 16) 8 = some t6)
    (h_t7 : d.dmem.loadInt (d.regs.get64 .rdi + 24) 8 = some t7)
    (h_t8 : d.dmem.loadInt (d.regs.get64 .rdi + 32) 8 = some t8)
    (h_t9 : d.dmem.loadInt (d.regs.get64 .rdi + 40) 8 = some t9)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + (-32#64)) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + (-24#64)) 8).isSome = true)
    (hd : shiftFrameDisjoint (d.regs.get64 .rsi + d.regs.get64 .rbp) (d.regs.get64 .rdi)) :
    ⦃ fun s => s = d ⦄ sqr4x_shift_iteration ⦃ fun _ s =>
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rcx = 0 ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi + 64 ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x4 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t8 ∧
      s.regs.get64 .r11 = BitVec.ofInt 64 t9 ∧
      s.regs.get64 .r14 = (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).shiftCarry ∧
      s.regs.get64 .r15 = (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).addCarry ∧
      s.zmms = d.zmms ∧
      s.dmem =
      ((((((((d.dmem.storeInt (d.regs.get64 .rdi + (-32#64)) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w0.toIntOpaque).storeInt (d.regs.get64 .rdi + (-24#64)) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w1.toIntOpaque).storeInt (d.regs.get64 .rdi + (-16#64)) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w2.toIntOpaque).storeInt (d.regs.get64 .rdi + (-8#64)) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w3.toIntOpaque).storeInt (d.regs.get64 .rdi + 0) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w4.toIntOpaque).storeInt (d.regs.get64 .rdi + 8) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w5.toIntOpaque).storeInt (d.regs.get64 .rdi + 16) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w6.toIntOpaque).storeInt (d.regs.get64 .rdi + 24) 8
        (shiftResult d x1 x2 x3 t2 t3 t4 t5 t6 t7 sc ac).words.w7.toIntOpaque) ⦄ := by
  vcgen [sqr4x_shift_iteration,
      sqr4x_shift_lane0_correct (t2 := t2) (t3 := t3) (x1 := x1),
      sqr4x_shift_lane1_correct (t2 := t4) (t3 := t5) (x1 := x2),
      sqr4x_shift_lane2_correct (t2 := t6) (t3 := t7) (x1 := x3),
      sqr4x_shift_lane3_correct (t2 := t8) (t3 := t9) (x1 := x4)] simplifying_assumptions with
    finish (ematch := 12) (splits := 0) (hom := false) (canonHeartbeats := 5)

section

/-- Two consecutive diagonal squares, sharing the two saved carry words. -/
def sqr4xDiagonalPair (x0 x1 t0 t1 t2 t3 sc ac : BitVec 64) :
    Sqr4xDiagonalResult × Sqr4xDiagonalResult :=
  let p := sqr4xDiagonalResult x0 t0 t1 sc ac
  (p, sqr4xDiagonalResult x1 t2 t3 p.shiftCarry p.addCarry)

private abbrev shiftTailResult (d : MachineData) (x1 t2 t3 : Int) :=
  sqr4xDiagonalPair (d.regs.get64 .rax) (BitVec.ofInt 64 x1)
    (d.regs.get64 .r10) (d.regs.get64 .r11) (BitVec.ofInt 64 t2) (BitVec.ofInt 64 t3)
    (d.regs.get64 .r14) (d.regs.get64 .r15)

attribute [local grind unfold] sqr4xDiagonalPair
attribute [local grind norm] sqr4xDiagonalResult_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr4xDiagonalResult.lo_mk Sqr4xDiagonalResult.hi_mk
  Sqr4xDiagonalResult.shiftCarry_mk Sqr4xDiagonalResult.addCarry_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub
  Option.map_none Option.map_some
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
/-- The final two diagonal squares, followed by restoration of the modulus
pointer from the vector register saved by the caller. -/
theorem sqr4x_shift_tail_correct [CodeEnv] (d : MachineData) (x1 t2 t3 : Int)
    (h_rcx : d.regs.get64 .rcx = 0)
    (h_x : d.dmem.loadInt (d.regs.get64 .rsi + (-8#64)) 8 = some x1)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + (-16#64)) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + (-8#64)) 8 = some t3)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rdi + (-32#64)) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (d.regs.get64 .rdi + (-24#64)) 8).isSome = true) :
    ⦃ fun s => s = d ⦄ sqr4x_shift_tail ⦃ fun _ s =>
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rbp = (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 ∧
      s.zmms = d.zmms ∧
      s.dmem = (((d.dmem.storeInt (d.regs.get64 .rdi + (-32#64)) 8
        (shiftTailResult d x1 t2 t3).1.lo.toIntOpaque).storeInt (d.regs.get64 .rdi + (-24#64)) 8
        (shiftTailResult d x1 t2 t3).1.hi.toIntOpaque).storeInt (d.regs.get64 .rdi + (-16#64)) 8
        (shiftTailResult d x1 t2 t3).2.lo.toIntOpaque).storeInt (d.regs.get64 .rdi + (-8#64)) 8
        (shiftTailResult d x1 t2 t3).2.hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_tail] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end

end Sqr4xDiagonal

section Sqr4xShiftLoop

/-- Store the eight limbs of an unrolled arithmetic result in ascending order. -/
private abbrev storeSqr8xWords (mem : DataMem) (addr : BitVec 64) (w : Sqr8xWords) : DataMem :=
  ((((((((mem.storeInt (addr + 0) 8 w.w0.toIntOpaque).storeInt (addr + 8) 8 w.w1.toIntOpaque).storeInt (addr + 16) 8 w.w2.toIntOpaque).storeInt (addr + 24) 8 w.w3.toIntOpaque).storeInt (addr + 32) 8 w.w4.toIntOpaque).storeInt (addr + 40) 8 w.w5.toIntOpaque).storeInt (addr + 48) 8 w.w6.toIntOpaque).storeInt (addr + 56) 8 w.w7.toIntOpaque)

structure Sqr4xShiftState where
  shiftCarry : BitVec 64
  addCarry : BitVec 64
  memory : DataMem

/-- Fold the four-square arithmetic over the original input and cross-product
limbs. The two saved carry words connect consecutive groups. -/
def sqr4xShiftFold (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xShiftState) : Nat → Sqr4xShiftState
  | 0 => initial
  | k + 1 =>
    let s := sqr4xShiftFold x t base initial k
    let r := sqr4xShiftResult (x.getD (4 * k) 0) (x.getD (4 * k + 1) 0)
      (x.getD (4 * k + 2) 0) (x.getD (4 * k + 3) 0)
      ⟨t.getD (8 * k) 0, t.getD (8 * k + 1) 0, t.getD (8 * k + 2) 0,
        t.getD (8 * k + 3) 0, t.getD (8 * k + 4) 0, t.getD (8 * k + 5) 0,
        t.getD (8 * k + 6) 0, t.getD (8 * k + 7) 0⟩ s.shiftCarry s.addCarry
    ⟨r.shiftCarry, r.addCarry, storeSqr8xWords s.memory (base + BitVec.ofNat 64 (64 * k)) r.words⟩

def sqr4xShiftPrefix (d : MachineData) (x t : List (BitVec 64)) (k : Nat) : Sqr4xShiftState :=
  sqr4xShiftFold x t (d.regs.get64 .rdi + (-32#64))
    ⟨d.regs.get64 .r14, d.regs.get64 .r15, d.dmem⟩ k

private theorem shift_fold_load (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xShiftState) (k : Nat) (addr : BitVec 64)
    (hd : ∀ i < 8, ∀ j < 64 * k,
      addr + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    (sqr4xShiftFold x t base initial k).memory.loadInt addr 8 = initial.memory.loadInt addr 8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [sqr4xShiftFold, storeSqr8xWords]
    have hdis (j : Nat) (hj : j < 8) :
        ∀ i < 8, ∀ l < 8, addr + BitVec.ofNat 64 i ≠
          base + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 l := by
      intro i hi l hl
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        hd i hi (64 * k + (8 * j + l)) (by omega)
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 56) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 7 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 48) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 6 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 40) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 5 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 32) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 4 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 24) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 3 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 16) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 2 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 8) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 1 (by decide))]
    rw [load_after_disjoint_store _ (base + BitVec.ofNat 64 (64 * k) + 0) addr _
      (by simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using hdis 0 (by decide))]
    exact ih (by intro i hi j hj; exact hd i hi j (by omega))

private def shiftOffset (n k : Nat) : BitVec 64 := innerOffset (2 * n) (2 * k)
private def shiftIndex (n : Nat) (v : BitVec 64) : Nat := innerIndex (2 * n) v / 2

private theorem shift_counter_facts (n k : Nat) (hk : k ≤ n) (hb : 64 * n + 64 < 2 ^ 63) :
    (shiftOffset n k = 0 ↔ k = n) ∧
    (k < n → (shiftOffset n k).toNat = 2 ^ 64 - 32 * (n - k) ∧
      shiftIndex n (shiftOffset n k) = k) := by
  have h := offset_facts (2 * n) (2 * k) (by omega) (by omega)
  dsimp only [shiftOffset, shiftIndex]
  grind only

private theorem shift_counter_step (n k : Nat) :
    32 + shiftOffset n k = shiftOffset n (k + 1) := by
  rw [BitVec.add_comm]
  simpa only [shiftOffset, Nat.mul_add, Nat.mul_one] using offset_step_two (2 * n) (2 * k)

private theorem shift_counter_initial (n : Nat) (hn : 0 < n) (hb : 64 * n + 64 < 2 ^ 63) :
    shiftIndex n (0#64 - BitVec.ofNat 64 (32 * n)) = 0 := by
  have h := offset_initial_index (2 * n) (by omega) (by omega)
  simpa only [shiftIndex, show 16 * (2 * n) = 32 * n by omega, Nat.zero_div] using congrArg (· / 2) h

private theorem shift_counter_continue (n k : Nat) (hk : k < n) (hb : 64 * n + 64 < 2 ^ 63)
    (hne : (32 + shiftOffset n k).toNat ≠ 0) :
    k + 1 < n ∧ shiftIndex n (32 + shiftOffset n k) = k + 1 ∧
    2 ^ 64 - (32 + shiftOffset n k).toNat < 2 ^ 64 - (shiftOffset n k).toNat := by
  have h := offset_continue_two (2 * n) (2 * k) (by omega) (by omega)
    (show (innerOffset (2 * n) (2 * k) + 32).toNat ≠ 0 by simpa only [BitVec.add_comm, shiftOffset] using hne)
  dsimp only [shiftIndex, shiftOffset]
  rw [BitVec.add_comm 32]
  grind only

private def shiftFrame (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) : Prop :=
  d.dmem =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
    (d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64))) ⋆
    (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At (d.regs.get64 .rdi + (-32#64))) ⋆ R)

private theorem shift_prefix_input (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 64 * n + 64 < 2 ^ 63)
    (hxl : x.length = 4 * n + 2) (htl : t.length = 8 * n + 4)
    (hm : shiftFrame d n x t R) (k j : Nat) (hk : k ≤ n) (hj : j < x.length) :
    (sqr4xShiftPrefix d x t k).memory.loadInt
      (d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toInt)) := by
  rw [sqr4xShiftPrefix, shift_fold_load]
  · exact load_limb hm (by omega) j hj
  · intro i hi l hl
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      sep_At_ne hm (8 * j + i) (by rw [length_flatMap_limbs]; omega)
        l (by rw [length_flatMap_limbs]; omega)

private theorem shift_prefix_output (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 64 * n + 64 < 2 ^ 63)
    (htl : t.length = 8 * n + 4) (hm : shiftFrame d n x t R)
    (k j : Nat) (hkj : 8 * k ≤ j) (hj : j < t.length) :
    (sqr4xShiftPrefix d x t k).memory.loadInt
      (d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (t.getD j 0).toInt)) := by
  rw [sqr4xShiftPrefix, shift_fold_load]
  · exact load_tp_limb j hm (by omega) hj rfl
  · simpa only [show 16 * (4 * k) = 64 * k by omega] using
      word_before_disjoint (d.regs.get64 .rdi + (-32#64)) (4 * k) j (by omega) (by omega)

private theorem shift_prefix_disjoint (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hxl : x.length = 4 * n + 2) (htl : t.length = 8 * n + 4)
    (hm : shiftFrame d n x t R) (k : Nat) (hk : k < n) :
    shiftFrameDisjoint (d.regs.get64 .rsi + shiftOffset n k)
      (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k)) := by
  intro i hi j hj
  have h := sep_At_ne hm (32 * k + (8 + i)) (by rw [length_flatMap_limbs]; omega)
    (64 * k + j) (by rw [length_flatMap_limbs]; omega)
  simp only [BitVec.ofNat_add, shiftOffset, innerOffset] at h ⊢
  have hmul (v : Nat) : 16 * (2 * v) = 32 * v := by omega
  simp only [hmul]
  grind only

private theorem shift_iteration_inputs (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 64 * n + 64 < 2 ^ 63)
    (hxl : x.length = 4 * n + 2) (htl : t.length = 8 * n + 4)
    (hm : shiftFrame d n x t R) (k : Nat) (hk : k < n) :
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rsi + shiftOffset n k + (-8#64)) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (4 * k + 1) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rsi + shiftOffset n k + 0) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (4 * k + 2) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rsi + shiftOffset n k + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (4 * k + 3) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rsi + shiftOffset n k + 16) 8 = some (Int.ofBytes (Int.toBytes 8 (x.getD (4 * k + 4) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-16#64)) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 2) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-8#64)) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 3) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 0) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 4) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 8) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 5) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 16) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 6) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 24) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 7) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 32) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 8) 0).toInt)) ∧
    (sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 40) 8 = some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * k + 9) 0).toInt)) ∧
    ((sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-32#64)) 8).isSome = true ∧
    ((sqr4xShiftPrefix d x t k).memory.loadInt (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-24#64)) 8).isSome = true ∧
    shiftFrameDisjoint (d.regs.get64 .rsi + shiftOffset n k) (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k)) := by
  have hmul (v : Nat) : 16 * (2 * v) = 32 * v := by omega
  have hmul4 : 8 * (4 * k) = 32 * k := by omega
  have hmul8 : 8 * (8 * k) = 64 * k := by omega
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · have ha : d.regs.get64 .rsi + shiftOffset n k + (-8#64) = d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) + BitVec.ofNat 64 (8 * (4 * k + 1)) := by
      simp only [shiftOffset, innerOffset, hmul, Nat.mul_add, BitVec.ofNat_add, hmul4]
      grind
    rw [ha]
    exact shift_prefix_input d n x t R hb hxl htl hm k (4 * k + 1) (by omega) (by omega)
  · have ha : d.regs.get64 .rsi + shiftOffset n k + 0 = d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) + BitVec.ofNat 64 (8 * (4 * k + 2)) := by
      simp only [shiftOffset, innerOffset, hmul, Nat.mul_add, BitVec.ofNat_add, hmul4]
      grind
    rw [ha]
    exact shift_prefix_input d n x t R hb hxl htl hm k (4 * k + 2) (by omega) (by omega)
  · have ha : d.regs.get64 .rsi + shiftOffset n k + 8 = d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) + BitVec.ofNat 64 (8 * (4 * k + 3)) := by
      simp only [shiftOffset, innerOffset, hmul, Nat.mul_add, BitVec.ofNat_add, hmul4]
      grind
    rw [ha]
    exact shift_prefix_input d n x t R hb hxl htl hm k (4 * k + 3) (by omega) (by omega)
  · have ha : d.regs.get64 .rsi + shiftOffset n k + 16 = d.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) + BitVec.ofNat 64 (8 * (4 * k + 4)) := by
      simp only [shiftOffset, innerOffset, hmul, Nat.mul_add, BitVec.ofNat_add, hmul4]
      grind
    rw [ha]
    exact shift_prefix_input d n x t R hb hxl htl hm k (4 * k + 4) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-16#64) = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 2)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 2) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-8#64) = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 3)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 3) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 0 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 4)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 4) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 8 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 5)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 5) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 16 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 6)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 6) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 24 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 7)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 7) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 32 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 8)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 8) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + 40 = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 9)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    exact shift_prefix_output d n x t R hb htl hm k (8 * k + 9) (by omega) (by omega)
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-32#64) = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 0)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    rw [shift_prefix_output d n x t R hb htl hm k (8 * k + 0) (by omega) (by omega)]
    rfl
  · have ha : d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-24#64) = d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * k + 1)) := by
      simp only [Nat.mul_add, hmul8, BitVec.ofNat_add]
      grind
    rw [ha]
    rw [shift_prefix_output d n x t R hb htl hm k (8 * k + 1) (by omega) (by omega)]
    rfl
  · exact shift_prefix_disjoint d n x t R hxl htl hm k hk

private abbrev shiftBlockResult (d : MachineData) (x t : List (BitVec 64)) (k : Nat) :=
  sqr4xShiftResult (x.getD (4 * k) 0) (x.getD (4 * k + 1) 0)
    (x.getD (4 * k + 2) 0) (x.getD (4 * k + 3) 0)
    ⟨t.getD (8 * k) 0, t.getD (8 * k + 1) 0, t.getD (8 * k + 2) 0,
      t.getD (8 * k + 3) 0, t.getD (8 * k + 4) 0, t.getD (8 * k + 5) 0,
      t.getD (8 * k + 6) 0, t.getD (8 * k + 7) 0⟩
    (sqr4xShiftPrefix d x t k).shiftCarry (sqr4xShiftPrefix d x t k).addCarry

private theorem shift_prefix_zero (d : MachineData) (x t : List (BitVec 64)) :
    (sqr4xShiftPrefix d x t 0).shiftCarry = d.regs.get64 .r14 ∧
    (sqr4xShiftPrefix d x t 0).addCarry = d.regs.get64 .r15 ∧
    (sqr4xShiftPrefix d x t 0).memory = d.dmem := ⟨rfl, rfl, rfl⟩

private abbrev storeShiftWords (mem : DataMem) (center : BitVec 64) (w : Sqr8xWords) :=
  ((((((((mem.storeInt (center + (-32#64)) 8 w.w0.toIntOpaque).storeInt (center + (-24#64)) 8 w.w1.toIntOpaque).storeInt (center + (-16#64)) 8 w.w2.toIntOpaque).storeInt (center + (-8#64)) 8 w.w3.toIntOpaque).storeInt (center + 0) 8 w.w4.toIntOpaque).storeInt (center + 8) 8 w.w5.toIntOpaque).storeInt (center + 16) 8 w.w6.toIntOpaque).storeInt (center + 24) 8 w.w7.toIntOpaque)

private theorem store_shift_words (mem : DataMem) (center : BitVec 64) (w : Sqr8xWords) :
    storeSqr8xWords mem (center + (-32#64)) w = storeShiftWords mem center w := by
  simp only [storeSqr8xWords, storeShiftWords, BitVec.add_assoc]
  rfl

@[local grind =] private theorem shift_pointer_step (b : BitVec 64) (k : Nat) :
    b + BitVec.ofNat 64 (64 * k) + 64 = b + BitVec.ofNat 64 (64 * (k + 1)) := by
  simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
  grind

private theorem shift_prefix_step (d : MachineData) (x t : List (BitVec 64)) (k : Nat) :
    (sqr4xShiftPrefix d x t (k + 1)).shiftCarry = (shiftBlockResult d x t k).shiftCarry ∧
    (sqr4xShiftPrefix d x t (k + 1)).addCarry = (shiftBlockResult d x t k).addCarry ∧
    (sqr4xShiftPrefix d x t (k + 1)).memory =
      storeShiftWords (sqr4xShiftPrefix d x t k).memory
        (d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k)) (shiftBlockResult d x t k).words := by
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [sqr4xShiftPrefix, sqr4xShiftFold]
  rw [show d.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (64 * k) =
    d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) + (-32#64) from by grind, store_shift_words]
  rfl

private abbrev shiftInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  let k := shiftIndex n (s.regs.get64 .rbp)
  k < n ∧ s.regs.get64 .rbp = shiftOffset n k ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 (64 * k) ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧ s.zmms = d.zmms ∧ s.regs.get64 .rcx = 0 ∧
  s.regs.get64 .rax = x.getD (4 * k) 0 ∧
  s.regs.get64 .r10 = t.getD (8 * k) 0 ∧ s.regs.get64 .r11 = t.getD (8 * k + 1) 0 ∧
  s.regs.get64 .r14 = (sqr4xShiftPrefix d x t k).shiftCarry ∧
  s.regs.get64 .r15 = (sqr4xShiftPrefix d x t k).addCarry ∧ s.dmem = (sqr4xShiftPrefix d x t k).memory

section

attribute [local irreducible] shiftOffset shiftIndex shiftFrame sqr4xShiftPrefix sqr4xShiftResult
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
attribute [local grind =] ofInt_limb
local grind_pattern shift_prefix_step => sqr4xShiftPrefix d x t (k + 1)
local grind_pattern shift_prefix_zero => sqr4xShiftPrefix d x t 0
local grind_pattern shift_iteration_inputs => sqr4xShiftPrefix d x t k, shiftFrame d n x t R

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem shift_iteration_from_prefix [CodeEnv] (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (R : DataMem → Prop) (hb : 64 * n + 64 < 2 ^ 63)
    (hxl : x.length = 4 * n + 2) (htl : t.length = 8 * n + 4)
    (hm : shiftFrame d n x t R) (s : MachineData) (hs : shiftInvariant d n x t s) :
    ⦃ fun s' => s' = s ⦄ sqr4x_shift_iteration ⦃ fun _ s' =>
      s'.regs.get64 .rbp = s.regs.get64 .rbp ∧
      s'.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 (64 * (shiftIndex n (s.regs.get64 .rbp) + 1)) ∧
      s'.regs.get64 .rsi = d.regs.get64 .rsi ∧ s'.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s'.regs.get64 .r9 = d.regs.get64 .r9 ∧ s'.zmms = d.zmms ∧ s'.regs.get64 .rcx = 0 ∧
      s'.regs.get64 .rax = x.getD (4 * (shiftIndex n (s.regs.get64 .rbp) + 1)) 0 ∧
      s'.regs.get64 .r10 = t.getD (8 * (shiftIndex n (s.regs.get64 .rbp) + 1)) 0 ∧
      s'.regs.get64 .r11 = t.getD (8 * (shiftIndex n (s.regs.get64 .rbp) + 1) + 1) 0 ∧
      s'.regs.get64 .r14 = (sqr4xShiftPrefix d x t (shiftIndex n (s.regs.get64 .rbp) + 1)).shiftCarry ∧
      s'.regs.get64 .r15 = (sqr4xShiftPrefix d x t (shiftIndex n (s.regs.get64 .rbp) + 1)).addCarry ∧
      s'.dmem = (sqr4xShiftPrefix d x t (shiftIndex n (s.regs.get64 .rbp) + 1)).memory ⦄ := by
  vcgen [sqr4x_shift_iteration_correct
      (x1 := Int.ofBytes (Int.toBytes 8 (x.getD (4 * (shiftIndex n (s.regs.get64 .rbp)) + 1) 0).toInt))
      (x2 := Int.ofBytes (Int.toBytes 8 (x.getD (4 * (shiftIndex n (s.regs.get64 .rbp)) + 2) 0).toInt))
      (x3 := Int.ofBytes (Int.toBytes 8 (x.getD (4 * (shiftIndex n (s.regs.get64 .rbp)) + 3) 0).toInt))
      (x4 := Int.ofBytes (Int.toBytes 8 (x.getD (4 * (shiftIndex n (s.regs.get64 .rbp)) + 4) 0).toInt))
      (t2 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 2) 0).toInt))
      (t3 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 3) 0).toInt))
      (t4 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 4) 0).toInt))
      (t5 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 5) 0).toInt))
      (t6 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 6) 0).toInt))
      (t7 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 7) 0).toInt))
      (t8 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 8) 0).toInt))
      (t9 := Int.ofBytes (Int.toBytes 8 (t.getD (8 * (shiftIndex n (s.regs.get64 .rbp)) + 9) 0).toInt))
      (sc := (sqr4xShiftPrefix d x t (shiftIndex n (s.regs.get64 .rbp))).shiftCarry)
      (ac := (sqr4xShiftPrefix d x t (shiftIndex n (s.regs.get64 .rbp))).addCarry)] simplifying_assumptions with
    finish (ematch := 12) (splits := 0) (hom := false) (canonHeartbeats := 5)

end

attribute [local irreducible] shiftOffset shiftIndex shiftFrame sqr4xShiftPrefix
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
local grind_pattern shift_prefix_zero => sqr4xShiftPrefix d x t 0

/-- The repeated four-square phase, starting at the jump to its loop header. -/
def sqr4x_shift_prog : Program := parse("shift_start:\njmp .Lsqr4x_shift_n_add\n.Lsqr4x_shift_n_add:") ++
  sqr4x_shift_iteration ++ parse("addq $32,%rbp\njnz .Lsqr4x_shift_n_add")

private theorem shift_view : Program.view sqr4x_shift_prog =
    ([], [("shift_start", parse("jmp .Lsqr4x_shift_n_add")),
      (".Lsqr4x_shift_n_add", sqr4x_shift_iteration ++ parse("addq $32,%rbp\njnz .Lsqr4x_shift_n_add"))]) := by decide

private abbrev shiftTable (d : MachineData) (n : Nat) (x t : List (BitVec 64)) :
    Label → MachineData → Prop
  | "shift_start", s => s = d
  | ".Lsqr4x_shift_n_add", s => shiftInvariant d n x t s
  | _, _ => False

private abbrev shiftVar : Label → MachineData → Nat
  | "shift_start", _ => 2 ^ 64
  | ".Lsqr4x_shift_n_add", s => 2 ^ 64 - (s.regs.get64 .rbp).toNat
  | _, _ => 0

private theorem shift_counter_zero (n : Nat) :
    shiftOffset n 0 = 0#64 - BitVec.ofNat 64 (32 * n) := by
  simp only [shiftOffset, innerOffset, Nat.mul_zero, show 16 * (2 * n) = 32 * n by omega]

attribute [local sym_simp] Option.map_none Option.map_some CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind norm] Option.map_none Option.map_some CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind =] shift_counter_zero shift_counter_step shift_counter_initial
local grind_pattern shift_counter_facts => shiftOffset n k
local grind_pattern shift_counter_continue => 32 + shiftOffset n k

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr4x_shift_prog)]
local instance : CodeEnv := ⟨layout sqr4x_shift_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Functional correctness of the repeated diagonal phase. Two prefetched input
limbs and four cross-product limbs remain for the separately verified tail. -/
theorem sqr4x_shift_prog_correct (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (h_pos : 0 < n) (h_bound : 64 * n + 64 < 2 ^ 63)
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 (32 * n))
    (h_rcx : d.regs.get64 .rcx = 0)
    (h_rax : d.regs.get64 .rax = x.getD 0 0)
    (h_r10 : d.regs.get64 .r10 = t.getD 0 0) (h_r11 : d.regs.get64 .r11 = t.getD 1 0)
    (h_x_len : x.length = 4 * n + 2) (h_t_len : t.length = 8 * n + 4)
    (R : DataMem → Prop) (h_mem : shiftFrame d n x t R) :
    ⦃ fun s => s = d ⦄ sqr4x_shift_prog ⦃ fun _ s =>
      s.regs.get64 .rbp = 0 ∧ s.regs.get64 .rcx = 0 ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 (64 * n) ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .r9 = d.regs.get64 .r9 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = x.getD (4 * n) 0 ∧ s.regs.get64 .r10 = t.getD (8 * n) 0 ∧
      s.regs.get64 .r11 = t.getD (8 * n + 1) 0 ∧
      s.regs.get64 .r14 = (sqr4xShiftPrefix d x t n).shiftCarry ∧
      s.regs.get64 .r15 = (sqr4xShiftPrefix d x t n).addCarry ∧
      s.dmem = (sqr4xShiftPrefix d x t n).memory ⦄ := by
  apply MachineWP.cfg (shiftTable d n x t) shiftVar
  cfg_cases [shift_view]
  · vcgen simplifying_assumptions with finish (ematch := 12) (splits := 16)
  · vcgen [shift_iteration_from_prefix d n x t R h_bound h_x_len h_t_len h_mem]
      simplifying_assumptions with finish (ematch := 12) (splits := 16) (hom := true) (canonHeartbeats := 5)
end

end Sqr4xShiftLoop

section Sqr4xShiftPreamble

private abbrev shiftPreambleResult (d : MachineData) (x0 x1 t1 t2 t3 : Int) :=
  sqr4xDiagonalPair (BitVec.ofInt 64 x0) (BitVec.ofInt 64 x1) 0 (BitVec.ofInt 64 t1)
    (BitVec.ofInt 64 t2) (BitVec.ofInt 64 t3) (d.regs.get64 .r14) (d.regs.get64 .r15)

private def shiftPreambleDisjoint (a sp : BitVec 64) : Prop := shiftFrameDisjoint a (sp + 88)

private theorem shift_preamble_loads (mem : DataMem) (a sp : BitVec 64) (v w : Int)
    (hd : shiftPreambleDisjoint a sp) :
    ((mem.storeInt (sp + 56) 8 v).storeInt (sp + 64) 8 w).loadInt (a + 0) 8 = mem.loadInt (a + 0) 8 ∧
    ((mem.storeInt (sp + 56) 8 v).storeInt (sp + 64) 8 w).loadInt (sp + 88) 8 = mem.loadInt (sp + 88) 8 ∧
    ((mem.storeInt (sp + 56) 8 v).storeInt (sp + 64) 8 w).loadInt (sp + 96) 8 = mem.loadInt (sp + 96) 8 := by
  have h := shift_lane0_loads mem a (sp + 88) v w hd
  simpa [BitVec.add_assoc] using And.intro h.2.1 (And.intro h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1)

attribute [local irreducible] shiftPreambleDisjoint
attribute [local grind unfold] sqr4xDiagonalPair
attribute [local grind norm] sqr4xDiagonalResult_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr4xDiagonalResult.lo_mk Sqr4xDiagonalResult.hi_mk
  Sqr4xDiagonalResult.shiftCarry_mk Sqr4xDiagonalResult.addCarry_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub Option.map_none Option.map_some
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern shift_preamble_loads =>
  (mem.storeInt (sp + 56) 8 v).storeInt (sp + 64) 8 w, shiftPreambleDisjoint a sp

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1400000 in
theorem sqr4x_shift_preamble_correct [CodeEnv] (d : MachineData) (x0 x1 x2 t1 t2 t3 t4 t5 : Int)
    (h_rcx : d.regs.get64 .rcx = 0)
    (h_x0 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + (-16#64)) 8 = some x0)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + (-8#64)) 8 = some x1)
    (h_x2 : d.dmem.loadInt (d.regs.get64 .rsi + d.regs.get64 .rbp + 0) 8 = some x2)
    (h_o0 : (d.dmem.loadInt (d.regs.get64 .rsp + 56) 8).isSome = true)
    (h_t1 : d.dmem.loadInt (d.regs.get64 .rsp + 64) 8 = some t1)
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rsp + 72) 8 = some t2)
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rsp + 80) 8 = some t3)
    (h_t4 : d.dmem.loadInt (d.regs.get64 .rsp + 88) 8 = some t4)
    (h_t5 : d.dmem.loadInt (d.regs.get64 .rsp + 96) 8 = some t5)
    (hd : shiftPreambleDisjoint (d.regs.get64 .rsi + d.regs.get64 .rbp) (d.regs.get64 .rsp)) :
    ⦃ fun s => s = d ⦄ sqr4x_shift_preamble ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_shift_n_add" ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rcx = 0 ∧
      s.zmms = d.zmms ∧ s.regs.get64 .rbp = d.regs.get64 .rbp + 16 ∧
      s.regs.get64 .rdi = d.regs.get64 .rsp + 120 ∧
      s.regs.get64 .rax = BitVec.ofInt 64 x2 ∧
      s.regs.get64 .r10 = BitVec.ofInt 64 t4 ∧ s.regs.get64 .r11 = BitVec.ofInt 64 t5 ∧
      s.regs.get64 .r14 = (shiftPreambleResult d x0 x1 t1 t2 t3).2.shiftCarry ∧
      s.regs.get64 .r15 = (shiftPreambleResult d x0 x1 t1 t2 t3).2.addCarry ∧
      s.dmem = (((d.dmem.storeInt (d.regs.get64 .rsp + 56) 8
        (shiftPreambleResult d x0 x1 t1 t2 t3).1.lo.toIntOpaque).storeInt (d.regs.get64 .rsp + 64) 8
        (shiftPreambleResult d x0 x1 t1 t2 t3).1.hi.toIntOpaque).storeInt (d.regs.get64 .rsp + 72) 8
        (shiftPreambleResult d x0 x1 t1 t2 t3).2.lo.toIntOpaque).storeInt (d.regs.get64 .rsp + 80) 8
        (shiftPreambleResult d x0 x1 t1 t2 t3).2.hi.toIntOpaque ⦄ := by
  vcgen [sqr4x_shift_preamble] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end Sqr4xShiftPreamble

section Sqr8xTailLoop

/-- Arithmetic reference for the tail's eight saved-coefficient products. -/
def sqr8xTailFold (m : Sqr8xWords) (coefficients : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr8xReduceState) : Nat → Sqr8xReduceState
  | 0 => initial
  | k + 1 =>
    let s := sqr8xTailFold m coefficients base initial k
    let low := (sqr4xMac m.w0 s.coefficient s.words.w0 0).1
    ⟨sqr8xReduceResult s.coefficient m s.words, coefficients.getD (k + 1) 0,
      s.memory.storeInt (base + BitVec.ofNat 64 (8 * k)) 8 low.toIntOpaque⟩

def sqr8xTailPrefix (d : MachineData) (m : Sqr8xWords)
    (coefficients : List (BitVec 64)) (k : Nat) : Sqr8xReduceState :=
  sqr8xTailFold m coefficients (d.regs.get64 .rdi)
    ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ k

private theorem tail_fold_subdom (m : Sqr8xWords) (q : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) :
    Mem.SubDom initial.memory (sqr8xTailFold m q base initial k).memory := by
  induction k with
  | zero => exact Mem.SubDom.refl _
  | succ k ih => exact ih.storeInt _ _ _

private theorem tail_fold_load (m : Sqr8xWords) (q : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) (addr : BitVec 64)
    (hd : ∀ j < k, ∀ u < 8, ∀ v < 8,
      addr + BitVec.ofNat 64 u ≠ base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 v) :
    (sqr8xTailFold m q base initial k).memory.loadInt addr 8 = initial.memory.loadInt addr 8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [sqr8xTailFold]
    rw [load_after_disjoint_store]
    · exact ih (by intro j hj; exact hd j (by omega))
    · exact hd k (by omega)

private def tailFrame (mem : DataMem) (mp sp out : BitVec 64)
    (m : Sqr8xWords) (q : List (BitVec 64)) : Prop :=
  (∀ i < 8, mem.loadInt (mp + BitVec.ofNat 64 (8 * i)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (m.get i).toInt))) ∧
  (∀ i < 8, mem.loadInt (sp + BitVec.ofNat 64 (104 - 8 * i)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (q.getD (i + 1) 0).toInt))) ∧
  ∀ j < 8,
    (mem.loadInt (out + BitVec.ofNat 64 (8 * j)) 8).isSome = true ∧
    readWindowDisjoint mp (out + BitVec.ofNat 64 (8 * j)) 64 ∧
    ∀ i < 8, readWindowDisjoint (sp + BitVec.ofNat 64 (104 - 8 * i))
      (out + BitVec.ofNat 64 (8 * j)) 8

private theorem tail_prefix_frame (d : MachineData) (m : Sqr8xWords) (q : List (BitVec 64))
    (hf : tailFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) (d.regs.get64 .rdi) m q)
    (k : Nat) (hk : k ≤ 8) :
    tailFrame (sqr8xTailPrefix d m q k).memory
      (d.regs.get64 .rbp) (d.regs.get64 .rsp) (d.regs.get64 .rdi) m q := by
  obtain ⟨hm, hq, hs⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [sqr8xTailPrefix, tail_fold_load]
    · exact hm i hi
    · intro j hj u hu v hv he
      have h := (hs j (by omega)).2.1 (8 * i + u) (by omega) v hv
      simp only [BitVec.ofNat_add, BitVec.add_assoc] at h
      exact h (by simpa only [BitVec.add_assoc] using he)
  · intro i hi
    rw [sqr8xTailPrefix, tail_fold_load]
    · exact hq i hi
    · intro j hj u hu v hv
      exact (hs j (by omega)).2.2 i hi u hu v hv
  · intro j hj
    refine ⟨?_, (hs j hj).2⟩
    exact Mem.SubDom.loadInt_isSome (tail_fold_subdom m q (d.regs.get64 .rdi)
      ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ k) (hs j hj).1

private theorem tail_frame_loads (mem : DataMem) (mp sp out : BitVec 64)
    (m : Sqr8xWords) (q : List (BitVec 64)) (h : tailFrame mem mp sp out m q) :
    mem.loadInt (mp + 0) 8 = some (Int.ofBytes (Int.toBytes 8 m.w0.toInt)) ∧
    mem.loadInt (mp + 8) 8 = some (Int.ofBytes (Int.toBytes 8 m.w1.toInt)) ∧
    mem.loadInt (mp + 16) 8 = some (Int.ofBytes (Int.toBytes 8 m.w2.toInt)) ∧
    mem.loadInt (mp + 24) 8 = some (Int.ofBytes (Int.toBytes 8 m.w3.toInt)) ∧
    mem.loadInt (mp + 32) 8 = some (Int.ofBytes (Int.toBytes 8 m.w4.toInt)) ∧
    mem.loadInt (mp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 m.w5.toInt)) ∧
    mem.loadInt (mp + 48) 8 = some (Int.ofBytes (Int.toBytes 8 m.w6.toInt)) ∧
    mem.loadInt (mp + 56) 8 = some (Int.ofBytes (Int.toBytes 8 m.w7.toInt)) := by
  exact ⟨h.1 0 (by decide), h.1 1 (by decide), h.1 2 (by decide), h.1 3 (by decide),
    h.1 4 (by decide), h.1 5 (by decide), h.1 6 (by decide), h.1 7 (by decide)⟩

private theorem tail_counter_address (sp : BitVec 64) (j : Nat) (hj : j < 8) :
    sp + reduceCount j * 8 + 40 = sp + BitVec.ofNat 64 (104 - 8 * j) := by
  simp only [reduceCount]
  have hn : 104 - 8 * j = (8 - j) * 8 + 40 := by omega
  rw [hn, BitVec.ofNat_add, BitVec.ofNat_mul]
  simp only [BitVec.add_assoc]
  rfl

private theorem tail_frame_slot (mem : DataMem) (mp sp out : BitVec 64)
    (m : Sqr8xWords) (q : List (BitVec 64)) (h : tailFrame mem mp sp out m q)
    (j : Nat) (hj : j < 8) :
    mem.loadInt (sp + reduceCount j * 8 + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 (q.getD (j + 1) 0).toInt)) ∧
    (mem.loadInt (out + BitVec.ofNat 64 (8 * j)) 8).isSome = true ∧
    readWindowDisjoint mp (out + BitVec.ofNat 64 (8 * j)) 64 ∧
    readWindowDisjoint (sp + reduceCount j * 8 + 40) (out + BitVec.ofNat 64 (8 * j)) 8 := by
  rw [tail_counter_address sp j hj]
  exact ⟨h.2.1 j hj, (h.2.2 j hj).1, (h.2.2 j hj).2.1, (h.2.2 j hj).2.2 j hj⟩

private theorem tail_prefix_zero (d : MachineData) (m : Sqr8xWords) (q : List (BitVec 64)) :
    sqr8xTailPrefix d m q 0 = ⟨reductionWords d, d.regs.get64 .rbx, d.dmem⟩ := rfl

private theorem tail_prefix_step_fields (d : MachineData) (m : Sqr8xWords)
    (q : List (BitVec 64)) (k : Nat) :
    (sqr8xTailPrefix d m q (k + 1)).words =
      sqr8xReduceResult (sqr8xTailPrefix d m q k).coefficient m (sqr8xTailPrefix d m q k).words ∧
    (sqr8xTailPrefix d m q (k + 1)).coefficient = q.getD (k + 1) 0 ∧
    (sqr8xTailPrefix d m q (k + 1)).memory =
      (sqr8xTailPrefix d m q k).memory.storeInt (d.regs.get64 .rdi + BitVec.ofNat 64 (8 * k))
        8 (sqr4xMac m.w0 (sqr8xTailPrefix d m q k).coefficient
          (sqr8xTailPrefix d m q k).words.w0 0).1.toIntOpaque := ⟨rfl, rfl, rfl⟩

private theorem tail_iteration_prefix (d s : MachineData) (m : Sqr8xWords)
    (q : List (BitVec 64)) (k : Nat)
    (hq : s.regs.get64 .rbx = (sqr8xTailPrefix d m q k).coefficient)
    (h0 : s.regs.get64 .r8 = (sqr8xTailPrefix d m q k).words.w0)
    (h1 : s.regs.get64 .r9 = (sqr8xTailPrefix d m q k).words.w1)
    (h2 : s.regs.get64 .r10 = (sqr8xTailPrefix d m q k).words.w2)
    (h3 : s.regs.get64 .r11 = (sqr8xTailPrefix d m q k).words.w3)
    (h4 : s.regs.get64 .r12 = (sqr8xTailPrefix d m q k).words.w4)
    (h5 : s.regs.get64 .r13 = (sqr8xTailPrefix d m q k).words.w5)
    (h6 : s.regs.get64 .r14 = (sqr8xTailPrefix d m q k).words.w6)
    (h7 : s.regs.get64 .r15 = (sqr8xTailPrefix d m q k).words.w7) :
    reductionResult s m = (sqr8xTailPrefix d m q (k + 1)).words := by
  have hw : reductionWords s = (sqr8xTailPrefix d m q k).words := by
    dsimp only [reductionWords]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [reductionResult, hq, hw]
  exact (tail_prefix_step_fields d m q k).1.symm

/-- Eight multiply-adds against one modulus block using the saved coefficients. -/
def sqr8x_tail_prog : Program := parse("tail_start:\nmovl $8,%ecx\n.L8x_tail:") ++
  sqr8x_tail_iteration ++ parse("decl %ecx\njnz .L8x_tail")

private theorem tail_view : Program.view sqr8x_tail_prog =
    ([], [("tail_start", parse("movl $8,%ecx")),
      (".L8x_tail", sqr8x_tail_iteration ++ parse("decl %ecx\njnz .L8x_tail"))]) := by decide

private abbrev tailInvariant (d : MachineData) (m : Sqr8xWords) (q : List (BitVec 64))
    (s : MachineData) : Prop :=
  let j := reduceIndex (s.regs.get64 .rcx)
  let r := sqr8xTailPrefix d m q j
  j < 8 ∧ s.regs.get64 .rcx = reduceCount j ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 (8 * j) ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧
  s.zmms = d.zmms ∧ s.regs.get64 .rax = m.w0 ∧
  s.regs.get64 .rbx = r.coefficient ∧ s.regs.get64 .r8 = r.words.w0 ∧ s.regs.get64 .r9 = r.words.w1 ∧ s.regs.get64 .r10 = r.words.w2 ∧ s.regs.get64 .r11 = r.words.w3 ∧ s.regs.get64 .r12 = r.words.w4 ∧ s.regs.get64 .r13 = r.words.w5 ∧ s.regs.get64 .r14 = r.words.w6 ∧ s.regs.get64 .r15 = r.words.w7 ∧ s.dmem = r.memory

private abbrev tailTable (d : MachineData) (m : Sqr8xWords) (q : List (BitVec 64)) :
    Label → MachineData → Prop
  | "tail_start", s => s = d
  | ".L8x_tail", s => tailInvariant d m q s
  | _, _ => False

private abbrev tailVar : Label → MachineData → Nat
  | "tail_start", _ => 9
  | ".L8x_tail", s => (s.regs.get64 .rcx).toNat
  | _, _ => 0

private theorem tail_pointer_step (b : BitVec 64) (k : Nat) :
    b + BitVec.ofNat 64 (8 * k) + 8 = b + BitVec.ofNat 64 (8 * (k + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

attribute [local irreducible] sqr8xTailPrefix sqr8xReduceResult reduceCount reduceIndex tailFrame
attribute [local sym_simp] BitVec.zero_add CondCode.interp_nz StatusFlags.zf_from_result Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  CondCode.interp_nz StatusFlags.zf_from_result Option.map_none Option.map_some
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
  Sqr8xReduceState.words_mk Sqr8xReduceState.coefficient_mk Sqr8xReduceState.memory_mk
  reduce_index_initial reduce_count_initial reduce_count_done
attribute [local grind =] tail_prefix_zero tail_pointer_step
local grind_pattern reduce_counter_facts => reduceCount j
local grind_pattern reduce_counter_step => (reduceCount j).setWidth 32 - 1
local grind_pattern reduce_counter_next => (reduceCount j).setWidth 32 - 1
local grind_pattern tail_frame_loads => tailFrame mem mp sp out m q
local grind_pattern tail_iteration_prefix => reductionResult s m, sqr8xTailPrefix d m q k
local grind_pattern tail_prefix_step_fields => sqr8xTailPrefix d m q k, reduceCount k
local grind_pattern tail_prefix_frame => sqr8xTailPrefix d m q k,
  tailFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) (d.regs.get64 .rdi) m q
local grind_pattern tail_frame_slot => tailFrame mem mp sp out m q, reduceCount j

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr8x_tail_prog)]
local instance : CodeEnv := ⟨layout sqr8x_tail_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- The eight-step tail loop stores all low words, advances the output pointer,
and preserves the saved carry mask for the following modulus block. -/
theorem sqr8x_tail_prog_correct (d : MachineData) (m : Sqr8xWords) (q : List (BitVec 64))
    (h_rax : d.regs.get64 .rax = m.w0)
    (h_mem : tailFrame d.dmem (d.regs.get64 .rbp) (d.regs.get64 .rsp) (d.regs.get64 .rdi) m q) :
    ⦃ fun s => s = d ⦄ sqr8x_tail_prog ⦃ fun _ s =>
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi + 64 ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.zmms = d.zmms ∧ s.regs.get64 .rax = m.w0 ∧ s.regs.get64 .rcx = 0 ∧
      s.regs.get64 .rbx = (sqr8xTailPrefix d m q 8).coefficient ∧
      s.regs.get64 .r8 = (sqr8xTailPrefix d m q 8).words.w0
      ∧ s.regs.get64 .r9 = (sqr8xTailPrefix d m q 8).words.w1
      ∧ s.regs.get64 .r10 = (sqr8xTailPrefix d m q 8).words.w2
      ∧ s.regs.get64 .r11 = (sqr8xTailPrefix d m q 8).words.w3
      ∧ s.regs.get64 .r12 = (sqr8xTailPrefix d m q 8).words.w4
      ∧ s.regs.get64 .r13 = (sqr8xTailPrefix d m q 8).words.w5
      ∧ s.regs.get64 .r14 = (sqr8xTailPrefix d m q 8).words.w6
      ∧ s.regs.get64 .r15 = (sqr8xTailPrefix d m q 8).words.w7 ∧
      s.dmem = (sqr8xTailPrefix d m q 8).memory ⦄ := by
  apply MachineWP.cfg (tailTable d m q) tailVar
  cfg_cases [tail_view]
  · vcgen simplifying_assumptions with finish (splits := 0)
  · vcgen [(fun s => sqr8x_tail_iteration_correct s m
      (q.getD (reduceIndex (s.regs.get64 .rcx) + 1) 0))]
      simplifying_assumptions with
      finish (ematch := 12) (splits := 16) (canonHeartbeats := 5)
end

end Sqr8xTailLoop

section Sqr4xFinalProducts

/-- The last six pair products, including the carries into the two high words.
Word zero is left untouched by this fragment. -/
def sqr4xFinalProducts (x0 x1 x2 x3 t1 t2 t3 : BitVec 64) : Sqr8xWords × BitVec 64 :=
  let p1 := sqr4xMac x1 x0 t1 0
  let p2 := sqr4xMac x2 x0 p1.2 t2
  let p3 := sqr4xMac x2 x1 t3 0
  let p4 := sqr4xMac x3 x0 p2.2 p3.1
  let p5 := sqr4xMac x3 x1 p3.2 p4.2
  let p6 := sqr4xMac x2 x3 p5.2 0
  (⟨0, p1.1, p2.1, p4.1, p5.1, p6.1, p6.2, 0⟩, p5.2)

private abbrev finalProducts (d : MachineData) (x0 x1 x2 x3 : Int) :=
  sqr4xFinalProducts (BitVec.ofInt 64 x0) (BitVec.ofInt 64 x1)
    (BitVec.ofInt 64 x2) (BitVec.ofInt 64 x3)
    (d.regs.get64 .r10) (d.regs.get64 .r13) (d.regs.get64 .r12)

private abbrev finalProductBase (d : MachineData) :=
  d.regs.get64 .rsp + d.regs.get64 .r9 * 2

private def finalProductDisjoint (input center : BitVec 64) : Prop :=
  ∀ j < 7, readWindowDisjoint (input + (-32#64))
    (center + BitVec.ofNat 64 (8 * j)) 32

private theorem final_product_load (mem : DataMem) (input center : BitVec 64)
    (j : Nat) (v : Int) (hd : finalProductDisjoint input center) (hj : j < 7) :
    (mem.storeInt (center + BitVec.ofNat 64 (8 * j)) 8 v).loadInt
      (input + (-8#64)) 8 = mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + BitVec.ofNat 64 (8 * j)) 8 v).loadInt
      (input + (-16#64)) 8 = mem.loadInt (input + (-16#64)) 8 := by
  have h1 := load_window_after_store mem (input + (-32#64))
    (center + BitVec.ofNat 64 (8 * j)) v 32 24 (by decide) (hd j hj)
  have h2 := load_window_after_store mem (input + (-32#64))
    (center + BitVec.ofNat 64 (8 * j)) v 32 16 (by decide) (hd j hj)
  simpa [BitVec.add_assoc] using And.intro h1 h2

private theorem final_product_load0 (mem : DataMem) (input center : BitVec 64) (v : Int)
    (hd : finalProductDisjoint input center) :
    (mem.storeInt (center + 0) 8 v).loadInt (input + (-8#64)) 8 =
      mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + 0) 8 v).loadInt (input + (-16#64)) 8 =
      mem.loadInt (input + (-16#64)) 8 := by
  simpa [BitVec.add_assoc] using final_product_load mem input center 0 v hd (by decide)

private theorem final_product_load1 (mem : DataMem) (input center : BitVec 64) (v : Int)
    (hd : finalProductDisjoint input center) :
    (mem.storeInt (center + 8) 8 v).loadInt (input + (-8#64)) 8 =
      mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + 8) 8 v).loadInt (input + (-16#64)) 8 =
      mem.loadInt (input + (-16#64)) 8 := by
  simpa [BitVec.add_assoc] using final_product_load mem input center 1 v hd (by decide)

private theorem final_product_load2 (mem : DataMem) (input center : BitVec 64) (v : Int)
    (hd : finalProductDisjoint input center) :
    (mem.storeInt (center + 16) 8 v).loadInt (input + (-8#64)) 8 =
      mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + 16) 8 v).loadInt (input + (-16#64)) 8 =
      mem.loadInt (input + (-16#64)) 8 := by
  simpa [BitVec.add_assoc] using final_product_load mem input center 2 v hd (by decide)

private theorem final_product_load3 (mem : DataMem) (input center : BitVec 64) (v : Int)
    (hd : finalProductDisjoint input center) :
    (mem.storeInt (center + 24) 8 v).loadInt (input + (-8#64)) 8 =
      mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + 24) 8 v).loadInt (input + (-16#64)) 8 =
      mem.loadInt (input + (-16#64)) 8 := by
  simpa [BitVec.add_assoc] using final_product_load mem input center 3 v hd (by decide)

private theorem final_product_load4 (mem : DataMem) (input center : BitVec 64) (v : Int)
    (hd : finalProductDisjoint input center) :
    (mem.storeInt (center + 32) 8 v).loadInt (input + (-8#64)) 8 =
      mem.loadInt (input + (-8#64)) 8 ∧
    (mem.storeInt (center + 32) 8 v).loadInt (input + (-16#64)) 8 =
      mem.loadInt (input + (-16#64)) 8 := by
  simpa [BitVec.add_assoc] using final_product_load mem input center 4 v hd (by decide)

attribute [local irreducible] finalProductDisjoint
attribute [local grind unfold] sqr4xFinalProducts
attribute [local grind norm] sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub BitVec.xor_self
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub Option.map_none Option.map_some
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern final_product_load0 => mem.storeInt (center + 0) 8 v, finalProductDisjoint input center
local grind_pattern final_product_load1 => mem.storeInt (center + 8) 8 v, finalProductDisjoint input center
local grind_pattern final_product_load2 => mem.storeInt (center + 16) 8 v, finalProductDisjoint input center
local grind_pattern final_product_load3 => mem.storeInt (center + 24) 8 v, finalProductDisjoint input center
local grind_pattern final_product_load4 => mem.storeInt (center + 32) 8 v, finalProductDisjoint input center

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1800000 in
theorem sqr4x_final_products_correct [CodeEnv] (d : MachineData) (x0 x1 x2 x3 : Int)
    (h_rbp : d.regs.get64 .rbp = 0)
    (h_x0 : d.dmem.loadInt (d.regs.get64 .rsi + (-32#64)) 8 = some x0)
    (h_x1 : d.dmem.loadInt (d.regs.get64 .rsi + (-24#64)) 8 = some x1)
    (h_x2 : d.dmem.loadInt (d.regs.get64 .rsi + (-16#64)) 8 = some x2)
    (h_x3 : d.dmem.loadInt (d.regs.get64 .rsi + (-8#64)) 8 = some x3)
    (h_o0 : (d.dmem.loadInt (finalProductBase d + 0) 8).isSome = true)
    (h_o1 : (d.dmem.loadInt (finalProductBase d + 8) 8).isSome = true)
    (h_o2 : (d.dmem.loadInt (finalProductBase d + 16) 8).isSome = true)
    (h_o3 : (d.dmem.loadInt (finalProductBase d + 24) 8).isSome = true)
    (h_o4 : (d.dmem.loadInt (finalProductBase d + 32) 8).isSome = true)
    (h_o5 : (d.dmem.loadInt (finalProductBase d + 40) 8).isSome = true)
    (h_o6 : (d.dmem.loadInt (finalProductBase d + 48) 8).isSome = true)
    (hd : finalProductDisjoint (d.regs.get64 .rsi) (finalProductBase d)) :
    ⦃ fun s => s = d ⦄ sqr4x_final_products ⦃ fun _ s =>
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rcx = d.regs.get64 .rcx ∧
      s.zmms = d.zmms ∧ s.regs.get64 .rbp = 16 - d.regs.get64 .r9 ∧
      s.regs.get64 .rdi = finalProductBase d + 24 ∧
      s.regs.get64 .r14 = 0 ∧ s.regs.get64 .r15 = 0 ∧
      s.dmem =
      ((((((((d.dmem.storeInt (finalProductBase d + 0) 8 (finalProducts d x0 x1 x2 x3).1.w1.toIntOpaque).storeInt (finalProductBase d + 8) 8 (finalProducts d x0 x1 x2 x3).1.w2.toIntOpaque).storeInt (finalProductBase d + 16) 8 (finalProducts d x0 x1 x2 x3).1.w3.toIntOpaque).storeInt (finalProductBase d + 24) 8 (finalProducts d x0 x1 x2 x3).1.w4.toIntOpaque).storeInt (finalProductBase d + 32) 8 (finalProducts d x0 x1 x2 x3).2.toIntOpaque).storeInt (finalProductBase d + 32) 8 (finalProducts d x0 x1 x2 x3).1.w5.toIntOpaque).storeInt (finalProductBase d + 40) 8 (finalProducts d x0 x1 x2 x3).1.w6.toIntOpaque).storeInt (finalProductBase d + 48) 8 (finalProducts d x0 x1 x2 x3).1.w7.toIntOpaque) ⦄ := by
  vcgen [sqr4x_final_products] simplifying_assumptions with
    finish (ematch := 16) (splits := 0) (hom := false) (canonHeartbeats := 5)

end Sqr4xFinalProducts

section Sqr8xReductionEntry

attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add BitVec.xor_self
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
attribute [local grind =] ofInt_limb
attribute [local irreducible] readWindowDisjoint
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern inverse_load_after_store => mem.storeInt b 8 v, readWindowDisjoint a b 8

/-- Save the modulus end and workspace end, then enter the reduction loop. -/
theorem sqr8x_reduction_setup_correct [CodeEnv] (d : MachineData)
    (h0 : (d.dmem.loadInt (d.regs.get64 .rsp + 8) 8).isSome = true)
    (h1 : (d.dmem.loadInt (d.regs.get64 .rsp + 16) 8).isSome = true) :
    ⦃ fun s => s = d ⦄ sqr8x_reduction_setup ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduction_loop" ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .r9 = -d.regs.get64 .r9 ∧ s.regs.get64 .rax = 0 ∧
      s.regs.get64 .rdx = d.regs.get64 .rsp + d.regs.get64 .r9 * 2 + 56 ∧
      s.regs.get64 .rdi = d.regs.get64 .rsp + d.regs.get64 .r9 + 56 ∧ s.zmms = d.zmms ∧
      s.dmem = (d.dmem.storeInt (d.regs.get64 .rsp + 8) 8
        (d.regs.get64 .r9 + d.regs.get64 .rbp).toIntOpaque).storeInt (d.regs.get64 .rsp + 16) 8
        (d.regs.get64 .rsp + d.regs.get64 .r9 * 2 + 56).toIntOpaque ⦄ := by
  vcgen [sqr8x_reduction_setup] simplifying_assumptions with finish (splits := 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Load the next eight-word accumulator and form its first cancellation
coefficient, preserving the carry from the previous reduction pass in memory. -/
theorem sqr8x_reduction_entry_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (m0 n0 : BitVec 64)
    (h_t0 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 0) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w0.toInt)))
    (h_t1 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w1.toInt)))
    (h_t2 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w2.toInt)))
    (h_t3 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 24) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w3.toInt)))
    (h_t4 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 32) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w4.toInt)))
    (h_t5 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w5.toInt)))
    (h_t6 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 48) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w6.toInt)))
    (h_t7 : d.dmem.loadInt (d.regs.get64 .rdi + d.regs.get64 .r9 + 56) 8 =
      some (Int.ofBytes (Int.toBytes 8 t.w7.toInt)))
    (h_mod : d.dmem.loadInt (d.regs.get64 .rbp + 0) 8 = some (Int.ofBytes (Int.toBytes 8 m0.toInt)))
    (h_inv : d.dmem.loadInt (d.regs.get64 .rsp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 n0.toInt)))
    (h_slot : (d.dmem.loadInt (d.regs.get64 .rdx) 8).isSome = true)
    (hmd : readWindowDisjoint (d.regs.get64 .rbp) (d.regs.get64 .rdx) 8)
    (hnd : readWindowDisjoint (d.regs.get64 .rsp + 40) (d.regs.get64 .rdx) 8) :
    ⦃ fun s => s = d ⦄ sqr8x_reduction_entry ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduce" ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.zmms = d.zmms ∧ s.regs.get64 .rdi = d.regs.get64 .rdi + d.regs.get64 .r9 + 64 ∧
      s.regs.get64 .rax = m0 ∧ s.regs.get64 .rbx = t.w0 * n0 ∧ s.regs.get64 .rcx = 8 ∧
      s.regs.get64 .r8 = t.w0 ∧
      s.regs.get64 .r9 = t.w1 ∧
      s.regs.get64 .r10 = t.w2 ∧
      s.regs.get64 .r11 = t.w3 ∧
      s.regs.get64 .r12 = t.w4 ∧
      s.regs.get64 .r13 = t.w5 ∧
      s.regs.get64 .r14 = t.w6 ∧
      s.regs.get64 .r15 = t.w7 ∧
      s.dmem = d.dmem.storeInt (d.regs.get64 .rdx) 8 (d.regs.get64 .rax).toIntOpaque ⦄ := by
  vcgen [sqr8x_reduction_entry] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end Sqr8xReductionEntry

section Sqr8xWordAddition

/-- Eight-word addition with a single carry chain, specified over naturals. -/
def sqr8xAddResult (a b : Sqr8xWords) (carry : Bool) : Sqr8xWords × Bool :=
  let p0 := sqr4xAdc b.w0 a.w0 carry
  let p1 := sqr4xAdc b.w1 a.w1 p0.2
  let p2 := sqr4xAdc b.w2 a.w2 p1.2
  let p3 := sqr4xAdc b.w3 a.w3 p2.2
  let p4 := sqr4xAdc b.w4 a.w4 p3.2
  let p5 := sqr4xAdc b.w5 a.w5 p4.2
  let p6 := sqr4xAdc b.w6 a.w6 p5.2
  let p7 := sqr4xAdc b.w7 a.w7 p6.2
  (⟨p0.1, p1.1, p2.1, p3.1, p4.1, p5.1, p6.1, p7.1⟩, p7.2)

private def wordsLoaded (mem : DataMem) (base : BitVec 64) (w : Sqr8xWords) : Prop :=
  ∀ i < 8, mem.loadInt (base + BitVec.ofNat 64 (8 * i)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (w.get i).toInt))

private theorem words_loaded_fields (mem : DataMem) (base : BitVec 64) (w : Sqr8xWords)
    (h : wordsLoaded mem base w) :
    mem.loadInt (base + 0) 8 = some (Int.ofBytes (Int.toBytes 8 w.w0.toInt)) ∧
    mem.loadInt (base + 8) 8 = some (Int.ofBytes (Int.toBytes 8 w.w1.toInt)) ∧
    mem.loadInt (base + 16) 8 = some (Int.ofBytes (Int.toBytes 8 w.w2.toInt)) ∧
    mem.loadInt (base + 24) 8 = some (Int.ofBytes (Int.toBytes 8 w.w3.toInt)) ∧
    mem.loadInt (base + 32) 8 = some (Int.ofBytes (Int.toBytes 8 w.w4.toInt)) ∧
    mem.loadInt (base + 40) 8 = some (Int.ofBytes (Int.toBytes 8 w.w5.toInt)) ∧
    mem.loadInt (base + 48) 8 = some (Int.ofBytes (Int.toBytes 8 w.w6.toInt)) ∧
    mem.loadInt (base + 56) 8 = some (Int.ofBytes (Int.toBytes 8 w.w7.toInt)) := by
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

attribute [local grind unfold] sqr8xAddResult
attribute [local grind norm] sqr4xAdc_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub BitVec.xor_self
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub Option.map_none Option.map_some
attribute [local grind =] ofInt_limb
attribute [local irreducible] wordsLoaded
local grind_pattern words_loaded_fields => wordsLoaded mem base w

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr8x_add_words_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (h : wordsLoaded d.dmem (d.regs.get64 .rdi) t) :
    ⦃ fun s => s = d ⦄ sqr8x_add_words ⦃ fun _ s =>
      s.regs.get64 .rax = d.regs.get64 .rax ∧
      s.regs.get64 .rbx = d.regs.get64 .rbx ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx ∧
      s.regs.get64 .rdx = d.regs.get64 .rdx ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .r8 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w0 ∧
      s.regs.get64 .r9 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w1 ∧
      s.regs.get64 .r10 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w2 ∧
      s.regs.get64 .r11 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w3 ∧
      s.regs.get64 .r12 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w4 ∧
      s.regs.get64 .r13 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w5 ∧
      s.regs.get64 .r14 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w6 ∧
      s.regs.get64 .r15 = (sqr8xAddResult (reductionWords d) t d.status.cf).1.w7 ∧
      s.status.cf = (sqr8xAddResult (reductionWords d) t d.status.cf).2 ∧
      s.zmms = d.zmms ∧ s.dmem = d.dmem ⦄ := by
  vcgen [sqr8x_add_words, sqr8x_add_high] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem sqr8x_add_words_no_carry_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (h : wordsLoaded d.dmem (d.regs.get64 .rdi) t) :
    ⦃ fun s => s = d ⦄ sqr8x_add_words_no_carry ⦃ fun _ s =>
      s.regs.get64 .rax = d.regs.get64 .rax ∧
      s.regs.get64 .rbx = d.regs.get64 .rbx ∧
      s.regs.get64 .rcx = d.regs.get64 .rcx ∧
      s.regs.get64 .rdx = d.regs.get64 .rdx ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .r8 = (sqr8xAddResult (reductionWords d) t false).1.w0 ∧
      s.regs.get64 .r9 = (sqr8xAddResult (reductionWords d) t false).1.w1 ∧
      s.regs.get64 .r10 = (sqr8xAddResult (reductionWords d) t false).1.w2 ∧
      s.regs.get64 .r11 = (sqr8xAddResult (reductionWords d) t false).1.w3 ∧
      s.regs.get64 .r12 = (sqr8xAddResult (reductionWords d) t false).1.w4 ∧
      s.regs.get64 .r13 = (sqr8xAddResult (reductionWords d) t false).1.w5 ∧
      s.regs.get64 .r14 = (sqr8xAddResult (reductionWords d) t false).1.w6 ∧
      s.regs.get64 .r15 = (sqr8xAddResult (reductionWords d) t false).1.w7 ∧
      s.status.cf = (sqr8xAddResult (reductionWords d) t false).2 ∧
      s.zmms = d.zmms ∧ s.dmem = d.dmem ⦄ := by
  vcgen [sqr8x_add_words_no_carry, sqr8x_add_high] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)


end Sqr8xWordAddition

section Sqr8xReduceTail

private theorem unsigned_sub_carry (a b : BitVec 64) :
    ((a - b).toNat != (a.toNat : Int) - b.toNat) = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, BitVec.toNat_sub]
  have ha := a.isLt
  have hb := b.isLt
  omega

attribute [local irreducible] sqr8xAddResult wordsLoaded
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add BitVec.xor_self
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  CondCode.interp_nc CondCode.interp_c unsigned_sub_carry
attribute [local grind =] ofInt_limb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- After the cancellation block, either finish reduction or add the next
workspace block and start multiplying by the saved coefficients. -/
theorem sqr8x_reduce_tail_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (modulusEnd outputEnd m0 q0 : BitVec 64)
    (h_end : d.dmem.loadInt (d.regs.get64 .rsp + 8) 8 = some (Int.ofBytes (Int.toBytes 8 modulusEnd.toInt)))
    (h_out : d.dmem.loadInt (d.regs.get64 .rsp + 16) 8 = some (Int.ofBytes (Int.toBytes 8 outputEnd.toInt)))
    (h_tail : (d.regs.get64 .rbp + 64).toNat < modulusEnd.toNat →
      wordsLoaded d.dmem (d.regs.get64 .rdi) t ∧
      d.dmem.loadInt (d.regs.get64 .rsp + 112) 8 = some (Int.ofBytes (Int.toBytes 8 q0.toInt)) ∧
      d.dmem.loadInt (d.regs.get64 .rbp + 64) 8 = some (Int.ofBytes (Int.toBytes 8 m0.toInt))) :
    ⦃ fun s => s = d ⦄ sqr8x_reduce_tail ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.zmms = d.zmms ∧ s.dmem = d.dmem ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp + 64 ∧ s.regs.get64 .rdx = outputEnd ∧
      ((modulusEnd.toNat ≤ (d.regs.get64 .rbp + 64).toNat ∧
        pc = (_root_.Executable.labels cenv).label ".L8x_no_tail" ∧
        s.regs.get64 .rax = 0 ∧ s.status.cf = false ∧
        s.regs.get64 .r8 = d.regs.get64 .r8 ∧
        s.regs.get64 .r9 = d.regs.get64 .r9 ∧
        s.regs.get64 .r10 = d.regs.get64 .r10 ∧
        s.regs.get64 .r11 = d.regs.get64 .r11 ∧
        s.regs.get64 .r12 = d.regs.get64 .r12 ∧
        s.regs.get64 .r13 = d.regs.get64 .r13 ∧
        s.regs.get64 .r14 = d.regs.get64 .r14 ∧
        s.regs.get64 .r15 = d.regs.get64 .r15) ∨
      ((d.regs.get64 .rbp + 64).toNat < modulusEnd.toNat ∧
        pc = (_root_.Executable.labels cenv).label ".L8x_tail" ∧
        s.regs.get64 .rax = m0 ∧ s.regs.get64 .rbx = q0 ∧ s.regs.get64 .rcx = 8 ∧
        s.regs.get64 .rsi = -(BitVec.ofNat 64 (sqr8xAddResult (reductionWords d) t false).2.toNat) ∧
        s.regs.get64 .r8 = (sqr8xAddResult (reductionWords d) t false).1.w0 ∧
        s.regs.get64 .r9 = (sqr8xAddResult (reductionWords d) t false).1.w1 ∧
        s.regs.get64 .r10 = (sqr8xAddResult (reductionWords d) t false).1.w2 ∧
        s.regs.get64 .r11 = (sqr8xAddResult (reductionWords d) t false).1.w3 ∧
        s.regs.get64 .r12 = (sqr8xAddResult (reductionWords d) t false).1.w4 ∧
        s.regs.get64 .r13 = (sqr8xAddResult (reductionWords d) t false).1.w5 ∧
        s.regs.get64 .r14 = (sqr8xAddResult (reductionWords d) t false).1.w6 ∧
        s.regs.get64 .r15 = (sqr8xAddResult (reductionWords d) t false).1.w7)) ⦄ := by
  vcgen [sqr8x_reduce_tail, sqr8x_add_words_no_carry_correct (t := t)] simplifying_assumptions with
    finish (ematch := 12) (splits := 16) (hom := false) (canonHeartbeats := 5)

end Sqr8xReduceTail

section Sqr8xTailAdvance

attribute [local irreducible] sqr8xAddResult wordsLoaded
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add BitVec.xor_self
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  CondCode.interp_nc CondCode.interp_c unsigned_sub_carry
attribute [local grind =] ofInt_limb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Advance to another modulus block, carrying the saved addition flag, or
leave the tail loop when the modulus is exhausted. -/
theorem sqr8x_tail_advance_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (modulusEnd outputEnd m0 q0 : BitVec 64)
    (h_end : d.dmem.loadInt (d.regs.get64 .rsp + 8) 8 = some (Int.ofBytes (Int.toBytes 8 modulusEnd.toInt)))
    (h_out : d.dmem.loadInt (d.regs.get64 .rsp + 16) 8 = some (Int.ofBytes (Int.toBytes 8 outputEnd.toInt)))
    (h_tail : (d.regs.get64 .rbp + 64).toNat < modulusEnd.toNat →
      wordsLoaded d.dmem (d.regs.get64 .rdi) t ∧
      d.dmem.loadInt (d.regs.get64 .rsp + 112) 8 = some (Int.ofBytes (Int.toBytes 8 q0.toInt)) ∧
      d.dmem.loadInt (d.regs.get64 .rbp + 64) 8 = some (Int.ofBytes (Int.toBytes 8 m0.toInt))) :
    ⦃ fun s => s = d ⦄ sqr8x_tail_advance ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rsp = d.regs.get64 .rsp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.zmms = d.zmms ∧ s.dmem = d.dmem ∧
      s.regs.get64 .rbp = d.regs.get64 .rbp + 64 ∧ s.regs.get64 .rdx = outputEnd ∧
      ((modulusEnd.toNat ≤ (d.regs.get64 .rbp + 64).toNat ∧
        pc = (_root_.Executable.labels cenv).label ".L8x_tail_done" ∧
        s.regs.get64 .rsi = d.regs.get64 .rsi ∧
        s.regs.get64 .r8 = d.regs.get64 .r8 ∧
        s.regs.get64 .r9 = d.regs.get64 .r9 ∧
        s.regs.get64 .r10 = d.regs.get64 .r10 ∧
        s.regs.get64 .r11 = d.regs.get64 .r11 ∧
        s.regs.get64 .r12 = d.regs.get64 .r12 ∧
        s.regs.get64 .r13 = d.regs.get64 .r13 ∧
        s.regs.get64 .r14 = d.regs.get64 .r14 ∧
        s.regs.get64 .r15 = d.regs.get64 .r15) ∨
      ((d.regs.get64 .rbp + 64).toNat < modulusEnd.toNat ∧
        pc = (_root_.Executable.labels cenv).label ".L8x_tail" ∧
        s.regs.get64 .rax = m0 ∧ s.regs.get64 .rbx = q0 ∧ s.regs.get64 .rcx = 8 ∧
        s.regs.get64 .rsi = -(BitVec.ofNat 64 (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).2.toNat) ∧
        s.regs.get64 .r8 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w0 ∧
        s.regs.get64 .r9 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w1 ∧
        s.regs.get64 .r10 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w2 ∧
        s.regs.get64 .r11 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w3 ∧
        s.regs.get64 .r12 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w4 ∧
        s.regs.get64 .r13 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w5 ∧
        s.regs.get64 .r14 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w6 ∧
        s.regs.get64 .r15 = (sqr8xAddResult (reductionWords d) t (d.regs.get64 .rsi != 0)).1.w7)) ⦄ := by
  vcgen [sqr8x_tail_advance, sqr8x_add_words_correct (t := t)] simplifying_assumptions with
    finish (ematch := 12) (splits := 16) (hom := false) (canonHeartbeats := 5)

end Sqr8xTailAdvance

section Sqr8xTailCarry

private abbrev tailCarryResult (d : MachineData) (carry : BitVec 64) :=
  sqr8xAddResult (reductionWords d) ⟨carry, 0, 0, 0, 0, 0, 0, 0⟩ false

attribute [local grind unfold] sqr8xAddResult
attribute [local grind norm] sqr4xAdc_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add BitVec.sub_self BitVec.zero_sub BitVec.xor_self
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  Sqr8xWords.w0_mk Sqr8xWords.w1_mk Sqr8xWords.w2_mk Sqr8xWords.w3_mk
  Sqr8xWords.w4_mk Sqr8xWords.w5_mk Sqr8xWords.w6_mk Sqr8xWords.w7_mk
attribute [local sym_simp] BitVec.zero_add BitVec.sub_self BitVec.zero_sub Option.map_none Option.map_some
attribute [local grind =] ofInt_limb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Incorporate the carry saved at the end of the workspace before adding the
last accumulator block. The tail's separate carry mask becomes the incoming CF. -/
theorem sqr8x_tail_carry_correct [CodeEnv] (d : MachineData) (carry : BitVec 64)
    (h : d.dmem.loadInt (d.regs.get64 .rdx + 0) 8 = some (Int.ofBytes (Int.toBytes 8 carry.toInt))) :
    ⦃ fun s => s = d ⦄ sqr8x_tail_carry ⦃ fun _ s =>
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .rbp = d.regs.get64 .rbp ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rdx = d.regs.get64 .rdx ∧
      s.regs.get64 .rax = BitVec.ofNat 64 (tailCarryResult d carry).2.toNat ∧
      s.regs.get64 .rsi = -d.regs.get64 .rsi ∧ s.status.cf = (d.regs.get64 .rsi != 0) ∧
      s.regs.get64 .r8 = (tailCarryResult d carry).1.w0 ∧
      s.regs.get64 .r9 = (tailCarryResult d carry).1.w1 ∧
      s.regs.get64 .r10 = (tailCarryResult d carry).1.w2 ∧
      s.regs.get64 .r11 = (tailCarryResult d carry).1.w3 ∧
      s.regs.get64 .r12 = (tailCarryResult d carry).1.w4 ∧
      s.regs.get64 .r13 = (tailCarryResult d carry).1.w5 ∧
      s.regs.get64 .r14 = (tailCarryResult d carry).1.w6 ∧
      s.regs.get64 .r15 = (tailCarryResult d carry).1.w7 ∧
      s.zmms = d.zmms ∧ s.dmem = d.dmem ⦄ := by
  vcgen [sqr8x_tail_carry] simplifying_assumptions with
    finish (splits := 0) (hom := false) (canonHeartbeats := 5)

end Sqr8xTailCarry

section Sqr8xReductionFinish

private def returnDisjoint (sp out : BitVec 64) : Prop :=
  ∀ j < 8, readWindowDisjoint sp (out + BitVec.ofNat 64 (8 * j)) 8

private theorem store_words_return_load (mem : DataMem) (out sp : BitVec 64) (w : Sqr8xWords)
    (hd : returnDisjoint sp out) :
    (storeSqr8xWords mem out w).loadInt sp 8 = mem.loadInt sp 8 := by
  dsimp only [storeSqr8xWords]
  rw [load_after_disjoint_store _ (out + 56) sp _ (by simpa [readWindowDisjoint] using hd 7 (by decide))]
  rw [load_after_disjoint_store _ (out + 48) sp _ (by simpa [readWindowDisjoint] using hd 6 (by decide))]
  rw [load_after_disjoint_store _ (out + 40) sp _ (by simpa [readWindowDisjoint] using hd 5 (by decide))]
  rw [load_after_disjoint_store _ (out + 32) sp _ (by simpa [readWindowDisjoint] using hd 4 (by decide))]
  rw [load_after_disjoint_store _ (out + 24) sp _ (by simpa [readWindowDisjoint] using hd 3 (by decide))]
  rw [load_after_disjoint_store _ (out + 16) sp _ (by simpa [readWindowDisjoint] using hd 2 (by decide))]
  rw [load_after_disjoint_store _ (out + 8) sp _ (by simpa [readWindowDisjoint] using hd 1 (by decide))]
  rw [load_after_disjoint_store _ (out + 0) sp _ (by simpa [readWindowDisjoint] using hd 0 (by decide))]

private abbrev reductionFinishResult (d : MachineData) (t : Sqr8xWords) :=
  sqr8xAddResult (reductionWords d) t d.status.cf

attribute [local irreducible] sqr8xAddResult wordsLoaded
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 Width.scaleFactor_W16 BitVec.mul_one
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add BitVec.xor_self
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  CondCode.interp_nc CondCode.interp_c unsigned_sub_carry
attribute [local grind =] ofInt_limb

attribute [local grind norm] Width.bytesv_W64 BitVec.sub_self
local grind_pattern words_loaded_fields => wordsLoaded mem base w
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern store_words_return_load => storeSqr8xWords mem out w, returnDisjoint sp out

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- Add and store the final eight words of a reduction pass. The unsigned
workspace comparison chooses another pass or returns through the caller's stack. -/
theorem sqr8x_reduction_finish_correct [CodeEnv] (d : MachineData) (t : Sqr8xWords)
    (lastMod : Int) (ra : Int64)
    (h_words : wordsLoaded d.dmem (d.regs.get64 .rdi) t)
    (h_mod : d.dmem.loadInt (d.regs.get64 .rbp + (-8#64)) 8 = some lastMod)
    (h_ret : d.retAddr = some ra)
    (hd : returnDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rdi)) :
    ⦃ fun s => s = d ⦄ sqr8x_reduction_finish ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rbp = (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 ∧
      s.regs.get64 .r9 = (d.zmms.get (.xmm .mm3)).extractLsb' 0 64 ∧
      s.regs.get64 .rsi = 0 ∧ s.regs.get64 .rdx = d.regs.get64 .rdx ∧
      s.regs.get64 .rdi = d.regs.get64 .rdi + 64 ∧ s.zmms = d.zmms ∧
      s.regs.get64 .rax = d.regs.get64 .rax + BitVec.ofNat 64 (reductionFinishResult d t).2.toNat ∧
      s.dmem = storeSqr8xWords d.dmem (d.regs.get64 .rdi) (reductionFinishResult d t).1 ∧
      (((d.regs.get64 .rdi + 64).toNat < (d.regs.get64 .rdx).toNat ∧
        pc = (_root_.Executable.labels cenv).label ".L8x_reduction_loop" ∧
        s.regs.get64 .rsp = d.regs.get64 .rsp) ∨
      ((d.regs.get64 .rdx).toNat ≤ (d.regs.get64 .rdi + 64).toNat ∧ pc = ra ∧
        s.regs.get64 .rsp = d.regs.get64 .rsp + 8)) ⦄ := by
  vcgen [sqr8x_reduction_finish, sqr8x_add_words_correct (t := t)] simplifying_assumptions with
    finish (ematch := 16) (splits := 16) (hom := false) (canonHeartbeats := 5)

end Sqr8xReductionFinish

section Sqr8xReductionFold

/-- A word read in the arithmetic reference. The safety invariant supplies
mapped bytes, so the default is never used by a verified run. -/
private def readWord (mem : DataMem) (addr : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((mem.loadInt addr 8).getD 0)

private def readWords (mem : DataMem) (base : BitVec 64) : Sqr8xWords :=
  ⟨readWord mem (base + 0), readWord mem (base + 8), readWord mem (base + 16),
    readWord mem (base + 24), readWord mem (base + 32), readWord mem (base + 40),
    readWord mem (base + 48), readWord mem (base + 56)⟩

private def limbBlock (limbs : List (BitVec 64)) (j : Nat) : Sqr8xWords :=
  ⟨limbs.getD (8 * j) 0, limbs.getD (8 * j + 1) 0, limbs.getD (8 * j + 2) 0,
    limbs.getD (8 * j + 3) 0, limbs.getD (8 * j + 4) 0, limbs.getD (8 * j + 5) 0,
    limbs.getD (8 * j + 6) 0, limbs.getD (8 * j + 7) 0⟩

/-- The ninth word is the unused prefetch after the eighth tail iteration. -/
private def savedCoefficients (mem : DataMem) (sp : BitVec 64) : List (BitVec 64) :=
  (List.range 9).map fun k => readWord mem (sp + BitVec.ofNat 64 (112 - 8 * k))

/-- State between successive modulus blocks within one reduction pass. -/
structure Sqr8xBlockState where
  words : Sqr8xWords
  carry : BitVec 64
  memory : DataMem

/-- Add the next accumulator block, then multiply one further modulus block
by each of the eight saved coefficients. `b = 0` uses modulus words 8 through 15. -/
def sqr8xTailBlockStep (modulus coefficients : List (BitVec 64)) (sp : BitVec 64)
    (pass b : Nat) (s : Sqr8xBlockState) : Sqr8xBlockState :=
  let out := sp + 56 + BitVec.ofNat 64 (64 * (pass + b + 1))
  let sum := sqr8xAddResult s.words (readWords s.memory out) (s.carry != 0)
  let r := sqr8xTailFold (limbBlock modulus (b + 1)) coefficients out
    ⟨sum.1, coefficients.getD 0 0, s.memory⟩ 8
  ⟨r.words, -(BitVec.ofNat 64 sum.2.toNat), r.memory⟩

def sqr8xTailBlocksFold (modulus coefficients : List (BitVec 64)) (sp : BitVec 64)
    (pass : Nat) (initial : Sqr8xBlockState) : Nat → Sqr8xBlockState
  | 0 => initial
  | b + 1 => sqr8xTailBlockStep modulus coefficients sp pass b
      (sqr8xTailBlocksFold modulus coefficients sp pass initial b)

/-- Memory and the extra high word passed between eight-limb reduction passes. -/
structure Sqr8xReductionState where
  carry : BitVec 64
  memory : DataMem

/-- One complete eight-limb Montgomery pass. This is an arithmetic specification:
word multiply-adds, carry-chain additions, and their specified memory writes. -/
def sqr8xReductionPass (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) : Sqr8xReductionState :=
  let base := sp + 56
  let input := readWords initial.memory (base + BitVec.ofNat 64 (64 * pass))
  let saved := initial.memory.storeInt (base + BitVec.ofNat 64 (128 * blocks))
    8 initial.carry.toIntOpaque
  let cancelled := sqr8xReduceFold (limbBlock modulus 0) n0 sp
    ⟨input, input.w0 * n0, saved⟩ 8
  let coefficients := savedCoefficients cancelled.memory sp
  let tail := sqr8xTailBlocksFold modulus coefficients sp pass
    ⟨cancelled.words, 0, cancelled.memory⟩ (blocks - 1)
  let carrySum := if blocks = 1 then (tail.words, false)
    else sqr8xAddResult tail.words ⟨initial.carry, 0, 0, 0, 0, 0, 0, 0⟩ false
  let out := base + BitVec.ofNat 64 (64 * (pass + blocks))
  let sum := sqr8xAddResult carrySum.1 (readWords tail.memory out) (tail.carry != 0)
  ⟨BitVec.ofNat 64 carrySum.2.toNat + BitVec.ofNat 64 sum.2.toNat,
    storeSqr8xWords tail.memory out sum.1⟩

/-- Iterate the eight-limb passes over a modulus of `8 * blocks` limbs. -/
def sqr8xReductionFold (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks : Nat) (initial : Sqr8xReductionState) : Nat → Sqr8xReductionState
  | 0 => initial
  | i + 1 => sqr8xReductionPass modulus n0 sp blocks i
      (sqr8xReductionFold modulus n0 sp blocks initial i)

private theorem subdom_trans {a b c : DataMem} (h1 : Mem.SubDom a b) (h2 : Mem.SubDom b c) :
    Mem.SubDom a c := fun k hk => h2 k (h1 k hk)

private theorem store_words_subdom (mem : DataMem) (base : BitVec 64) (w : Sqr8xWords) :
    Mem.SubDom mem (storeSqr8xWords mem base w) := by
  exact ((((((((Mem.SubDom.refl mem).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _

private theorem tail_block_subdom (modulus coefficients : List (BitVec 64))
    (sp : BitVec 64) (pass b : Nat) (s : Sqr8xBlockState) :
    Mem.SubDom s.memory (sqr8xTailBlockStep modulus coefficients sp pass b s).memory := by
  dsimp only [sqr8xTailBlockStep]
  exact tail_fold_subdom _ _ _ ⟨_, _, s.memory⟩ 8

private theorem tail_blocks_subdom (modulus coefficients : List (BitVec 64))
    (sp : BitVec 64) (pass : Nat) (initial : Sqr8xBlockState) (b : Nat) :
    Mem.SubDom initial.memory (sqr8xTailBlocksFold modulus coefficients sp pass initial b).memory := by
  induction b with
  | zero => exact Mem.SubDom.refl _
  | succ b ih => exact subdom_trans ih (tail_block_subdom _ _ _ _ _ _)

private theorem reduction_pass_subdom (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) :
    Mem.SubDom initial.memory (sqr8xReductionPass modulus n0 sp blocks pass initial).memory := by
  dsimp only [sqr8xReductionPass]
  apply subdom_trans ?_ (store_words_subdom _ _ _)
  apply subdom_trans ?_ (tail_blocks_subdom _ _ _ _ ⟨_, _, _⟩ (blocks - 1))
  apply subdom_trans ?_ (reduce_fold_subdom _ _ _ ⟨_, _, _⟩ 8)
  exact (Mem.SubDom.refl initial.memory).storeInt _ _ _

private theorem reduction_fold_subdom (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks : Nat) (initial : Sqr8xReductionState) (i : Nat) :
    Mem.SubDom initial.memory (sqr8xReductionFold modulus n0 sp blocks initial i).memory := by
  induction i with
  | zero => exact Mem.SubDom.refl _
  | succ i ih => exact subdom_trans ih (reduction_pass_subdom _ _ _ _ _ _)

private theorem read_word_load (mem : DataMem) (addr : BitVec 64)
    (h : (mem.loadInt addr 8).isSome = true) :
    mem.loadInt addr 8 = some (Int.ofBytes (Int.toBytes 8 (readWord mem addr).toInt)) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp hv
  have hlen : bs.length = 8 := by
    have he := congrArg List.length (List.allSome_eq_map_some hb)
    simpa only [List.length_map, List.length_range] using he.symm
  have he : Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
    rw [BitVec.toInt_ofInt]
    exact Int.toBytes_bmod_ofBytes 8 bs hlen
  simp only [readWord, hv, Option.getD_some, he]

private theorem read_words_loaded (mem : DataMem) (base : BitVec 64)
    (h : ∀ i < 8, (mem.loadInt (base + BitVec.ofNat 64 (8 * i)) 8).isSome = true) :
    wordsLoaded mem base (readWords mem base) := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact read_word_load mem _ (h _ (by decide))

private theorem saved_coefficient_load (mem : DataMem) (sp : BitVec 64) (k : Nat) (hk : k < 9)
    (h : (mem.loadInt (sp + BitVec.ofNat 64 (112 - 8 * k)) 8).isSome = true) :
    mem.loadInt (sp + BitVec.ofNat 64 (112 - 8 * k)) 8 =
      some (Int.ofBytes (Int.toBytes 8 ((savedCoefficients mem sp).getD k 0).toInt)) := by
  have hg : (savedCoefficients mem sp).getD k 0 =
      readWord mem (sp + BitVec.ofNat 64 (112 - 8 * k)) := by
    simp [savedCoefficients, List.getD_eq_getElem?_getD, hk]
  rw [hg]
  exact read_word_load _ _ h

private def reductionMemory (original mem : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) : Prop :=
  Mem.SubDom original mem ∧
  (∀ j < modulus.length, mem.loadInt (mp + BitVec.ofNat 64 (8 * j)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (modulus.getD j 0).toInt))) ∧
  ∀ j < 6, mem.loadInt (sp + BitVec.ofNat 64 (8 * j)) 8 =
    original.loadInt (sp + BitVec.ofNat 64 (8 * j)) 8

private def modulusStackDisjoint (sp mp : BitVec 64) (blocks : Nat) : Prop :=
  ∀ i < 64 * blocks, ∀ j < 128 * blocks + 64,
    mp + BitVec.ofNat 64 i ≠ sp + BitVec.ofNat 64 j

private theorem stack_words_disjoint (sp : BitVec 64) (i j : Nat)
    (hi : 8 * i + 8 ≤ 2 ^ 64) (hj : 8 * j + 8 ≤ 2 ^ 64) (hne : i ≠ j) :
    readWindowDisjoint (sp + BitVec.ofNat 64 (8 * i)) (sp + BitVec.ofNat 64 (8 * j)) 8 := by
  intro u hu v hv
  grind only [= BitVec.toNat_ofNatLT]

private theorem reduction_memory_store (original mem : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (blocks : Nat)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks)
    (h : reductionMemory original mem sp mp modulus)
    (i : Nat) (h_low : 7 ≤ i) (h_high : i < 16 * blocks + 8) (v : Int) :
    reductionMemory original (mem.storeInt (sp + BitVec.ofNat 64 (8 * i)) 8 v) sp mp modulus := by
  refine ⟨h.1.storeInt _ _ _, ?_, ?_⟩
  · intro j hj
    rw [load_after_disjoint_store]
    · exact h.2.1 j hj
    · intro u hu w hw
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        h_disjoint (8 * j + u) (by omega) (8 * i + w) (by omega)
  · intro j hj
    rw [load_after_disjoint_store]
    · exact h.2.2 j hj
    · exact stack_words_disjoint sp j i (by omega) (by omega) (by omega)

private theorem cancellation_memory (original : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (blocks : Nat) (n0 : BitVec 64)
    (h_pos : 0 < blocks) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks)
    (initial : Sqr8xReduceState) (h : reductionMemory original initial.memory sp mp modulus)
    (k : Nat) (hk : k ≤ 8) :
    reductionMemory original (sqr8xReduceFold (limbBlock modulus 0) n0 sp initial k).memory sp mp modulus := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hs := reduction_memory_store original _ sp mp modulus blocks h_len h_bound h_disjoint
      (ih (by omega)) (14 - k) (by omega) (by omega)
      (sqr8xReduceFold (limbBlock modulus 0) n0 sp initial k).coefficient.toIntOpaque
    have hoff : 8 * (14 - k) = 112 - 8 * k := by omega
    simpa only [sqr8xReduceFold, hoff] using hs

private theorem tail_memory (original : DataMem) (sp mp : BitVec 64)
    (modulus coefficients : List (BitVec 64)) (blocks pass b : Nat)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks) (h_pass : pass < blocks) (h_block : b + 1 < blocks)
    (initial : Sqr8xReduceState) (h : reductionMemory original initial.memory sp mp modulus)
    (k : Nat) (hk : k ≤ 8) :
    reductionMemory original
      (sqr8xTailFold (limbBlock modulus (b + 1)) coefficients
        (sp + 56 + BitVec.ofNat 64 (64 * (pass + b + 1))) initial k).memory sp mp modulus := by
  induction k with
  | zero => exact h
  | succ k ih =>
    dsimp only [sqr8xTailFold]
    have hoff : sp + 56 + BitVec.ofNat 64 (64 * (pass + b + 1)) + BitVec.ofNat 64 (8 * k) =
        sp + BitVec.ofNat 64 (8 * (7 + 8 * (pass + b + 1) + k)) := by
      rw [show 8 * (7 + 8 * (pass + b + 1) + k) = 56 + 64 * (pass + b + 1) + 8 * k by omega]
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    rw [hoff]
    exact reduction_memory_store original _ sp mp modulus blocks h_len h_bound h_disjoint
      (ih (by omega)) _ (by omega) (by omega) _

private theorem tail_blocks_memory (original : DataMem) (sp mp : BitVec 64)
    (modulus coefficients : List (BitVec 64)) (blocks pass : Nat)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks) (h_pass : pass < blocks)
    (initial : Sqr8xBlockState) (h : reductionMemory original initial.memory sp mp modulus)
    (b : Nat) (hb : b < blocks) :
    reductionMemory original
      (sqr8xTailBlocksFold modulus coefficients sp pass initial b).memory sp mp modulus := by
  induction b with
  | zero => exact h
  | succ b ih =>
    dsimp only [sqr8xTailBlocksFold, sqr8xTailBlockStep]
    exact tail_memory original sp mp modulus coefficients blocks pass b h_len h_bound h_disjoint
      h_pass hb ⟨_, _, _⟩ (ih (by omega)) 8 (by decide)

private theorem reduction_store_words (original mem : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (blocks pass : Nat) (w : Sqr8xWords)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks) (h_pass : pass < blocks)
    (h : reductionMemory original mem sp mp modulus) :
    reductionMemory original
      (storeSqr8xWords mem (sp + 56 + BitVec.ofNat 64 (64 * (pass + blocks))) w) sp mp modulus := by
  have hoff (j : Nat) : sp + 56 + BitVec.ofNat 64 (64 * (pass + blocks)) + BitVec.ofNat 64 (8 * j) =
      sp + BitVec.ofNat 64 (8 * (7 + 8 * (pass + blocks) + j)) := by
    rw [show 8 * (7 + 8 * (pass + blocks) + j) = 56 + 64 * (pass + blocks) + 8 * j by omega]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  have step (mem : DataMem) (j : Nat) (hj : j < 8) (v : Int)
      (hm : reductionMemory original mem sp mp modulus) :
      reductionMemory original (mem.storeInt
        (sp + 56 + BitVec.ofNat 64 (64 * (pass + blocks)) + BitVec.ofNat 64 (8 * j)) 8 v) sp mp modulus := by
    rw [hoff]
    exact reduction_memory_store original mem sp mp modulus blocks h_len h_bound h_disjoint
      hm _ (by omega) (by omega) v
  exact step _ 7 (by decide) _ (step _ 6 (by decide) _ (step _ 5 (by decide) _
    (step _ 4 (by decide) _ (step _ 3 (by decide) _ (step _ 2 (by decide) _
      (step _ 1 (by decide) _ (step _ 0 (by decide) _ h)))))))

private theorem reduction_pass_memory (original : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (n0 : BitVec 64) (blocks pass : Nat)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks) (h_pass : pass < blocks)
    (initial : Sqr8xReductionState) (h : reductionMemory original initial.memory sp mp modulus) :
    reductionMemory original (sqr8xReductionPass modulus n0 sp blocks pass initial).memory sp mp modulus := by
  dsimp only [sqr8xReductionPass]
  apply reduction_store_words original _ sp mp modulus blocks pass _ h_len h_bound h_disjoint h_pass
  apply tail_blocks_memory original sp mp modulus _ blocks pass h_len h_bound h_disjoint h_pass
    ⟨_, _, _⟩ ?_ (blocks - 1) (by omega)
  apply cancellation_memory original sp mp modulus blocks n0 (by omega) h_len h_bound h_disjoint
    ⟨_, _, _⟩ ?_ 8 (by decide)
  have hoff : sp + 56 + BitVec.ofNat 64 (128 * blocks) =
      sp + BitVec.ofNat 64 (8 * (7 + 16 * blocks)) := by
    rw [show 8 * (7 + 16 * blocks) = 56 + 128 * blocks by omega]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hoff]
  exact reduction_memory_store original _ sp mp modulus blocks h_len h_bound h_disjoint h
    (7 + 16 * blocks) (by omega) (by omega) _

private theorem reduction_fold_memory (original : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (n0 : BitVec 64) (blocks : Nat)
    (h_len : modulus.length = 8 * blocks) (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint sp mp blocks)
    (initial : Sqr8xReductionState) (h : reductionMemory original initial.memory sp mp modulus)
    (i : Nat) (hi : i ≤ blocks) :
    reductionMemory original (sqr8xReductionFold modulus n0 sp blocks initial i).memory sp mp modulus := by
  induction i with
  | zero => exact h
  | succ i ih =>
    exact reduction_pass_memory original sp mp modulus n0 blocks i h_len h_bound h_disjoint
      (by omega) _ (ih (by omega))

end Sqr8xReductionFold

end Sqr8xInternal

section Sqr8xFullReduction

private def sqr8x_reduce_cycle : Program :=
  sqr8x_reduce_iteration ++ parse("decl %ecx\njnz .L8x_reduce")

private def sqr8x_tail_cycle : Program :=
  sqr8x_tail_iteration ++ parse("decl %ecx\njnz .L8x_tail")

/-- The complete reduction half, including its nested tail loop and return. -/
def sqr8x_reduction_prog : Program :=
  parse("__bn_sqr8x_reduction:") ++ sqr8x_reduction_preamble ++
  parse(".L8x_reduce:") ++ sqr8x_reduce_iteration ++
  parse("decl %ecx\njnz .L8x_reduce") ++ sqr8x_reduce_tail ++
  parse(".L8x_tail:") ++ sqr8x_tail_iteration ++
  parse("decl %ecx\njnz .L8x_tail") ++ sqr8x_tail_finish

private theorem reduction_view : Program.view sqr8x_reduction_prog =
    ([], [("__bn_sqr8x_reduction", sqr8x_reduction_setup),
      (".L8x_reduction_loop", sqr8x_reduction_entry),
      (".L8x_reduce", sqr8x_reduce_cycle ++ sqr8x_reduce_tail),
      (".L8x_tail", sqr8x_tail_cycle ++ sqr8x_tail_advance),
      (".L8x_tail_done", sqr8x_tail_carry),
      (".L8x_no_tail", sqr8x_reduction_finish)]) := by
  decide

private def reductionInitialMemory (d : MachineData) (blocks : Nat) : DataMem :=
  (d.dmem.storeInt (d.regs.get64 .rsp + 8) 8
    (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toIntOpaque).storeInt
      (d.regs.get64 .rsp + 16) 8
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toIntOpaque

/-- Expected state after complete reduction passes, including the two stack
metadata writes performed on entry. -/
def sqr8xReductionPrefix (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass : Nat) : Sqr8xReductionState :=
  sqr8xReductionFold modulus n0 (d.regs.get64 .rsp) blocks
    ⟨0, reductionInitialMemory d blocks⟩ pass

private def cancellationPrefix (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass k : Nat) : Sqr8xReduceState :=
  let r := sqr8xReductionPrefix d modulus n0 blocks pass
  let base := d.regs.get64 .rsp + 56
  let words := readWords r.memory (base + BitVec.ofNat 64 (64 * pass))
  sqr8xReduceFold (limbBlock modulus 0) n0 (d.regs.get64 .rsp)
    ⟨words, words.w0 * n0,
      r.memory.storeInt (base + BitVec.ofNat 64 (128 * blocks)) 8 r.carry.toIntOpaque⟩ k

private def passCoefficients (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass : Nat) : List (BitVec 64) :=
  savedCoefficients (cancellationPrefix d modulus n0 blocks pass 8).memory (d.regs.get64 .rsp)

private def tailBlocksPrefix (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass b : Nat) : Sqr8xBlockState :=
  let r := cancellationPrefix d modulus n0 blocks pass 8
  sqr8xTailBlocksFold modulus (passCoefficients d modulus n0 blocks pass) (d.regs.get64 .rsp)
    pass ⟨r.words, 0, r.memory⟩ b

private def tailBlockSum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass b : Nat) : Sqr8xWords × Bool :=
  let r := tailBlocksPrefix d modulus n0 blocks pass (b - 1)
  let out := d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (pass + b))
  sqr8xAddResult r.words (readWords r.memory out) (r.carry != 0)

private def tailIterationPrefix (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass b k : Nat) : Sqr8xReduceState :=
  let r := tailBlocksPrefix d modulus n0 blocks pass (b - 1)
  let out := d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (pass + b))
  let q := passCoefficients d modulus n0 blocks pass
  sqr8xTailFold (limbBlock modulus b) q out
    ⟨(tailBlockSum d modulus n0 blocks pass b).1, q.getD 0 0, r.memory⟩ k

private def passCarrySum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass : Nat) : Sqr8xWords × Bool :=
  let r := tailBlocksPrefix d modulus n0 blocks pass (blocks - 1)
  if blocks = 1 then (r.words, false)
  else sqr8xAddResult r.words ⟨(sqr8xReductionPrefix d modulus n0 blocks pass).carry, 0, 0, 0, 0, 0, 0, 0⟩ false

private def passFinishSum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass : Nat) : Sqr8xWords × Bool :=
  let r := tailBlocksPrefix d modulus n0 blocks pass (blocks - 1)
  let out := d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (pass + blocks))
  sqr8xAddResult (passCarrySum d modulus n0 blocks pass).1 (readWords r.memory out) (r.carry != 0)

private theorem reduction_prefix_step (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass : Nat) :
    (sqr8xReductionPrefix d modulus n0 blocks (pass + 1)).carry =
      BitVec.ofNat 64 (passCarrySum d modulus n0 blocks pass).2.toNat +
        BitVec.ofNat 64 (passFinishSum d modulus n0 blocks pass).2.toNat ∧
    (sqr8xReductionPrefix d modulus n0 blocks (pass + 1)).memory =
      storeSqr8xWords (tailBlocksPrefix d modulus n0 blocks pass (blocks - 1)).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (pass + blocks)))
        (passFinishSum d modulus n0 blocks pass).1 := ⟨rfl, rfl⟩

private theorem tail_block_prefix_step (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks pass b : Nat) (hb : 0 < b) :
    (tailBlocksPrefix d modulus n0 blocks pass b).words =
      (tailIterationPrefix d modulus n0 blocks pass b 8).words ∧
    (tailBlocksPrefix d modulus n0 blocks pass b).memory =
      (tailIterationPrefix d modulus n0 blocks pass b 8).memory ∧
    (tailBlocksPrefix d modulus n0 blocks pass b).carry =
      -(BitVec.ofNat 64 (tailBlockSum d modulus n0 blocks pass b).2.toNat) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  simp only [tailBlocksPrefix, sqr8xTailBlocksFold, sqr8xTailBlockStep, tailIterationPrefix,
    tailBlockSum, Nat.add_sub_cancel, Nat.succ_eq_add_one]
  exact ⟨rfl, rfl, rfl⟩

private def reductionOuterIndex (sp : BitVec 64) (blocks : Nat) (p : BitVec 64) : Nat :=
  (p.toNat - (sp.toNat + 56 + 64 * blocks)) / 64

private def cancellationOuterIndex (sp p : BitVec 64) : Nat :=
  (p.toNat - (sp.toNat + 120)) / 64

private def reductionBlockIndex (mp p : BitVec 64) : Nat := (p.toNat - mp.toNat) / 64

private def tailOuterIndex (sp p : BitVec 64) (b k : Nat) : Nat :=
  (p.toNat - (sp.toNat + 56 + 64 * b + 8 * k)) / 64

private theorem reduction_pointer_nat (sp : BitVec 64) (blocks i k : Nat)
    (hi : 64 * i + 8 * k ≤ 128 * blocks) (hk : k < 8)
    (hbound : sp.toNat + 128 * blocks + 64 < 2 ^ 64) :
    (sp + 56 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (8 * k)).toNat =
      sp.toNat + 56 + 64 * i + 8 * k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (56 : BitVec 64).toNat = 56 from rfl]
  omega

private theorem modulus_pointer_nat (mp : BitVec 64) (blocks b : Nat) (hb : b ≤ blocks)
    (hbound : mp.toNat + 64 * blocks < 2 ^ 64) :
    (mp + BitVec.ofNat 64 (64 * b)).toNat = mp.toNat + 64 * b := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem reduction_outer_index (sp : BitVec 64) (blocks i : Nat) (hi : i ≤ blocks)
    (hbound : sp.toNat + 128 * blocks + 64 < 2 ^ 64) :
    reductionOuterIndex sp blocks (sp + 56 + BitVec.ofNat 64 (64 * (blocks + i))) = i := by
  simp only [reductionOuterIndex, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (56 : BitVec 64).toNat = 56 from rfl]
  omega

private theorem cancellation_outer_index (sp : BitVec 64) (blocks i : Nat) (hi : i < blocks)
    (hbound : sp.toNat + 128 * blocks + 64 < 2 ^ 64) :
    cancellationOuterIndex sp (sp + 56 + BitVec.ofNat 64 (64 * (i + 1))) = i := by
  simp only [cancellationOuterIndex, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (56 : BitVec 64).toNat = 56 from rfl]
  omega

private theorem reduction_block_index (mp : BitVec 64) (blocks b : Nat) (hb : b ≤ blocks)
    (hbound : mp.toNat + 64 * blocks < 2 ^ 64) :
    reductionBlockIndex mp (mp + BitVec.ofNat 64 (64 * b)) = b := by
  simp only [reductionBlockIndex, modulus_pointer_nat mp blocks b hb hbound]
  omega

private theorem tail_outer_index (sp : BitVec 64) (blocks i b k : Nat)
    (hi : i < blocks) (hb : b < blocks) (hk : k ≤ 8)
    (hbound : sp.toNat + 128 * blocks + 64 < 2 ^ 64) :
    tailOuterIndex sp (sp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k)) b k = i := by
  have hnat : (sp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k)).toNat =
      sp.toNat + 56 + 64 * (i + b) + 8 * k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (56 : BitVec 64).toNat = 56 from rfl]
    omega
  simp only [tailOuterIndex, hnat]
  omega

private theorem reduction_prefix_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h_init : reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (pass : Nat) (hp : pass ≤ blocks) :
    reductionMemory (reductionInitialMemory d blocks) (sqr8xReductionPrefix d modulus n0 blocks pass).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  reduction_fold_memory _ _ _ modulus n0 blocks h_len h_bound h_disjoint ⟨0, _⟩ h_init pass hp

private theorem cancellation_prefix_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h_init : reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (pass k : Nat) (hp : pass < blocks) (hk : k ≤ 8) :
    reductionMemory (reductionInitialMemory d blocks) (cancellationPrefix d modulus n0 blocks pass k).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus := by
  dsimp only [cancellationPrefix]
  apply cancellation_memory _ _ _ modulus blocks n0 (by omega) h_len h_bound h_disjoint ⟨_, _, _⟩ ?_ k hk
  have hoff : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) =
      d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + 16 * blocks)) := by
    rw [show 8 * (7 + 16 * blocks) = 56 + 128 * blocks by omega]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hoff]
  exact reduction_memory_store _ _ _ _ modulus blocks h_len h_bound h_disjoint
    (reduction_prefix_memory d modulus n0 blocks h_len h_bound h_disjoint h_init pass (by omega))
    (7 + 16 * blocks) (by omega) (by omega) _

private theorem tail_blocks_prefix_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h_init : reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (pass b : Nat) (hp : pass < blocks) (hb : b < blocks) :
    reductionMemory (reductionInitialMemory d blocks) (tailBlocksPrefix d modulus n0 blocks pass b).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  tail_blocks_memory _ _ _ modulus _ blocks pass h_len h_bound h_disjoint hp ⟨_, _, _⟩
    (cancellation_prefix_memory d modulus n0 blocks h_len h_bound h_disjoint h_init pass 8 hp (by decide)) b hb

private theorem tail_iteration_prefix_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h_init : reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (pass b k : Nat) (hp : pass < blocks) (hb0 : 0 < b) (hb : b < blocks) (hk : k ≤ 8) :
    reductionMemory (reductionInitialMemory d blocks) (tailIterationPrefix d modulus n0 blocks pass b k).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  dsimp only [tailIterationPrefix]
  exact tail_memory _ _ _ modulus _ blocks pass b h_len h_bound h_disjoint hp hb ⟨_, _, _⟩
    (tail_blocks_prefix_memory d modulus n0 blocks h_len h_bound h_disjoint h_init pass b hp (by omega)) k hk

private theorem tail_preserves_stack_prefix (m : Sqr8xWords) (q : List (BitVec 64)) (sp : BitVec 64)
    (blocks pass b : Nat) (initial : Sqr8xReduceState)
    (h_bound : 128 * blocks + 64 < 2 ^ 64) (hp : pass < blocks) (hb0 : 0 < b) (hb : b < blocks)
    (k j : Nat) (hk : k ≤ 8) (hj : j < 15) :
    (sqr8xTailFold m q (sp + 56 + BitVec.ofNat 64 (64 * (pass + b))) initial k).memory.loadInt
      (sp + BitVec.ofNat 64 (8 * j)) 8 = initial.memory.loadInt (sp + BitVec.ofNat 64 (8 * j)) 8 := by
  apply tail_fold_load
  intro i hi
  have hoff : sp + 56 + BitVec.ofNat 64 (64 * (pass + b)) + BitVec.ofNat 64 (8 * i) =
      sp + BitVec.ofNat 64 (8 * (7 + 8 * (pass + b) + i)) := by
    rw [show 8 * (7 + 8 * (pass + b) + i) = 56 + 64 * (pass + b) + 8 * i by omega]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hoff]
  exact stack_words_disjoint sp j _ (by omega) (by omega) (by omega)

private theorem tail_blocks_preserve_stack_prefix (modulus q : List (BitVec 64)) (sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xBlockState)
    (h_bound : 128 * blocks + 64 < 2 ^ 64) (hp : pass < blocks)
    (b j : Nat) (hb : b < blocks) (hj : j < 15) :
    (sqr8xTailBlocksFold modulus q sp pass initial b).memory.loadInt (sp + BitVec.ofNat 64 (8 * j)) 8 =
      initial.memory.loadInt (sp + BitVec.ofNat 64 (8 * j)) 8 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    dsimp only [sqr8xTailBlocksFold, sqr8xTailBlockStep]
    have hoff : pass + b + 1 = pass + (b + 1) := by omega
    simp only [hoff]
    rw [tail_preserves_stack_prefix _ q sp blocks pass (b + 1) ⟨_, _, _⟩ h_bound hp (by omega) hb 8 j (by decide) hj]
    exact ih (by omega)

private abbrev wordsMatch (s : MachineData) (w : Sqr8xWords) : Prop :=
  s.regs.get64 .r8 = w.w0 ∧
  s.regs.get64 .r9 = w.w1 ∧
  s.regs.get64 .r10 = w.w2 ∧
  s.regs.get64 .r11 = w.w3 ∧
  s.regs.get64 .r12 = w.w4 ∧
  s.regs.get64 .r13 = w.w5 ∧
  s.regs.get64 .r14 = w.w6 ∧
  s.regs.get64 .r15 = w.w7

private def reductionOuterInvariant (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let i := reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)
  i < blocks ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧ s.regs.get64 .r9 = -BitVec.ofNat 64 (64 * blocks) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) ∧
  s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rax = (sqr8xReductionPrefix d modulus n0 blocks i).carry ∧
  s.dmem = (sqr8xReductionPrefix d modulus n0 blocks i).memory

private def cancellationInvariant (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let i := cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)
  let k := reduceIndex (s.regs.get64 .rcx)
  let r := cancellationPrefix d modulus n0 blocks i k
  i < blocks ∧ k < 8 ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)) ∧
  s.regs.get64 .rcx = reduceCount k ∧ s.regs.get64 .rax = (limbBlock modulus 0).w0 ∧
  s.regs.get64 .rbx = r.coefficient ∧ wordsMatch s r.words ∧ s.dmem = r.memory

private def reductionTailInvariant (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let b := reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)
  let k := reduceIndex (s.regs.get64 .rcx)
  let i := tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi) b k
  let r := tailIterationPrefix d modulus n0 blocks i b k
  i < blocks ∧ 0 < b ∧ b < blocks ∧ k < 8 ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k) ∧
  s.regs.get64 .rcx = reduceCount k ∧ s.regs.get64 .rax = (limbBlock modulus b).w0 ∧
  s.regs.get64 .rsi = -(BitVec.ofNat 64 (tailBlockSum d modulus n0 blocks i b).2.toNat) ∧
  s.regs.get64 .rbx = r.coefficient ∧ wordsMatch s r.words ∧ s.dmem = r.memory

private def reductionCarryInvariant (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let i := reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)
  let r := tailBlocksPrefix d modulus n0 blocks i (blocks - 1)
  i < blocks ∧ 1 < blocks ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) ∧
  s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rsi = r.carry ∧ wordsMatch s r.words ∧ s.dmem = r.memory

private def reductionFinishInvariant (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let i := reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)
  let r := tailBlocksPrefix d modulus n0 blocks i (blocks - 1)
  i < blocks ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) ∧
  s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rax = BitVec.ofNat 64 (passCarrySum d modulus n0 blocks i).2.toNat ∧
  s.status.cf = (r.carry != 0) ∧ wordsMatch s (passCarrySum d modulus n0 blocks i).1 ∧
  s.dmem = r.memory

private abbrev reductionTable (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : Label → MachineData → Prop
  | "__bn_sqr8x_reduction", s => s = d
  | ".L8x_reduction_loop", s => reductionOuterInvariant d modulus n0 blocks s
  | ".L8x_reduce", s => cancellationInvariant d modulus n0 blocks s
  | ".L8x_tail", s => reductionTailInvariant d modulus n0 blocks s
  | ".L8x_tail_done", s => reductionCarryInvariant d modulus n0 blocks s
  | ".L8x_no_tail", s => reductionFinishInvariant d modulus n0 blocks s
  | _, _ => False

private abbrev reductionVar (d : MachineData) (blocks : Nat) : Label → MachineData → Nat
  | "__bn_sqr8x_reduction", _ => (blocks + 1) * 2 ^ 64
  | ".L8x_reduction_loop", s =>
      (blocks - reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)) * 2 ^ 64
  | ".L8x_reduce", s =>
      (blocks - cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)) * 2 ^ 64 -
        (reduceIndex (s.regs.get64 .rcx) + 1)
  | ".L8x_tail", s =>
      let b := reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)
      let k := reduceIndex (s.regs.get64 .rcx)
      (blocks - tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi) b k) * 2 ^ 64 - (8 * b + k + 1)
  | ".L8x_tail_done", s =>
      (blocks - reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)) * 2 ^ 64 - (8 * blocks + 1)
  | ".L8x_no_tail", s =>
      (blocks - reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)) * 2 ^ 64 - (8 * blocks + 2)
  | _, _ => 0

private theorem reduction_prefix_zero (d : MachineData) (modulus : List (BitVec 64)) (n0 : BitVec 64) (blocks : Nat) :
    (sqr8xReductionPrefix d modulus n0 blocks 0).carry = 0 ∧
    (sqr8xReductionPrefix d modulus n0 blocks 0).memory = reductionInitialMemory d blocks := ⟨rfl, rfl⟩

private theorem reduction_initial_index (sp : BitVec 64) (blocks : Nat)
    (h_bound : sp.toNat + 128 * blocks + 64 < 2 ^ 64) :
    reductionOuterIndex sp blocks (sp + BitVec.ofNat 64 (64 * blocks) + 56) = 0 := by
  simp only [reductionOuterIndex, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (56 : BitVec 64).toNat = 56 from rfl]
  omega

section
attribute [local irreducible] reductionOuterIndex sqr8xReductionPrefix
attribute [local grind unfold] reductionInitialMemory reductionOuterInvariant
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
attribute [local grind =] reduction_initial_index
local grind_pattern reduction_prefix_zero => sqr8xReductionPrefix d modulus n0 blocks 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_setup_establishes [CodeEnv] (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h_pos : 0 < blocks)
    (h_bound : (d.regs.get64 .rsp).toNat + 128 * blocks + 64 < 2 ^ 64)
    (h_size : d.regs.get64 .r9 = BitVec.ofNat 64 (64 * blocks))
    (h0 : (d.dmem.loadInt (d.regs.get64 .rsp + 8) 8).isSome = true)
    (h1 : (d.dmem.loadInt (d.regs.get64 .rsp + 16) 8).isSome = true) :
    ⦃ fun s => s = d ⦄ sqr8x_reduction_setup ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduction_loop" ∧
        reductionOuterInvariant d modulus n0 blocks s ⦄ := by
  vcgen [sqr8x_reduction_setup_correct] simplifying_assumptions with
    finish (ematch := 12) (splits := 16)
end

private theorem initial_memory_modulus (d : MachineData) (modulus : List (BitVec 64))
    (blocks : Nat) (h_len : modulus.length = 8 * blocks)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h_load : ∀ j < modulus.length, d.dmem.loadInt (d.regs.get64 .rbp + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (modulus.getD j 0).toInt))) :
    reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus := by
  refine ⟨Mem.SubDom.refl _, ?_, by intros; rfl⟩
  intro j hj
  dsimp only [reductionInitialMemory]
  rw [load_after_disjoint_store]
  · rw [load_after_disjoint_store]
    · exact h_load j hj
    · intro u hu v hv
      have h := h_disjoint (8 * j + u) (by omega) (8 + v) (by omega)
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using h
  · intro u hu v hv
    have h := h_disjoint (8 * j + u) (by omega) (16 + v) (by omega)
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using h

private theorem initial_memory_preserves (d : MachineData) (blocks j : Nat)
    (hj : j < 6) (hj1 : j ≠ 1) (hj2 : j ≠ 2) :
    (reductionInitialMemory d blocks).loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8 =
      d.dmem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8 := by
  dsimp only [reductionInitialMemory]
  rw [load_after_disjoint_store]
  · rw [load_after_disjoint_store]
    · exact stack_words_disjoint _ j 1 (by omega) (by decide) hj1
  · exact stack_words_disjoint _ j 2 (by omega) (by decide) hj2

private theorem initial_memory_mapped (d : MachineData) (blocks : Nat) :
    Mem.SubDom d.dmem (reductionInitialMemory d blocks) :=
  ((Mem.SubDom.refl d.dmem).storeInt _ _ _).storeInt _ _ _

private theorem initial_memory_ends (d : MachineData) (blocks : Nat) :
    (reductionInitialMemory d blocks).loadInt (d.regs.get64 .rsp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toInt)) ∧
    (reductionInitialMemory d blocks).loadInt (d.regs.get64 .rsp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toInt)) := by
  dsimp only [reductionInitialMemory]
  constructor
  · rw [load_after_disjoint_store _ (d.regs.get64 .rsp + 16)]
    · exact Mem.loadInt_storeInt _ _ _ _ (by decide)
    · exact stack_words_disjoint _ 1 2 (by decide) (by decide) (by decide)
  · exact Mem.loadInt_storeInt _ _ _ _ (by decide)

private theorem modulus_block_loaded (original mem : DataMem) (sp mp : BitVec 64)
    (modulus : List (BitVec 64)) (blocks b : Nat) (h_len : modulus.length = 8 * blocks)
    (h : reductionMemory original mem sp mp modulus) (hb : b < blocks) :
    wordsLoaded mem (mp + BitVec.ofNat 64 (64 * b)) (limbBlock modulus b) := by
  intro i hi
  have he := h.2.1 (8 * b + i) (by omega)
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [limbBlock, Sqr8xWords.get, Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem reduction_stack_load (d : MachineData) (blocks : Nat) (modulus : List (BitVec 64))
    (mem : DataMem) (h : reductionMemory (reductionInitialMemory d blocks) mem
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (h_map : ∀ j < 16 * blocks + 8, (d.dmem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true)
    (j : Nat) (hj : j < 16 * blocks + 8) :
    (mem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true :=
  Mem.SubDom.loadInt_isSome (subdom_trans (initial_memory_mapped d blocks) h.1) (h_map j hj)

private theorem cancellation_frame (d : MachineData) (blocks : Nat) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (mem : DataMem) (h_pos : 0 < blocks) (h_len : modulus.length = 8 * blocks)
    (h_bound : 128 * blocks + 64 < 2 ^ 64)
    (h_disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks)
    (h : reductionMemory (reductionInitialMemory d blocks) mem (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (h_map : ∀ j < 16 * blocks + 8, (d.dmem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true)
    (h_inverse : d.dmem.loadInt (d.regs.get64 .rsp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 n0.toInt))) :
    reduceFrame mem (d.regs.get64 .rbp) (d.regs.get64 .rsp) (limbBlock modulus 0) n0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [wordsLoaded] using modulus_block_loaded _ mem _ _ modulus blocks 0 h_len h h_pos
  · have he := h.2.2 5 (by decide)
    have hp := initial_memory_preserves d blocks 5 (by decide) (by decide) (by decide)
    simpa using he.trans (hp.trans h_inverse)
  · intro k hk
    have hoff : 112 - 8 * k = 8 * (14 - k) := by omega
    rw [hoff]
    refine ⟨reduction_stack_load d blocks modulus mem h h_map _ (by omega), ?_, ?_⟩
    · intro u hu v hv
      have he := h_disjoint u (by omega) (8 * (14 - k) + v) (by omega)
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
    · exact stack_words_disjoint _ 5 (14 - k) (by decide) (by omega) (by omega)

private structure ReductionContext (d : MachineData) (modulus : List (BitVec 64)) (n0 : BitVec 64) (blocks : Nat) : Prop where
  positive : 0 < blocks
  length : modulus.length = 8 * blocks
  stackBound : (d.regs.get64 .rsp).toNat + 128 * blocks + 64 < 2 ^ 64
  modulusBound : (d.regs.get64 .rbp).toNat + 64 * blocks < 2 ^ 64
  disjoint : modulusStackDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rbp) blocks
  mapped : ∀ j < 16 * blocks + 8, (d.dmem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true
  modulusLoaded : ∀ j < modulus.length, d.dmem.loadInt (d.regs.get64 .rbp + BitVec.ofNat 64 (8 * j)) 8 =
    some (Int.ofBytes (Int.toBytes 8 (modulus.getD j 0).toInt))
  n0Loaded : d.dmem.loadInt (d.regs.get64 .rsp + 40) 8 = some (Int.ofBytes (Int.toBytes 8 n0.toInt))
  inverse : (limbBlock modulus 0).w0 * n0 + 1 = 0
  savedModulus : (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 = d.regs.get64 .rbp
  savedSize : (d.zmms.get (.xmm .mm3)).extractLsb' 0 64 = -BitVec.ofNat 64 (64 * blocks)

private theorem ReductionContext.initial {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks) :
    reductionMemory (reductionInitialMemory d blocks) (reductionInitialMemory d blocks)
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  initial_memory_modulus d modulus blocks h.length h.disjoint h.modulusLoaded

private theorem ReductionContext.prefix {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i ≤ blocks) :
    reductionMemory (reductionInitialMemory d blocks) (sqr8xReductionPrefix d modulus n0 blocks i).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  reduction_prefix_memory d modulus n0 blocks h.length (by have := h.stackBound; omega) h.disjoint h.initial i hi

private theorem ReductionContext.cancel {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i k : Nat) (hi : i < blocks) (hk : k ≤ 8) :
    reductionMemory (reductionInitialMemory d blocks) (cancellationPrefix d modulus n0 blocks i k).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  cancellation_prefix_memory d modulus n0 blocks h.length (by have := h.stackBound; omega) h.disjoint h.initial i k hi hk

private theorem ReductionContext.tailBlocks {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (hi : i < blocks) (hb : b < blocks) :
    reductionMemory (reductionInitialMemory d blocks) (tailBlocksPrefix d modulus n0 blocks i b).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  tail_blocks_prefix_memory d modulus n0 blocks h.length (by have := h.stackBound; omega) h.disjoint h.initial i b hi hb

private theorem ReductionContext.tailIteration {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b k : Nat) (hi : i < blocks) (hb0 : 0 < b) (hb : b < blocks) (hk : k ≤ 8) :
    reductionMemory (reductionInitialMemory d blocks) (tailIterationPrefix d modulus n0 blocks i b k).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus :=
  tail_iteration_prefix_memory d modulus n0 blocks h.length (by have := h.stackBound; omega) h.disjoint h.initial i b k hi hb0 hb hk

private theorem ReductionContext.readBlock {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (mem : DataMem) (hm : reductionMemory (reductionInitialMemory d blocks) mem
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus)
    (j : Nat) (hj : j < 2 * blocks) :
    wordsLoaded mem (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * j))
      (readWords mem (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * j))) := by
  apply read_words_loaded
  intro k hk
  have hoff : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (8 * k) =
      d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + 8 * j + k)) := by
    rw [show 8 * (7 + 8 * j + k) = 56 + 64 * j + 8 * k by omega]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hoff]
  exact reduction_stack_load d blocks modulus mem hm h.mapped _ (by omega)

private theorem ReductionContext.frame {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (mem : DataMem) (hm : reductionMemory (reductionInitialMemory d blocks) mem
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus) :
    reduceFrame mem (d.regs.get64 .rbp) (d.regs.get64 .rsp) (limbBlock modulus 0) n0 :=
  cancellation_frame d blocks modulus n0 mem h.positive h.length (by have := h.stackBound; omega)
    h.disjoint hm h.mapped h.n0Loaded

private theorem outer_entry_loads {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    wordsLoaded (sqr8xReductionPrefix d modulus n0 blocks i).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * i))
      (readWords (sqr8xReductionPrefix d modulus n0 blocks i).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * i))) ∧
    reduceFrame (sqr8xReductionPrefix d modulus n0 blocks i).memory
      (d.regs.get64 .rbp) (d.regs.get64 .rsp) (limbBlock modulus 0) n0 ∧
    ((sqr8xReductionPrefix d modulus n0 blocks i).memory.loadInt
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8).isSome = true ∧
    readWindowDisjoint (d.regs.get64 .rbp) (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 ∧
    readWindowDisjoint (d.regs.get64 .rsp + 40) (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 := by
  have hm := h.prefix i (by omega)
  refine ⟨h.readBlock _ hm i (by omega), h.frame _ hm, ?_, ?_, ?_⟩
  · have hoff : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) =
        d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + 16 * blocks)) := by
      rw [show 8 * (7 + 16 * blocks) = 56 + 128 * blocks by omega]
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    rw [hoff]
    exact reduction_stack_load d blocks modulus _ hm h.mapped _ (by omega)
  · intro u hu v hv
    have he := h.disjoint u (by have := h.positive; omega) (56 + 128 * blocks + v) (by omega)
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
  · have he := stack_words_disjoint (d.regs.get64 .rsp) 5 (7 + 16 * blocks)
        (by decide) (by have := h.stackBound; omega) (by omega)
    simpa [Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem cancellation_prefix_zero (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) :
    (cancellationPrefix d modulus n0 blocks i 0).words =
      readWords (sqr8xReductionPrefix d modulus n0 blocks i).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * i)) ∧
    (cancellationPrefix d modulus n0 blocks i 0).coefficient =
      (cancellationPrefix d modulus n0 blocks i 0).words.w0 * n0 ∧
    (cancellationPrefix d modulus n0 blocks i 0).memory =
      (sqr8xReductionPrefix d modulus n0 blocks i).memory.storeInt
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8
        (sqr8xReductionPrefix d modulus n0 blocks i).carry.toIntOpaque := ⟨rfl, rfl, rfl⟩

@[local grind =] private theorem reduction_input_pointer (sp : BitVec 64) (blocks i : Nat) :
    sp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + -BitVec.ofNat 64 (64 * blocks) =
      sp + 56 + BitVec.ofNat 64 (64 * i) := by
  simp only [Nat.mul_add, BitVec.ofNat_add]
  grind (hom := false)

@[local grind =] private theorem reduction_entry_pointer (sp : BitVec 64) (i : Nat) :
    sp + 56 + BitVec.ofNat 64 (64 * i) + 64 =
      sp + 56 + BitVec.ofNat 64 (64 * (i + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

section
attribute [local irreducible] reductionOuterIndex cancellationOuterIndex sqr8xReductionPrefix
  cancellationPrefix readWords limbBlock reduceCount reduceIndex reduceFrame wordsLoaded
attribute [local grind unfold] reductionOuterInvariant cancellationInvariant
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
local grind_pattern cancellation_prefix_zero => sqr8xReductionPrefix d modulus n0 blocks i
local grind_pattern words_loaded_fields => wordsLoaded mem base w
local grind_pattern reduce_frame_loads => reduceFrame mem mp sp m n0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_entry_establishes [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ reductionOuterInvariant d modulus n0 blocks s ⦄ sqr8x_reduction_entry ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduce" ∧
        cancellationInvariant d modulus n0 blocks s ∧
        s.regs.get64 .rdi = s0.regs.get64 .rdi + s0.regs.get64 .r9 + 64 ⦄ := by
  vcgen [(fun s => sqr8x_reduction_entry_correct s
    (readWords (sqr8xReductionPrefix d modulus n0 blocks
      (reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi))).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 *
        reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)))) (limbBlock modulus 0).w0 n0)]
    simplifying_assumptions with finish (ematch := 16) (splits := 0) (hom := false)
      [reduce_index_initial, reduce_count_initial, → outer_entry_loads h, h.stackBound, → cancellation_outer_index (d.regs.get64 .rsp) blocks]
end



private theorem cancellation_coefficient (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i k : Nat) :
    (cancellationPrefix d modulus n0 blocks i k).coefficient =
      (cancellationPrefix d modulus n0 blocks i k).words.w0 * n0 := by
  cases k <;> rfl

private theorem cancellation_step (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i k : Nat) :
    (cancellationPrefix d modulus n0 blocks i (k + 1)).words =
      sqr8xReduceResult (cancellationPrefix d modulus n0 blocks i k).coefficient (limbBlock modulus 0)
        (cancellationPrefix d modulus n0 blocks i k).words ∧
    (cancellationPrefix d modulus n0 blocks i (k + 1)).memory =
      (cancellationPrefix d modulus n0 blocks i k).memory.storeInt
        (d.regs.get64 .rsp + BitVec.ofNat 64 (112 - 8 * k)) 8
        (cancellationPrefix d modulus n0 blocks i k).coefficient.toIntOpaque := ⟨rfl, rfl⟩

private theorem words_match_reduction (s : MachineData) (w : Sqr8xWords) (h : wordsMatch s w) :
    reductionWords s = w := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [reductionWords, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem cancellation_iteration_result (d s : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i k : Nat)
    (hq : s.regs.get64 .rbx = (cancellationPrefix d modulus n0 blocks i k).coefficient)
    (hw : wordsMatch s (cancellationPrefix d modulus n0 blocks i k).words) :
    reductionResult s (limbBlock modulus 0) = (cancellationPrefix d modulus n0 blocks i (k + 1)).words := by
  simp only [reductionResult, hq, words_match_reduction s _ hw]
  exact (cancellation_step d modulus n0 blocks i k).1.symm

private theorem cancellation_access {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i k : Nat) (hi : i < blocks) (hk : k < 8) :
    reduceFrame (cancellationPrefix d modulus n0 blocks i k).memory
      (d.regs.get64 .rbp) (d.regs.get64 .rsp) (limbBlock modulus 0) n0 ∧
    (limbBlock modulus 0).w0 * (cancellationPrefix d modulus n0 blocks i k).coefficient +
      (cancellationPrefix d modulus n0 blocks i k).words.w0 = 0 := by
  refine ⟨h.frame _ (h.cancel i k hi (by omega)), ?_⟩
  rw [cancellation_coefficient]
  exact reduce_coefficient_cancels _ _ _ h.inverse

private theorem reduction_metadata {d modulus n0 blocks} (_h : ReductionContext d modulus n0 blocks)
    (mem : DataMem) (hm : reductionMemory (reductionInitialMemory d blocks) mem
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus) :
    mem.loadInt (d.regs.get64 .rsp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toInt)) ∧
    mem.loadInt (d.regs.get64 .rsp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toInt)) :=
  ⟨(hm.2.2 1 (by decide)).trans (initial_memory_ends d blocks).1,
   (hm.2.2 2 (by decide)).trans (initial_memory_ends d blocks).2⟩

private theorem cancellation_coefficients {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i j : Nat) (hi : i < blocks) (hj : j < 9) :
    (cancellationPrefix d modulus n0 blocks i 8).memory.loadInt
      (d.regs.get64 .rsp + BitVec.ofNat 64 (112 - 8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 ((passCoefficients d modulus n0 blocks i).getD j 0).toInt)) := by
  apply saved_coefficient_load _ _ _ hj
  have hoff : 112 - 8 * j = 8 * (14 - j) := by omega
  rw [hoff]
  exact reduction_stack_load d blocks modulus _ (h.cancel i 8 hi (by decide)) h.mapped _ (by have := h.positive; omega)

private theorem tail_blocks_coefficients {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b j : Nat) (hi : i < blocks) (hb : b < blocks) (hj : j < 9) :
    (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt
      (d.regs.get64 .rsp + BitVec.ofNat 64 (112 - 8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 ((passCoefficients d modulus n0 blocks i).getD j 0).toInt)) := by
  have hoff : 112 - 8 * j = 8 * (14 - j) := by omega
  have hp := tail_blocks_preserve_stack_prefix modulus (passCoefficients d modulus n0 blocks i)
    (d.regs.get64 .rsp) blocks i
    ⟨(cancellationPrefix d modulus n0 blocks i 8).words, 0, (cancellationPrefix d modulus n0 blocks i 8).memory⟩
    (by have := h.stackBound; omega) hi b (14 - j) hb (by omega)
  change (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt _ _ = _ at hp
  rw [← hoff] at hp
  exact hp.trans (cancellation_coefficients h i j hi hj)

private theorem tail_iteration_coefficients {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b k j : Nat) (hi : i < blocks) (hb0 : 0 < b) (hb : b < blocks) (hk : k ≤ 8) (hj : j < 9) :
    (tailIterationPrefix d modulus n0 blocks i b k).memory.loadInt
      (d.regs.get64 .rsp + BitVec.ofNat 64 (112 - 8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 ((passCoefficients d modulus n0 blocks i).getD j 0).toInt)) := by
  have hoff : 112 - 8 * j = 8 * (14 - j) := by omega
  dsimp only [tailIterationPrefix]
  rw [hoff, tail_preserves_stack_prefix _ _ _ blocks i b _ (by have := h.stackBound; omega) hi hb0 hb k (14 - j) hk (by omega)]
  rw [← hoff]
  exact tail_blocks_coefficients h i (b - 1) j hi (by omega) hj

private theorem tail_iteration_frame {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b k : Nat) (hi : i < blocks) (hb0 : 0 < b) (hb : b < blocks) (hk : k ≤ 8) :
    tailFrame (tailIterationPrefix d modulus n0 blocks i b k).memory
      (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b)) (d.regs.get64 .rsp)
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)))
      (limbBlock modulus b) (passCoefficients d modulus n0 blocks i) := by
  have hm := h.tailIteration i b k hi hb0 hb hk
  refine ⟨?_, ?_, ?_⟩
  · exact modulus_block_loaded _ _ _ _ _ blocks b h.length hm hb
  · intro j hj
    have he := tail_iteration_coefficients h i b k (j + 1) hi hb0 hb hk (by omega)
    simpa [show 112 - 8 * (j + 1) = 104 - 8 * j by omega] using he
  · intro j hj
    have hoff : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * j) =
        d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + 8 * (i + b) + j)) := by
      rw [show 8 * (7 + 8 * (i + b) + j) = 56 + 64 * (i + b) + 8 * j by omega]
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    rw [hoff]
    refine ⟨reduction_stack_load d blocks modulus _ hm h.mapped _ (by omega), ?_, ?_⟩
    · intro u hu v hv
      have he := h.disjoint (64 * b + u) (by omega) (8 * (7 + 8 * (i + b) + j) + v) (by omega)
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
    · intro a ha
      have he := stack_words_disjoint (d.regs.get64 .rsp) (13 - a) (7 + 8 * (i + b) + j)
        (by have := h.stackBound; omega) (by have := h.stackBound; omega) (by omega)
      have haeq : 104 - 8 * a = 8 * (13 - a) := by omega
      simpa [haeq] using he

private def cancellationDone (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let i := cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)
  let r := cancellationPrefix d modulus n0 blocks i 8
  i < blocks ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)) ∧
  wordsMatch s r.words ∧ s.dmem = r.memory

private theorem cancellation_tail_access {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    reduceFrame (cancellationPrefix d modulus n0 blocks i 8).memory
      (d.regs.get64 .rbp) (d.regs.get64 .rsp) (limbBlock modulus 0) n0 ∧
    (cancellationPrefix d modulus n0 blocks i 8).memory.loadInt (d.regs.get64 .rsp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toInt)) ∧
    (cancellationPrefix d modulus n0 blocks i 8).memory.loadInt (d.regs.get64 .rsp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toInt)) ∧
    (1 < blocks → wordsLoaded (cancellationPrefix d modulus n0 blocks i 8).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)))
      (readWords (cancellationPrefix d modulus n0 blocks i 8).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)))) ∧
      (cancellationPrefix d modulus n0 blocks i 8).memory.loadInt (d.regs.get64 .rsp + 112) 8 =
        some (Int.ofBytes (Int.toBytes 8 ((passCoefficients d modulus n0 blocks i).getD 0 0).toInt)) ∧
      (cancellationPrefix d modulus n0 blocks i 8).memory.loadInt (d.regs.get64 .rbp + 64) 8 =
        some (Int.ofBytes (Int.toBytes 8 (limbBlock modulus 1).w0.toInt))) := by
  have hm := h.cancel i 8 hi (by decide)
  refine ⟨h.frame _ hm, (reduction_metadata h _ hm).1, (reduction_metadata h _ hm).2, ?_⟩
  intro hb
  exact ⟨h.readBlock _ hm (i + 1) (by omega), cancellation_coefficients h i 0 hi (by decide),
    by simpa using (words_loaded_fields _ _ _ (modulus_block_loaded _ _ _ _ _ blocks 1 h.length hm hb)).1⟩

private theorem tail_blocks_zero (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) :
    (tailBlocksPrefix d modulus n0 blocks i 0).words = (cancellationPrefix d modulus n0 blocks i 8).words ∧
    (tailBlocksPrefix d modulus n0 blocks i 0).carry = 0 ∧
    (tailBlocksPrefix d modulus n0 blocks i 0).memory = (cancellationPrefix d modulus n0 blocks i 8).memory := ⟨rfl, rfl, rfl⟩

private theorem tail_iteration_zero (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i b : Nat) :
    (tailIterationPrefix d modulus n0 blocks i b 0).words = (tailBlockSum d modulus n0 blocks i b).1 ∧
    (tailIterationPrefix d modulus n0 blocks i b 0).coefficient = (passCoefficients d modulus n0 blocks i).getD 0 0 ∧
    (tailIterationPrefix d modulus n0 blocks i b 0).memory = (tailBlocksPrefix d modulus n0 blocks i (b - 1)).memory := ⟨rfl, rfl, rfl⟩

private theorem first_tail_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) :
    (tailIterationPrefix d modulus n0 blocks i 1 0).memory =
      (cancellationPrefix d modulus n0 blocks i 8).memory := rfl

private theorem first_tail_sum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) :
    tailBlockSum d modulus n0 blocks i 1 = sqr8xAddResult (cancellationPrefix d modulus n0 blocks i 8).words
      (readWords (cancellationPrefix d modulus n0 blocks i 8).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)))) false := rfl

private theorem pass_carry_single (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (i : Nat) :
    (passCarrySum d modulus n0 1 i).1 = (cancellationPrefix d modulus n0 1 i 8).words ∧
    (passCarrySum d modulus n0 1 i).2 = false := by
  simp only [passCarrySum]
  exact ⟨rfl, rfl⟩

private theorem cancellation_tail_pointers {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    ((d.regs.get64 .rbp + 64).toNat < (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toNat ↔ 1 < blocks) ∧
    reductionBlockIndex (d.regs.get64 .rbp) (d.regs.get64 .rbp + 64) = 1 ∧
    tailOuterIndex (d.regs.get64 .rsp)
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1))) 1 0 = i ∧
    (blocks = 1 → reductionOuterIndex (d.regs.get64 .rsp) blocks
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1))) = i) := by
  have h1 := modulus_pointer_nat (d.regs.get64 .rbp) blocks 1 (by omega) h.modulusBound
  have hb := modulus_pointer_nat (d.regs.get64 .rbp) blocks blocks (by omega) h.modulusBound
  refine ⟨by change (d.regs.get64 .rbp + 64).toNat = _ at h1; omega, ?_, ?_, ?_⟩
  · exact reduction_block_index _ blocks 1 (by omega) h.modulusBound
  · by_cases hsingle : blocks = 1
    · have hi0 : i = 0 := by omega
      subst i
      simp only [tailOuterIndex, BitVec.toNat_add, BitVec.toNat_ofNat]
      have hb := h.stackBound
      simp only [show (56 : BitVec 64).toNat = 56 from rfl] at *
      omega
    · simpa using tail_outer_index (d.regs.get64 .rsp) blocks i 1 0 hi (by omega) (by decide) h.stackBound
  · intro he
    subst blocks
    simpa [Nat.add_comm] using reduction_outer_index (d.regs.get64 .rsp) 1 i (by omega) h.stackBound

private theorem tail_invariant_intro {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b k : Nat) (s : MachineData) (hi : i < blocks) (hb0 : 0 < b) (hb : b < blocks) (hk : k < 8)
    (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp) (hz : s.zmms = d.zmms)
    (hbp : s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b))
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k))
    (hcx : s.regs.get64 .rcx = reduceCount k) (ha : s.regs.get64 .rax = (limbBlock modulus b).w0)
    (hsi : s.regs.get64 .rsi = -(BitVec.ofNat 64 (tailBlockSum d modulus n0 blocks i b).2.toNat))
    (hq : s.regs.get64 .rbx = (tailIterationPrefix d modulus n0 blocks i b k).coefficient)
    (hw : wordsMatch s (tailIterationPrefix d modulus n0 blocks i b k).words)
    (hm : s.dmem = (tailIterationPrefix d modulus n0 blocks i b k).memory) :
    reductionTailInvariant d modulus n0 blocks s := by
  have hbi : reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp) = b := by
    rw [hbp]; exact reduction_block_index _ blocks b (by omega) h.modulusBound
  have hki : reduceIndex (s.regs.get64 .rcx) = k := by
    rw [hcx]; exact (reduce_counter_facts k (by omega)).2.1
  have hii : tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi) b k = i := by
    rw [hdi]; exact tail_outer_index _ blocks i b k hi hb (by omega) h.stackBound
  simp only [reductionTailInvariant, hbi, hki, hii]
  exact ⟨hi, hb0, hb, hk, hsp, hz, hbp, hdi, hcx, ha, hsi, hq, hw, hm⟩

private theorem first_tail_intro {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (s : MachineData) (hi : i < blocks) (hb : 1 < blocks)
    (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp) (hz : s.zmms = d.zmms)
    (hbp : s.regs.get64 .rbp = d.regs.get64 .rbp + 64)
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)))
    (hcx : s.regs.get64 .rcx = 8) (ha : s.regs.get64 .rax = (limbBlock modulus 1).w0)
    (hsi : s.regs.get64 .rsi = -(BitVec.ofNat 64 (tailBlockSum d modulus n0 blocks i 1).2.toNat))
    (hq : s.regs.get64 .rbx = (passCoefficients d modulus n0 blocks i).getD 0 0)
    (hw : wordsMatch s (tailBlockSum d modulus n0 blocks i 1).1)
    (hm : s.dmem = (cancellationPrefix d modulus n0 blocks i 8).memory) :
    reductionTailInvariant d modulus n0 blocks s := by
  apply tail_invariant_intro h i 1 0 s hi (by decide) hb (by decide) hsp hz hbp
    (by simpa using hdi) hcx ha hsi hq hw hm

private theorem single_finish_intro {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (s : MachineData) (hi : i < blocks) (hb : blocks = 1)
    (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp) (hz : s.zmms = d.zmms)
    (hbp : s.regs.get64 .rbp = d.regs.get64 .rbp + 64)
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + 1)))
    (hdx : s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks))
    (ha : s.regs.get64 .rax = 0) (hcf : s.status.cf = false)
    (hw : wordsMatch s (cancellationPrefix d modulus n0 blocks i 8).words)
    (hm : s.dmem = (cancellationPrefix d modulus n0 blocks i 8).memory) :
    reductionFinishInvariant d modulus n0 blocks s := by
  subst blocks
  have hii : reductionOuterIndex (d.regs.get64 .rsp) 1 (s.regs.get64 .rdi) = i := by
    rw [hdi]
    simpa [Nat.add_comm] using reduction_outer_index (d.regs.get64 .rsp) 1 i (by omega) h.stackBound
  simp only [reductionFinishInvariant, hii]
  exact ⟨hi, hsp, hz, hbp, by simpa [Nat.add_comm] using hdi, hdx, ha, hcf, hw, hm⟩

section
attribute [local irreducible] reductionOuterIndex cancellationOuterIndex reductionBlockIndex tailOuterIndex
  sqr8xReductionPrefix cancellationPrefix tailBlocksPrefix tailBlockSum tailIterationPrefix passCarrySum
  passCoefficients sqr8xAddResult readWords limbBlock reduceCount reduceIndex reduceFrame wordsLoaded
attribute [local grind unfold] cancellationDone
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern words_match_reduction => reductionWords s, w.w0
local grind_pattern words_loaded_fields => wordsLoaded mem base w
local grind_pattern tail_blocks_zero => cancellationPrefix d modulus n0 blocks i 8
local grind_pattern tail_iteration_zero => tailIterationPrefix d modulus n0 blocks i b 0
local grind_pattern first_tail_sum => tailBlockSum d modulus n0 blocks i 1
local grind_pattern pass_carry_single => passCarrySum d modulus n0 1 i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_tail_establishes [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ cancellationDone d modulus n0 blocks s ⦄ sqr8x_reduce_tail ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rdi = s0.regs.get64 .rdi ∧
        s.regs.get64 .rbp = s0.regs.get64 .rbp + 64 ∧
        ((pc = (_root_.Executable.labels cenv).label ".L8x_tail" ∧ reductionTailInvariant d modulus n0 blocks s) ∨
        (pc = (_root_.Executable.labels cenv).label ".L8x_no_tail" ∧ reductionFinishInvariant d modulus n0 blocks s)) ⦄ := by
  vcgen [(fun s => sqr8x_reduce_tail_correct s
    (readWords (cancellationPrefix d modulus n0 blocks
      (cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)) 8).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 *
        (cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi) + 1))))
    (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks))
    (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) (limbBlock modulus 1).w0
    ((passCoefficients d modulus n0 blocks (cancellationOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi))).getD 0 0))]
    simplifying_assumptions with finish (ematch := 16) (splits := 4) (hom := false) only
      [BitVec.toNat_ofNat, = BitVec.toNat_ofNatLT, words_match_reduction, → words_loaded_fields, tail_blocks_zero, tail_iteration_zero, first_tail_sum, first_tail_memory, pass_carry_single,
        reduce_index_initial, reduce_count_initial, h.positive, h.stackBound, h.modulusBound,
        → cancellation_tail_access h,
        → cancellation_tail_pointers h, → first_tail_intro h, → single_finish_intro h]
end



private def reductionTailDone (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  let b := reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)
  let i := tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi) b 8
  let r := tailBlocksPrefix d modulus n0 blocks i b
  i < blocks ∧ 0 < b ∧ b < blocks ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1)) ∧
  s.regs.get64 .rsi = r.carry ∧ wordsMatch s r.words ∧ s.dmem = r.memory

private theorem tail_advance_access {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (hi : i < blocks) (_hb0 : 0 < b) (hb : b < blocks) :
    (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt (d.regs.get64 .rsp + 8) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toInt)) ∧
    (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt (d.regs.get64 .rsp + 16) 8 =
      some (Int.ofBytes (Int.toBytes 8 (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toInt)) ∧
    (b + 1 < blocks → wordsLoaded (tailBlocksPrefix d modulus n0 blocks i b).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1)))
      (readWords (tailBlocksPrefix d modulus n0 blocks i b).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1)))) ∧
      (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt (d.regs.get64 .rsp + 112) 8 =
        some (Int.ofBytes (Int.toBytes 8 ((passCoefficients d modulus n0 blocks i).getD 0 0).toInt)) ∧
      (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt
        (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * (b + 1))) 8 =
        some (Int.ofBytes (Int.toBytes 8 (limbBlock modulus (b + 1)).w0.toInt))) := by
  have hm := h.tailBlocks i b hi hb
  refine ⟨(reduction_metadata h _ hm).1, (reduction_metadata h _ hm).2, ?_⟩
  intro hb1
  exact ⟨h.readBlock _ hm (i + b + 1) (by omega), tail_blocks_coefficients h i b 0 hi hb (by decide),
    by simpa using (words_loaded_fields _ _ _ (modulus_block_loaded _ _ _ _ _ blocks (b + 1) h.length hm hb1)).1⟩

private theorem tail_advance_pointers {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (hi : i < blocks) (_hb0 : 0 < b) (hb : b < blocks) :
    d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) + 64 =
      d.regs.get64 .rbp + BitVec.ofNat 64 (64 * (b + 1)) ∧
    ((d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) + 64).toNat <
      (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks)).toNat ↔ b + 1 < blocks) ∧
    reductionBlockIndex (d.regs.get64 .rbp) (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) + 64) = b + 1 ∧
    (b + 1 < blocks → tailOuterIndex (d.regs.get64 .rsp)
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1))) (b + 1) 0 = i) ∧
    (b + 1 = blocks → reductionOuterIndex (d.regs.get64 .rsp) blocks
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1))) = i) := by
  have hp : d.regs.get64 .rbp + BitVec.ofNat 64 (64 * b) + 64 =
      d.regs.get64 .rbp + BitVec.ofNat 64 (64 * (b + 1)) := by
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · rw [hp, modulus_pointer_nat _ blocks (b + 1) (by omega) h.modulusBound,
      modulus_pointer_nat _ blocks blocks (by omega) h.modulusBound]
    omega
  · rw [hp]
    exact reduction_block_index _ blocks (b + 1) (by omega) h.modulusBound
  · intro hb1
    simpa [Nat.add_assoc] using tail_outer_index (d.regs.get64 .rsp) blocks i (b + 1) 0 hi hb1 (by decide) h.stackBound
  · intro he
    have hoff : i + b + 1 = blocks + i := by omega
    rw [hoff]
    exact reduction_outer_index _ blocks i (by omega) h.stackBound

private theorem tail_next_memory (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i b : Nat) :
    (tailIterationPrefix d modulus n0 blocks i (b + 1) 0).memory =
      (tailBlocksPrefix d modulus n0 blocks i b).memory := by
  simp only [tailIterationPrefix, Nat.add_sub_cancel, sqr8xTailFold]

private theorem tail_next_sum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i b : Nat) :
    tailBlockSum d modulus n0 blocks i (b + 1) =
      sqr8xAddResult (tailBlocksPrefix d modulus n0 blocks i b).words
        (readWords (tailBlocksPrefix d modulus n0 blocks i b).memory
          (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1))))
        ((tailBlocksPrefix d modulus n0 blocks i b).carry != 0) := by
  simp only [tailBlockSum, Nat.add_sub_cancel, Nat.add_assoc]

private theorem next_tail_intro {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (s : MachineData) (hi : i < blocks) (hb0 : 0 < b) (hb : b + 1 < blocks)
    (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp) (hz : s.zmms = d.zmms)
    (hbp : s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * (b + 1)))
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1)))
    (hcx : s.regs.get64 .rcx = 8) (ha : s.regs.get64 .rax = (limbBlock modulus (b + 1)).w0)
    (hsi : s.regs.get64 .rsi = -(BitVec.ofNat 64 (tailBlockSum d modulus n0 blocks i (b + 1)).2.toNat))
    (hq : s.regs.get64 .rbx = (passCoefficients d modulus n0 blocks i).getD 0 0)
    (hw : wordsMatch s (tailBlockSum d modulus n0 blocks i (b + 1)).1)
    (hm : s.dmem = (tailBlocksPrefix d modulus n0 blocks i b).memory) :
    reductionTailInvariant d modulus n0 blocks s := by
  apply tail_invariant_intro h i (b + 1) 0 s hi (by omega) hb (by decide) hsp hz hbp
    (by simpa [Nat.add_assoc] using hdi) hcx ha hsi hq hw
  simpa only [tailIterationPrefix, sqr8xTailFold, Nat.add_sub_cancel] using hm

private theorem tail_done_intro {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (s : MachineData) (hi : i < blocks) (hb0 : 0 < b) (hb : b + 1 = blocks)
    (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp) (hz : s.zmms = d.zmms)
    (hbp : s.regs.get64 .rbp = d.regs.get64 .rbp + BitVec.ofNat 64 (64 * (b + 1)))
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1)))
    (hdx : s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks))
    (hsi : s.regs.get64 .rsi = (tailBlocksPrefix d modulus n0 blocks i b).carry)
    (hw : wordsMatch s (tailBlocksPrefix d modulus n0 blocks i b).words)
    (hm : s.dmem = (tailBlocksPrefix d modulus n0 blocks i b).memory) :
    reductionCarryInvariant d modulus n0 blocks s := by
  have hoff : i + b + 1 = blocks + i := by omega
  rw [hoff] at hdi
  have hii : reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi) = i := by
    rw [hdi]; exact reduction_outer_index _ blocks i (by omega) h.stackBound
  have hb' : blocks - 1 = b := by omega
  simp only [reductionCarryInvariant, hii, hb']
  exact ⟨hi, by omega, hsp, hz, by simpa [hb] using hbp, hdi, hdx, hsi, hw, hm⟩

section
attribute [local irreducible] reductionOuterIndex reductionBlockIndex tailOuterIndex
  tailBlocksPrefix tailBlockSum tailIterationPrefix passCoefficients sqr8xAddResult readWords limbBlock reduceCount reduceIndex wordsLoaded
attribute [local grind unfold] reductionTailDone
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern words_match_reduction => reductionWords s, w.w0
local grind_pattern words_loaded_fields => wordsLoaded mem base w
local grind_pattern tail_iteration_zero => tailIterationPrefix d modulus n0 blocks i b 0
local grind_pattern tail_next_sum => tailBlocksPrefix d modulus n0 blocks i b

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem tail_advance_establishes [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ reductionTailDone d modulus n0 blocks s ⦄ sqr8x_tail_advance ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rdi = s0.regs.get64 .rdi ∧
        s.regs.get64 .rbp = s0.regs.get64 .rbp + 64 ∧
        ((pc = (_root_.Executable.labels cenv).label ".L8x_tail" ∧ reductionTailInvariant d modulus n0 blocks s) ∨
        (pc = (_root_.Executable.labels cenv).label ".L8x_tail_done" ∧ reductionCarryInvariant d modulus n0 blocks s)) ⦄ := by
  vcgen [(fun s => sqr8x_tail_advance_correct s
    (readWords (tailBlocksPrefix d modulus n0 blocks
      (tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)
        (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)) 8)
      (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp))).memory (s.regs.get64 .rdi))
    (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks))
    (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks))
    (limbBlock modulus (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp) + 1)).w0
    ((passCoefficients d modulus n0 blocks (tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)
      (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)) 8)).getD 0 0))]
    simplifying_assumptions with finish (ematch := 16) (splits := 4) (hom := false) only
      [BitVec.toNat_ofNat, = BitVec.toNat_ofNatLT, words_match_reduction, → words_loaded_fields, tail_iteration_zero, tail_next_sum, tail_next_memory,
        reduce_index_initial, reduce_count_initial, h.positive, h.stackBound, h.modulusBound,
        → tail_advance_access h, → tail_advance_pointers h, → next_tail_intro h, → tail_done_intro h]
end



private theorem cancellation_saved_carry {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i k : Nat) (hi : i < blocks) (hk : k ≤ 8) :
    (cancellationPrefix d modulus n0 blocks i k).memory.loadInt
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (sqr8xReductionPrefix d modulus n0 blocks i).carry.toInt)) := by
  dsimp only [cancellationPrefix]
  rw [reduce_fold_load]
  · exact Mem.loadInt_storeInt _ _ _ _ (by decide)
  · intro j hj
    have hoff : 112 - 8 * j = 8 * (14 - j) := by omega
    have he := stack_words_disjoint (d.regs.get64 .rsp) (7 + 16 * blocks) (14 - j)
      (by have := h.stackBound; omega) (by omega) (by have := h.positive; omega)
    simpa [readWindowDisjoint, hoff, Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem tail_preserves_end (m : Sqr8xWords) (q : List (BitVec 64)) (sp : BitVec 64)
    (blocks i b : Nat) (initial : Sqr8xReduceState)
    (h_bound : 128 * blocks + 64 < 2 ^ 64) (hi : i < blocks) (hb : b < blocks)
    (k : Nat) (hk : k ≤ 8) :
    (sqr8xTailFold m q (sp + 56 + BitVec.ofNat 64 (64 * (i + b))) initial k).memory.loadInt
      (sp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 =
      initial.memory.loadInt (sp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 := by
  apply tail_fold_load
  intro j hj
  have he := stack_words_disjoint sp (7 + 16 * blocks) (7 + 8 * (i + b) + j)
    (by omega) (by omega) (by omega)
  simpa [readWindowDisjoint, Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem tail_blocks_preserve_end (modulus q : List (BitVec 64)) (sp : BitVec 64)
    (blocks i : Nat) (initial : Sqr8xBlockState)
    (h_bound : 128 * blocks + 64 < 2 ^ 64) (hi : i < blocks)
    (b : Nat) (hb : b < blocks) :
    (sqr8xTailBlocksFold modulus q sp i initial b).memory.loadInt
      (sp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 =
      initial.memory.loadInt (sp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    dsimp only [sqr8xTailBlocksFold, sqr8xTailBlockStep]
    rw [show i + b + 1 = i + (b + 1) by omega]
    rw [tail_preserves_end _ q sp blocks i (b + 1) ⟨_, _, _⟩ h_bound hi hb 8 (by decide)]
    exact ih (by omega)

private theorem tail_blocks_saved_carry {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b : Nat) (hi : i < blocks) (hb : b < blocks) :
    (tailBlocksPrefix d modulus n0 blocks i b).memory.loadInt
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (sqr8xReductionPrefix d modulus n0 blocks i).carry.toInt)) := by
  dsimp only [tailBlocksPrefix]
  rw [tail_blocks_preserve_end _ _ _ blocks i _ (by have := h.stackBound; omega) hi b hb]
  exact cancellation_saved_carry h i 8 hi (by decide)

private theorem pass_carry_multiple (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) (hb : 1 < blocks) :
    passCarrySum d modulus n0 blocks i = sqr8xAddResult
      (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).words
      ⟨(sqr8xReductionPrefix d modulus n0 blocks i).carry, 0, 0, 0, 0, 0, 0, 0⟩ false := by
  simp only [passCarrySum, ite_eq_right (by omega : blocks ≠ 1)]

private theorem tail_final_saved_carry {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory.loadInt
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (sqr8xReductionPrefix d modulus n0 blocks i).carry.toInt)) :=
  tail_blocks_saved_carry h i (blocks - 1) hi (by omega)

section
attribute [local irreducible] reductionOuterIndex sqr8xReductionPrefix tailBlocksPrefix passCarrySum sqr8xAddResult
attribute [local grind unfold] reductionCarryInvariant reductionFinishInvariant
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern words_match_reduction => reductionWords s, w.w0
local grind_pattern pass_carry_multiple => passCarrySum d modulus n0 blocks i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_carry_establishes [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ reductionCarryInvariant d modulus n0 blocks s ⦄ sqr8x_tail_carry
    ⦃ fun _ s => reductionFinishInvariant d modulus n0 blocks s ∧ s.regs.get64 .rdi = s0.regs.get64 .rdi ⦄ := by
  vcgen [(fun s => sqr8x_tail_carry_correct s
    (sqr8xReductionPrefix d modulus n0 blocks
      (reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi))).carry)]
    simplifying_assumptions with finish (ematch := 16) (splits := 0) (hom := false)
      [→ tail_final_saved_carry h]
end

private theorem reduction_return {d modulus n0 blocks} (_h : ReductionContext d modulus n0 blocks)
    (s : MachineData) (hs : s.regs.get64 .rsp = d.regs.get64 .rsp)
    (hm : reductionMemory (reductionInitialMemory d blocks) s.dmem
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus) : s.retAddr = d.retAddr := by
  have he := hm.2.2 0 (by decide)
  have hp := initial_memory_preserves d blocks 0 (by decide) (by decide) (by decide)
  simp only [MachineData.retAddr, hs]
  congr 1
  simpa [Width.bytes] using he.trans hp

private theorem reduction_finish_access {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    wordsLoaded (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)))
      (readWords (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)))) ∧
    (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory.loadInt
      (d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks) + (-8#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 ((modulus.getD (8 * blocks - 1) 0).toInt))) ∧
    returnDisjoint (d.regs.get64 .rsp) (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i))) ∧
    reductionMemory (reductionInitialMemory d blocks) (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory
      (d.regs.get64 .rsp) (d.regs.get64 .rbp) modulus := by
  have hm := h.tailBlocks i (blocks - 1) hi (by omega)
  refine ⟨h.readBlock _ hm (blocks + i) (by omega), ?_, ?_, hm⟩
  · have he := hm.2.1 (8 * blocks - 1) (by have := h.length; omega)
    have hoff : d.regs.get64 .rbp + BitVec.ofNat 64 (64 * blocks) + (-8#64) =
        d.regs.get64 .rbp + BitVec.ofNat 64 (8 * (8 * blocks - 1)) := by
      have hn : 8 * (8 * blocks - 1) + 8 = 64 * blocks := by omega
      rw [← hn, BitVec.ofNat_add]
      grind (hom := false)
    rw [hoff]
    exact he
  · intro j hj
    have he := stack_words_disjoint (d.regs.get64 .rsp) 0 (7 + 8 * (blocks + i) + j)
      (by decide) (by have := h.stackBound; omega) (by omega)
    simpa [Nat.mul_add, ← Nat.mul_assoc, BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem reduction_finish_pointers {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i : Nat) (hi : i < blocks) :
    ((d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + 64).toNat <
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)).toNat ↔ i + 1 < blocks) ∧
    reductionOuterIndex (d.regs.get64 .rsp) blocks
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + 64) = i + 1 ∧
    (i + 1 = blocks → d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + 64 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks)) ∧
    d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + 64 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + (i + 1))) := by
  have hp : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i)) + 64 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + (i + 1))) := by
    rw [show 64 * (blocks + (i + 1)) = 64 * (blocks + i) + 64 by omega, BitVec.ofNat_add]
    simp [BitVec.add_assoc]
  rw [hp]
  have h1 := reduction_pointer_nat (d.regs.get64 .rsp) blocks (blocks + (i + 1)) 0 (by omega) (by decide) h.stackBound
  have h2 := reduction_pointer_nat (d.regs.get64 .rsp) blocks (2 * blocks) 0 (by omega) (by decide) h.stackBound
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at h1 h2
  refine ⟨?_, reduction_outer_index _ blocks (i + 1) (by omega) h.stackBound, ?_, rfl⟩
  · have he : 64 * (2 * blocks) = 128 * blocks := by omega
    rw [he] at h2
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (56 : BitVec 64).toNat = 56 from rfl]
    have := h.stackBound
    omega
  · intro he
    rw [he, show 64 * (blocks + blocks) = 128 * blocks by omega]

private def reductionResultPost (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData) : Prop :=
  s.regs.get64 .rsp = d.regs.get64 .rsp + 8 ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧ s.regs.get64 .r9 = -BitVec.ofNat 64 (64 * blocks) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rsi = 0 ∧ s.regs.get64 .rax = (sqr8xReductionPrefix d modulus n0 blocks blocks).carry ∧
  s.dmem = (sqr8xReductionPrefix d modulus n0 blocks blocks).memory

private theorem pass_finish_sum (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i : Nat) :
    passFinishSum d modulus n0 blocks i =
      sqr8xAddResult (passCarrySum d modulus n0 blocks i).1
        (readWords (tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).memory
          (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks + i))))
        ((tailBlocksPrefix d modulus n0 blocks i (blocks - 1)).carry != 0) := by
  simp only [passFinishSum, Nat.add_comm blocks i]

section
attribute [local irreducible] reductionOuterIndex sqr8xReductionPrefix tailBlocksPrefix passCarrySum passFinishSum
  sqr8xAddResult readWords reductionMemory wordsLoaded returnDisjoint
attribute [local grind unfold] reductionFinishInvariant reductionOuterInvariant reductionResultPost
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern words_match_reduction => reductionWords s, w.w0
local grind_pattern reduction_prefix_step => passFinishSum d modulus n0 blocks pass
local grind_pattern pass_finish_sum => passFinishSum d modulus n0 blocks i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_finish_establishes [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (ra : Int64) (h : ReductionContext d modulus n0 blocks)
    (hret : d.retAddr = some ra) :
    ⦃ fun s => s = s0 ∧ reductionFinishInvariant d modulus n0 blocks s ⦄ sqr8x_reduction_finish ⦃ fun _ _ => False;
      fun pc s => s.regs.get64 .rdi = s0.regs.get64 .rdi + 64 ∧
        ((pc = (_root_.Executable.labels cenv).label ".L8x_reduction_loop" ∧ reductionOuterInvariant d modulus n0 blocks s) ∨
        (pc = ra ∧ reductionResultPost d modulus n0 blocks s)) ⦄ := by
  vcgen [(fun s => sqr8x_reduction_finish_correct s
    (readWords (tailBlocksPrefix d modulus n0 blocks
      (reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)) (blocks - 1)).memory
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (blocks +
        reductionOuterIndex (d.regs.get64 .rsp) blocks (s.regs.get64 .rdi)))))
    (Int.ofBytes (Int.toBytes 8 ((modulus.getD (8 * blocks - 1) 0).toInt))) ra)]
    simplifying_assumptions with finish (ematch := 16) (splits := 16) only
      [BitVec.toNat_ofNat, = BitVec.toNat_ofNatLT, words_match_reduction, reduction_prefix_step, pass_finish_sum,
        → reduction_finish_access h, → reduction_finish_pointers h, → reduction_return h,
        h.savedModulus, h.savedSize]
end



private theorem tail_iteration_step (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i b k : Nat) :
    (tailIterationPrefix d modulus n0 blocks i b (k + 1)).words =
      sqr8xReduceResult (tailIterationPrefix d modulus n0 blocks i b k).coefficient (limbBlock modulus b)
        (tailIterationPrefix d modulus n0 blocks i b k).words ∧
    (tailIterationPrefix d modulus n0 blocks i b (k + 1)).coefficient =
      (passCoefficients d modulus n0 blocks i).getD (k + 1) 0 ∧
    (tailIterationPrefix d modulus n0 blocks i b (k + 1)).memory =
      (tailIterationPrefix d modulus n0 blocks i b k).memory.storeInt
        (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k)) 8
        (sqr4xMac (limbBlock modulus b).w0 (tailIterationPrefix d modulus n0 blocks i b k).coefficient
          (tailIterationPrefix d modulus n0 blocks i b k).words.w0 0).1.toIntOpaque := ⟨rfl, rfl, rfl⟩

private theorem tail_iteration_result (d s : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks i b k : Nat)
    (hq : s.regs.get64 .rbx = (tailIterationPrefix d modulus n0 blocks i b k).coefficient)
    (hw : wordsMatch s (tailIterationPrefix d modulus n0 blocks i b k).words) :
    reductionResult s (limbBlock modulus b) = (tailIterationPrefix d modulus n0 blocks i b (k + 1)).words := by
  simp only [reductionResult, hq, words_match_reduction s _ hw]
  exact (tail_iteration_step d modulus n0 blocks i b k).1.symm

private theorem tail_iteration_pointers {d modulus n0 blocks} (h : ReductionContext d modulus n0 blocks)
    (i b k : Nat) (hi : i < blocks) (_hb0 : 0 < b) (hb : b < blocks) (hk : k < 8) :
    tailOuterIndex (d.regs.get64 .rsp)
      (d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k) + 8) b (k + 1) = i ∧
    d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k) + 8 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * (k + 1)) ∧
    (k + 1 = 8 → d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k) + 8 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b + 1))) := by
  have hp : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * k) + 8 =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (64 * (i + b)) + BitVec.ofNat 64 (8 * (k + 1)) := by
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨?_, hp, ?_⟩
  · rw [hp]
    exact tail_outer_index _ blocks i b (k + 1) hi hb (by omega) h.stackBound
  · intro he
    rw [hp, he]
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

section Sqr8xReductionCycles
attribute [local irreducible] reductionOuterIndex cancellationOuterIndex reductionBlockIndex tailOuterIndex
  sqr8xReductionPrefix cancellationPrefix tailBlocksPrefix tailBlockSum tailIterationPrefix passCarrySum passFinishSum
  passCoefficients sqr8xAddResult readWords limbBlock sqr8xReduceResult reduceCount reduceIndex reduceFrame tailFrame wordsLoaded
attribute [local grind unfold] reductionOuterInvariant cancellationInvariant cancellationDone
  reductionTailInvariant reductionTailDone reductionCarryInvariant reductionFinishInvariant reductionResultPost
attribute [local sym_simp] BitVec.zero_add CondCode.interp_nz StatusFlags.zf_from_result Option.map_none Option.map_some
attribute [local grind norm] set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind =] reduce_counter_address cancellation_coefficient
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern reduce_counter_facts => reduceCount j
local grind_pattern reduce_counter_step => (reduceCount j).setWidth 32 - 1
local grind_pattern reduce_counter_next => (reduceCount j).setWidth 32 - 1
local grind_pattern reduce_frame_loads => reduceFrame mem mp sp m n0
local grind_pattern reduce_frame_slot => reduceFrame mem mp sp m n0, reduceCount j
local grind_pattern cancellation_iteration_result => reductionResult s (limbBlock modulus 0), cancellationPrefix d modulus n0 blocks i k
local grind_pattern cancellation_step => cancellationPrefix d modulus n0 blocks i k, reduceCount k
local grind_pattern tail_frame_loads => tailFrame mem mp sp out m q
local grind_pattern tail_frame_slot => tailFrame mem mp sp out m q, reduceCount j
local grind_pattern tail_iteration_result => reductionResult s (limbBlock modulus b), tailIterationPrefix d modulus n0 blocks i b k
local grind_pattern tail_iteration_step => tailIterationPrefix d modulus n0 blocks i b k, reduceCount k
local grind_pattern tail_block_prefix_step => tailIterationPrefix d modulus n0 blocks pass b 8


set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem cancellation_cycle_correct [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ cancellationInvariant d modulus n0 blocks s ⦄ sqr8x_reduce_cycle
    ⦃ fun _ s => cancellationDone d modulus n0 blocks s ∧ s.regs.get64 .rdi = s0.regs.get64 .rdi ∧
        reduceIndex (s0.regs.get64 .rcx) + 1 = 8;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduce" ∧
        cancellationInvariant d modulus n0 blocks s ∧ s.regs.get64 .rdi = s0.regs.get64 .rdi ∧
        reduceIndex (s.regs.get64 .rcx) = reduceIndex (s0.regs.get64 .rcx) + 1 ⦄ := by
  vcgen [sqr8x_reduce_cycle, sqr8x_reduce_iteration_correct (m := limbBlock modulus 0) (n0 := n0)]
    simplifying_assumptions with finish (ematch := 16) (splits := 4) (hom := false)
      [→ cancellation_access h]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem tail_cycle_correct [CodeEnv] (d s0 : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ reductionTailInvariant d modulus n0 blocks s ⦄ sqr8x_tail_cycle
    ⦃ fun _ s => reductionTailDone d modulus n0 blocks s ∧
        s.regs.get64 .rbp = s0.regs.get64 .rbp ∧ s.regs.get64 .rdi = s0.regs.get64 .rdi + 8 ∧
        reduceIndex (s0.regs.get64 .rcx) + 1 = 8;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_tail" ∧
        reductionTailInvariant d modulus n0 blocks s ∧
        s.regs.get64 .rbp = s0.regs.get64 .rbp ∧ s.regs.get64 .rdi = s0.regs.get64 .rdi + 8 ∧
        reduceIndex (s.regs.get64 .rcx) = reduceIndex (s0.regs.get64 .rcx) + 1 ⦄ := by
  vcgen [sqr8x_tail_cycle, (fun s => sqr8x_tail_iteration_correct s
    (limbBlock modulus (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)))
    ((passCoefficients d modulus n0 blocks (tailOuterIndex (d.regs.get64 .rsp) (s.regs.get64 .rdi)
      (reductionBlockIndex (d.regs.get64 .rbp) (s.regs.get64 .rbp)) (reduceIndex (s.regs.get64 .rcx)))).getD
      (reduceIndex (s.regs.get64 .rcx) + 1) 0))]
    simplifying_assumptions with finish (ematch := 16) (splits := 16)
      [h.stackBound, h.modulusBound, → tail_iteration_frame h, → tail_iteration_pointers h]
end Sqr8xReductionCycles


section Sqr8xReductionCFG
attribute [local irreducible] reductionOuterIndex cancellationOuterIndex reductionBlockIndex tailOuterIndex
  sqr8xReductionPrefix cancellationPrefix tailBlocksPrefix tailBlockSum tailIterationPrefix passCarrySum passFinishSum
  passCoefficients sqr8xAddResult readWords limbBlock sqr8xReduceResult reduceCount reduceIndex reduceFrame tailFrame wordsLoaded
attribute [local grind unfold] reductionOuterInvariant cancellationInvariant cancellationDone
  reductionTailInvariant reductionTailDone reductionCarryInvariant reductionFinishInvariant reductionResultPost
attribute [local sym_simp] BitVec.zero_add CondCode.interp_nz StatusFlags.zf_from_result Option.map_none Option.map_some
attribute [local grind norm] Option.map_none Option.map_some set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  CondCode.interp_nz StatusFlags.zf_from_result
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x

variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr8x_reduction_prog)]
local instance : CodeEnv := ⟨layout sqr8x_reduction_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
/-- The complete nested reduction CFG against its arithmetic fold, including
coefficient storage, every tail block, carry propagation, and return. -/
theorem sqr8x_reduction_prog_correct (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (ra : Int64) (h : ReductionContext d modulus n0 blocks)
    (h_size : d.regs.get64 .r9 = BitVec.ofNat 64 (64 * blocks)) (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ sqr8x_reduction_prog ⦃ fun _ _ => False;
      fun pc s => pc = ra ∧ reductionResultPost d modulus n0 blocks s ⦄ := by
  apply MachineWP.cfg_exit (reductionTable d modulus n0 blocks) (reductionVar d blocks)
  cfg_cases [reduction_view]
  · vcgen [reduction_setup_establishes d modulus n0 blocks h.positive h.stackBound h_size] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.positive, h.stackBound, h.mapped 1, h.mapped 2,
        reduction_initial_index (d.regs.get64 .rsp) blocks h.stackBound]
  · vcgen [(fun s => reduction_entry_establishes d s modulus n0 blocks h)] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.stackBound, reduce_index_initial,
        → cancellation_outer_index (d.regs.get64 .rsp) blocks]
  · vcgen [(fun s => cancellation_cycle_correct d s modulus n0 blocks h),
        (fun s => reduction_tail_establishes d s modulus n0 blocks h)] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.stackBound, h.modulusBound, h.positive,
        → cancellation_tail_pointers h]
  · vcgen [(fun s => tail_cycle_correct d s modulus n0 blocks h),
        (fun s => tail_advance_establishes d s modulus n0 blocks h)] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.stackBound, h.modulusBound, h.positive,
        → tail_iteration_pointers h, → tail_advance_pointers h]
  · vcgen [(fun s => reduction_carry_establishes d s modulus n0 blocks h)] simplifying_assumptions with
      finish (splits := 16)
  · vcgen [(fun s => reduction_finish_establishes d s modulus n0 blocks ra h hret)] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.stackBound, h.positive, → reduction_finish_pointers h]
end Sqr8xReductionCFG


end Sqr8xFullReduction

section Sqr8xFullSquaring

open Std Std.ExtHashMap

/-- The limb array currently stored in a mapped region. -/
private def snapshotLimbs (mem : DataMem) (a : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun i => readWord mem (a + BitVec.ofNat 64 (8 * i)))

private theorem snapshot_length (mem : DataMem) (a : BitVec 64) (n : Nat) :
    (snapshotLimbs mem a n).length = n := by simp [snapshotLimbs]

private theorem snapshot_cons (mem : DataMem) (a : BitVec 64) (n : Nat) :
    snapshotLimbs mem a (n + 1) = readWord mem a :: snapshotLimbs mem (a + 8) n := by
  simp only [snapshotLimbs, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  dsimp only [Function.comp_def]
  congr 1
  simp only [Nat.mul_succ, BitVec.ofNat_add]
  grind

private theorem snapshot_bytes (mem : DataMem) (a : BitVec 64) (n : Nat)
    (bs : List UInt8) (R : DataMem → Prop) (hlen : bs.length = 8 * n)
    (hb : 8 * n ≤ 2 ^ 64) (hm : mem =⋆ Eq (bs.At a) ⋆ R) :
    (snapshotLimbs mem a n).flatMap (fun w => Int.toBytes 8 w.toInt) = bs := by
  induction n generalizing a bs R with
  | zero =>
    have he : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [snapshotLimbs, he]
  | succ n ih =>
    have hfirst : (bs.take 8).length = 8 := by simp only [List.length_take]; omega
    have hrest : (bs.drop 8).length = 8 * n := by simp only [List.length_drop]; omega
    have hs : mem =⋆ Eq ((bs.take 8).At a) ⋆ (Eq ((bs.drop 8).At (a + 8)) ⋆ R) := by
      conv at hm => arg 1; arg 1; arg 1; rw [← List.take_append_drop 8 bs]
      rw [Mem.At_append_sep _ _ _ (by simp; omega), hfirst, sep_assoc] at hm
      exact hm
    have hl := Mem.loadInt_sep _ a 8 _ mem hs hfirst (by decide)
    have ht := ih (a + 8) (bs.drop 8) (Eq ((bs.take 8).At a) ⋆ R) hrest (by omega)
      (by simpa only [sep_comm_l] using hs)
    rw [snapshot_cons, List.flatMap_cons, ht]
    have he : Int.toBytes 8 (readWord mem a).toInt = bs.take 8 := by
      simp only [readWord, hl, Option.getD_some, BitVec.toInt_ofInt]
      exact Int.toBytes_bmod_ofBytes 8 (bs.take 8) hfirst
    rw [he, List.take_append_drop]

private theorem snapshot_block (mem : DataMem) (a : BitVec 64) (n : Nat)
    (R : DataMem → Prop) (hm : mem =⋆ Mem.Block a (8 * n) ⋆ R) :
    mem =⋆ Eq (((snapshotLimbs mem a n).flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆ R := by
  obtain ⟨hb, bs, hlen, hs⟩ := Mem.Block.sep_elim hm
  rw [snapshot_bytes mem a n bs R hlen hb hs]
  exact hs

private theorem limb_slice (xs : List (BitVec 64)) (a : BitVec 64) (j n : Nat)
    (hj : j + n ≤ xs.length) (hb : 8 * xs.length ≤ 2 ^ 64) :
    Eq ((xs.flatMap fun w => Int.toBytes 8 w.toInt).At a) =
      Eq ((((xs.drop j).take n).flatMap fun w => Int.toBytes 8 w.toInt).At
        (a + BitVec.ofNat 64 (8 * j))) ⋆
      (Eq (((xs.take j).flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
        Eq (((xs.drop (j + n)).flatMap fun w => Int.toBytes 8 w.toInt).At
          (a + BitVec.ofNat 64 (8 * (j + n))))) := by
  have hs : xs = xs.take j ++ (xs.drop j).take n ++ xs.drop (j + n) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hpre : ((xs.take j).flatMap fun w => Int.toBytes 8 w.toInt).length = 8 * j := by
    rw [length_flatMap_limbs, List.length_take]; omega
  have hmid : (((xs.drop j).take n).flatMap fun w => Int.toBytes 8 w.toInt).length = 8 * n := by
    rw [length_flatMap_limbs, List.length_take, List.length_drop]; omega
  conv => lhs; arg 1; arg 1; rw [hs, List.flatMap_append, List.flatMap_append]
  rw [Mem.At_append3_sep _ _ _ a (by
    rw [hpre, hmid, length_flatMap_limbs, List.length_drop]; omega), hpre, hmid]
  rw [Nat.mul_add]

private theorem sep_two_windows (P A Q B R : DataMem → Prop) :
    (P ⋆ A) ⋆ ((Q ⋆ B) ⋆ R) = P ⋆ (Q ⋆ (A ⋆ (B ⋆ R))) := by ac_rfl

private theorem frame_windows (mem : DataMem) (x : List (BitVec 64))
    (a b : BitVec 64) (len xi xn ti tn : Nat) (R : DataMem → Prop)
    (hx : xi + xn ≤ x.length) (ht : ti + tn ≤ len)
    (hb : 8 * x.length ≤ 2 ^ 64)
    (hm : mem =⋆ Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At a) ⋆
      (Mem.Block b (8 * len) ⋆ R)) :
    ∃ F : DataMem → Prop, mem =⋆
      Eq ((((x.drop xi).take xn).flatMap fun w => Int.toBytes 8 w.toInt).At
        (a + BitVec.ofNat 64 (8 * xi))) ⋆
      (Eq (((((snapshotLimbs mem b len).drop ti).take tn).flatMap fun w => Int.toBytes 8 w.toInt).At
        (b + BitVec.ofNat 64 (8 * ti))) ⋆ F) := by
  have hm' := hm
  rw [sep_comm_l] at hm'
  have hw := (Mem.Block.sep_elim hm').1
  have hs := snapshot_block mem b len _ hm'
  rw [sep_comm_l] at hs
  rw [limb_slice x a xi xn hx hb, limb_slice (snapshotLimbs mem b len) b ti tn
    (by rw [snapshot_length]; exact ht) (by rw [snapshot_length]; exact hw)] at hs
  rw [sep_two_windows] at hs
  exact ⟨_, hs⟩


/-- Reference states at phase boundaries. Only registers consumed by the next
phase are set; the reference computation itself is the arithmetic folds above. -/
private def firstSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let r := sqr4xFirstPreambleResult d (4 * blocks - 2) x
  { d with
    regs := d.regs |>.set64 .rsi (d.regs.get64 .rsi + d.regs.get64 .r9)
      |>.set64 .rdi (d.regs.get64 .rsp + d.regs.get64 .r9 + 56)
      |>.set64 .rbp (32 - d.regs.get64 .r9) |>.set64 .rcx (32 - d.regs.get64 .r9)
      |>.set64 .r14 (x.getD 0 0) |>.set64 .r15 (x.getD 1 0)
      |>.set64 .rax r.previous |>.set64 .r11 r.carry0 |>.set64 .r13 r.carry1
    dmem := r.memory }

private def firstDoneSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := firstSeed d x blocks
  let n := 4 * blocks - 2
  let r := sqr4xInnerPrefix s n (x.drop 4) (List.replicate (2 * n) 0) n
  { s with
    regs := s.regs |>.set64 .rcx 0 |>.set64 .rax r.previous
      |>.set64 .r11 r.carry0 |>.set64 .r13 r.carry1
    dmem := r.memory }

private def outerSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := firstDoneSeed d x blocks
  let r := firstTailResult s
  { s with
    regs := s.regs |>.set64 .rbp (s.regs.get64 .rbp + 16)
      |>.set64 .r13 r.1 |>.set64 .r12 r.2
    dmem := (s.dmem.storeInt (s.regs.get64 .rdi) 8 r.1.toIntOpaque).storeInt
      (s.regs.get64 .rdi + 8) 8 r.2.toIntOpaque }

private def outerAccumulator (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : List (BitVec 64) :=
  ((snapshotLimbs (outerSeed d x blocks).dmem (d.regs.get64 .rsp + 56)
    (16 * blocks + 1)).drop 4).take (16 * blocks - 4)

private def productsSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := outerSeed d x blocks
  let n := 4 * blocks - 3
  let r := sqr4xOuterPrefix s n (x.drop 2) (outerAccumulator d x blocks) n
  { s with
    regs := s.regs |>.set64 .rbp 0 |>.set64 .rcx 0
      |>.set64 .r10 (r.limbs.getD (4 * n + 1) 0)
      |>.set64 .r13 (r.limbs.getD (4 * n + 2) 0)
      |>.set64 .r12 (r.limbs.getD (4 * n + 3) 0)
    dmem := r.memory }

private def diagonalSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := productsSeed d x blocks
  let r := sqr4xFinalProducts (x.getD (8 * blocks - 4) 0) (x.getD (8 * blocks - 3) 0)
    (x.getD (8 * blocks - 2) 0) (x.getD (8 * blocks - 1) 0)
    (s.regs.get64 .r10) (s.regs.get64 .r13) (s.regs.get64 .r12)
  let base := finalProductBase s
  { s with
    regs := s.regs |>.set64 .rbp (16 - s.regs.get64 .r9)
      |>.set64 .rdi (base + 24) |>.set64 .r14 0 |>.set64 .r15 0
    dmem := ((((((((s.dmem.storeInt (base + 0) 8 r.1.w1.toIntOpaque).storeInt
      (base + 8) 8 r.1.w2.toIntOpaque).storeInt (base + 16) 8 r.1.w3.toIntOpaque).storeInt
      (base + 24) 8 r.1.w4.toIntOpaque).storeInt (base + 32) 8 r.2.toIntOpaque).storeInt
      (base + 32) 8 r.1.w5.toIntOpaque).storeInt (base + 40) 8 r.1.w6.toIntOpaque).storeInt
      (base + 48) 8 r.1.w7.toIntOpaque) }

private def shiftSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := diagonalSeed d x blocks
  let t := snapshotLimbs s.dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)
  let r := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0)
    (t.getD 2 0) (t.getD 3 0) 0 0
  { s with
    regs := s.regs |>.set64 .rbp (s.regs.get64 .rbp + 16)
      |>.set64 .rdi (s.regs.get64 .rsp + 120) |>.set64 .rax (x.getD 2 0)
      |>.set64 .r10 (t.getD 4 0) |>.set64 .r11 (t.getD 5 0)
      |>.set64 .r14 r.2.shiftCarry |>.set64 .r15 r.2.addCarry
    dmem := (((s.dmem.storeInt (s.regs.get64 .rsp + 56) 8 r.1.lo.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 64) 8 r.1.hi.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 72) 8 r.2.lo.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 80) 8 r.2.hi.toIntOpaque }

private def shiftAccumulator (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : List (BitVec 64) :=
  ((snapshotLimbs (shiftSeed d x blocks).dmem (d.regs.get64 .rsp + 56)
    (16 * blocks + 1)).drop 4).take (16 * blocks - 4)

private def shiftDoneSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := shiftSeed d x blocks
  let n := 2 * blocks - 1
  let t := shiftAccumulator d x blocks
  let r := sqr4xShiftPrefix s (x.drop 2) t n
  { s with
    regs := s.regs |>.set64 .rbp 0 |>.set64 .rcx 0
      |>.set64 .rdi (s.regs.get64 .rdi + BitVec.ofNat 64 (64 * n))
      |>.set64 .rax ((x.drop 2).getD (4 * n) 0)
      |>.set64 .r10 (t.getD (8 * n) 0) |>.set64 .r11 (t.getD (8 * n + 1) 0)
      |>.set64 .r14 r.shiftCarry |>.set64 .r15 r.addCarry
    dmem := r.memory }

private def reductionSeed (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : MachineData :=
  let s := shiftDoneSeed d x blocks
  let t := shiftAccumulator d x blocks
  let n := 2 * blocks - 1
  let r := sqr4xDiagonalPair (s.regs.get64 .rax) (x.getD (8 * blocks - 1) 0)
    (s.regs.get64 .r10) (s.regs.get64 .r11) (t.getD (8 * n + 2) 0)
    (t.getD (8 * n + 3) 0) (s.regs.get64 .r14) (s.regs.get64 .r15)
  { s with
    regs := s.regs |>.set64 .rbp ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64)
    dmem := (((s.dmem.storeInt (s.regs.get64 .rdi + (-32#64)) 8 r.1.lo.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-24#64)) 8 r.1.hi.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-16#64)) 8 r.2.lo.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-8#64)) 8 r.2.hi.toIntOpaque }

/-- Full arithmetic-fold specification: first cross-products, the nested outer
loop, the remaining products, doubled cross-products plus diagonal squares,
and every reduction pass. This specifies the internal routine before the
caller's separate final conditional subtraction. -/
def bnSqr8xResult (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : Sqr8xReductionState :=
  sqr8xReductionPrefix (reductionSeed d x blocks) modulus n0 blocks blocks


/-- A finite sequence of limb stores within a workspace. This records only
where the reference folds write, and is independent of their arithmetic. -/
private inductive WorkspaceWrites (base : BitVec 64) (limbs : Nat) : DataMem → DataMem → Prop
  | refl (mem) : WorkspaceWrites base limbs mem mem
  | store {initial mem} (previous : WorkspaceWrites base limbs initial mem)
      (i : Nat) (hi : i < limbs) (v : Int) :
      WorkspaceWrites base limbs initial (mem.storeInt (base + BitVec.ofNat 64 (8 * i)) 8 v)

private theorem WorkspaceWrites.trans {base : BitVec 64} {limbs : Nat} {a b c : DataMem}
    (hab : WorkspaceWrites base limbs a b) (hbc : WorkspaceWrites base limbs b c) :
    WorkspaceWrites base limbs a c := by
  induction hbc with
  | refl => exact hab
  | store _ i hi v ih => exact ih.store i hi v

private theorem WorkspaceWrites.shift {base : BitVec 64} {offset len total : Nat} {a b : DataMem}
    (h : WorkspaceWrites (base + BitVec.ofNat 64 (8 * offset)) len a b)
    (hb : offset + len ≤ total) : WorkspaceWrites base total a b := by
  induction h with
  | refl => exact .refl _
  | store _ i hi v ih =>
    have hs := ih.store (offset + i) (by omega) v
    simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc] using hs

private theorem WorkspaceWrites.frame {base : BitVec 64} {limbs : Nat} {a b : DataMem}
    (h : WorkspaceWrites base limbs a b) (R : DataMem → Prop)
    (hm : a =⋆ Mem.Block base (8 * limbs) ⋆ R) : b =⋆ Mem.Block base (8 * limbs) ⋆ R := by
  have hb := (Mem.Block.sep_elim hm).1
  induction h with
  | refl => exact hm
  | store _ i hi v ih =>
    apply Mem.Block.storeInt ih _ v
    simp only [BitVec.add_comm base, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    omega

private theorem inner_fold_writes (a0 a1 : BitVec 64) (x t : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr4xInnerState) (k len : Nat) (hk : 2 * k ≤ len) :
    WorkspaceWrites base len initial.memory (sqr4xInnerFold a0 a1 x t base initial k).memory := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    dsimp only [sqr4xInnerFold]
    have hs := (ih (by omega)).store (2 * k) (by omega)
    have hs' (v : Int) := (hs v).store (2 * k + 1) (by omega)
    simpa [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc,
      show 8 * (2 * k) = 16 * k by omega] using hs' _ _

private theorem outer_preamble_writes (x : List (BitVec 64)) (base : BitVec 64)
    (n i : Nat) (hi : i < n) (initial : Sqr4xOuterState) :
    WorkspaceWrites (base - BitVec.ofNat 64 (32 * n + 64)) (4 * n + 8) initial.memory
      (sqr4xOuterPreambleStep x base n i initial).memory := by
  dsimp only [sqr4xOuterPreambleStep]
  have addr (j : Nat) : base + innerOffset n i + (-32#64) + innerOffset n i +
      (-32#64 + BitVec.ofNat 64 (8 * j)) =
      (base - BitVec.ofNat 64 (32 * n + 64)) + BitVec.ofNat 64 (8 * (4 * i + j)) := by
    simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]
    grind
  have h1 := (WorkspaceWrites.refl (base := base - BitVec.ofNat 64 (32 * n + 64))
    (limbs := 4 * n + 8) initial.memory).store (4 * i + 1) (by omega)
  have h2 (v : Int) := (h1 v).store (4 * i + 2) (by omega)
  have h3 (v w : Int) := (h2 v w).store (4 * i + 3) (by omega)
  simpa [← addr, BitVec.reduceAdd] using h3 _ _ _

private theorem outer_inner_writes (x : List (BitVec 64)) (base : BitVec 64)
    (n i : Nat) (_hi : i < n) (initial : Sqr4xOuterInnerState) (k : Nat) (hk : i + k ≤ n) :
    WorkspaceWrites (base - BitVec.ofNat 64 (32 * n + 64)) (4 * n + 8) initial.memory
      (sqr4xOuterInnerFold x base n i initial k).memory := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    dsimp only [sqr4xOuterInnerFold, sqr4xOuterInnerStep]
    have addr (j : Nat) : base + innerOffset n i + (-32#64) + innerOffset n (i + k) +
        BitVec.ofNat 64 (8 * j) =
        (base - BitVec.ofNat 64 (32 * n + 64)) + BitVec.ofNat 64 (8 * (2 * i + 2 * (i + k) + 4 + j)) := by
      simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]
      grind
    have h1 := (ih (by omega)).store (2 * i + 2 * (i + k) + 4 + 0) (by omega)
    have h2 (v : Int) := (h1 v).store (2 * i + 2 * (i + k) + 4 + 1) (by omega)
    simpa only [← addr, Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h2 _ _

private theorem outer_fold_writes (x : List (BitVec 64)) (base : BitVec 64)
    (n : Nat) (initial : Sqr4xOuterState) (k : Nat) (hk : k ≤ n) :
    WorkspaceWrites (base - BitVec.ofNat 64 (32 * n + 64)) (4 * n + 8) initial.memory
      (sqr4xOuterFold x base n initial k).memory := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    have hp := outer_preamble_writes x base n k (by omega) (sqr4xOuterFold x base n initial k)
    have hi := outer_inner_writes x base n k (by omega)
      (sqr4xOuterPreambleStep x base n k (sqr4xOuterFold x base n initial k)) (n - k) (by omega)
    dsimp only [sqr4xOuterFold, sqr4xOuterTailStep]
    have addr (j : Nat) : base + innerOffset n k + (-32#64) + BitVec.ofNat 64 (8 * j) =
        (base - BitVec.ofNat 64 (32 * n + 64)) + BitVec.ofNat 64 (8 * (2 * k + 2 * n + 4 + j)) := by
      simp only [innerOffset, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]
      grind
    have h1 := ((ih (by omega)).trans (hp.trans hi)).store (2 * k + 2 * n + 4 + 0) (by omega)
    have h2 (v : Int) := (h1 v).store (2 * k + 2 * n + 4 + 1) (by omega)
    simpa only [← addr, Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h2 _ _

private theorem store_words_writes (base : BitVec 64) (len i : Nat) (hi : i + 8 ≤ len)
    (mem : DataMem) (w : Sqr8xWords) :
    WorkspaceWrites base len mem (storeSqr8xWords mem (base + BitVec.ofNat 64 (8 * i)) w) := by
  have h (m : DataMem) (j : Nat) (hj : j < 8) (v : Int)
      (hm : WorkspaceWrites base len mem m) :
      WorkspaceWrites base len mem
        (m.storeInt (base + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (8 * j)) 8 v) := by
    simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc] using hm.store (i + j) (by omega) v
  exact h _ 7 (by decide) _ (h _ 6 (by decide) _ (h _ 5 (by decide) _ (h _ 4 (by decide) _
    (h _ 3 (by decide) _ (h _ 2 (by decide) _ (h _ 1 (by decide) _ (h _ 0 (by decide) _ (.refl _))))))))

private theorem shift_fold_writes (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xShiftState) (k len : Nat) (hk : 8 * k ≤ len) :
    WorkspaceWrites base len initial.memory (sqr4xShiftFold x t base initial k).memory := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    exact (ih (by omega)).trans (by
      simpa only [sqr4xShiftFold, show 8 * (8 * k) = 64 * k by omega] using
        store_words_writes base len (8 * k) (by omega) _ _)


/-- Calling convention and owned memory for the complete internal routine.
All sizes are expressed using `x.length`; `n0` is the negated low-word inverse.
`workspace` separates the input limbs at `%rsi`, the modulus limbs at `%xmm2`,
and the stack frame at `%rsp` (with `n0` at `40(%rsp)`). -/
structure BnSqr8xContext (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) : Prop where
  positive : 0 < x.length
  /-- The number of limbs must be a multiple of eight. -/
  inputMultiple : 8 ∣ x.length
  modulusLength : modulus.length = x.length
  size : d.regs.get64 .r9 = BitVec.ofNat 64 (8 * x.length)
  offset : d.regs.get64 .r10 = -d.regs.get64 .r9
  sizeBound : 16 * x.length + 64 < 2 ^ 63
  stackBound : (d.regs.get64 .rsp).toNat + 16 * x.length + 64 < 2 ^ 64
  modulusBound : ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64).toNat + 8 * x.length < 2 ^ 64
  /-- `n0` is the negated modular inverse `-M⁻¹ mod 2^64` (`M * n0 ≡ -1 (mod 2^64)`),
  so adding `(t0 * n0) * M` cancels the low word `t0`. Higher limbs of
  `M = BnSqr8x.limbsToNat modulus` vanish modulo `2^64`. -/
  inverse : modulus.getD 0 0 * n0 + 1 = 0
  savedSize : (d.zmms.get (.xmm .mm3)).extractLsb' 0 64 = -BitVec.ofNat 64 (8 * x.length)
  workspace : ∃ R : DataMem → Prop,
    d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At (d.regs.get64 .rsi)) ⋆
      (Eq ((modulus.flatMap fun w => Int.toBytes 8 w.toInt).At
        ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64)) ⋆
      (Mem.Block (d.regs.get64 .rsp) 40 ⋆
      (Eq ((Int.toBytes 8 n0.toInt).At (d.regs.get64 .rsp + 40)) ⋆
      (Mem.Block (d.regs.get64 .rsp + 48) (8 * (2 * x.length + 2)) ⋆ R))))

/-- Block-count form of `BnSqr8xContext` used by the implementation proofs.
Each block contains eight limbs. -/
structure BnSqr8xBlockContext (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : Prop where
  positive : 0 < blocks
  inputLength : x.length = 8 * blocks
  modulusLength : modulus.length = 8 * blocks
  size : d.regs.get64 .r9 = BitVec.ofNat 64 (64 * blocks)
  offset : d.regs.get64 .r10 = -d.regs.get64 .r9
  sizeBound : 128 * blocks + 64 < 2 ^ 63
  stackBound : (d.regs.get64 .rsp).toNat + 128 * blocks + 64 < 2 ^ 64
  modulusBound : ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64).toNat + 64 * blocks < 2 ^ 64
  inverse : modulus.getD 0 0 * n0 + 1 = 0
  savedSize : (d.zmms.get (.xmm .mm3)).extractLsb' 0 64 = -BitVec.ofNat 64 (64 * blocks)
  workspace : ∃ R : DataMem → Prop,
    d.dmem =⋆
      Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At (d.regs.get64 .rsi)) ⋆
      (Eq ((modulus.flatMap fun w => Int.toBytes 8 w.toInt).At
        ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64)) ⋆
      (Mem.Block (d.regs.get64 .rsp) 40 ⋆
      (Eq ((Int.toBytes 8 n0.toInt).At (d.regs.get64 .rsp + 40)) ⋆
      (Mem.Block (d.regs.get64 .rsp + 48) (8 * (16 * blocks + 2)) ⋆ R))))

private theorem BnSqr8xContext.toBlockContext {d x modulus n0}
    (h : BnSqr8xContext d x modulus n0) :
    BnSqr8xBlockContext d x modulus n0 (x.length / 8) := by
  obtain ⟨blocks, h_len⟩ := h.inputMultiple
  have h_blocks : x.length / 8 = blocks := by omega
  rw [h_blocks]
  exact {
    positive := by have := h.positive; omega
    inputLength := h_len
    modulusLength := h.modulusLength.trans h_len
    size := by simpa [h_len, ← Nat.mul_assoc] using h.size
    offset := h.offset
    sizeBound := by simpa [h_len, ← Nat.mul_assoc] using h.sizeBound
    stackBound := by simpa [h_len, ← Nat.mul_assoc] using h.stackBound
    modulusBound := by simpa [h_len, ← Nat.mul_assoc] using h.modulusBound
    inverse := h.inverse
    savedSize := by simpa [h_len, ← Nat.mul_assoc] using h.savedSize
    workspace := by simpa [h_len, ← Nat.mul_assoc] using h.workspace }

private theorem block_append {a : BitVec 64} {len1 len2 : Nat} {F : DataMem → Prop} {m : DataMem}
    (hw : len1 + len2 ≤ 2 ^ 64)
    (h : m =⋆ Mem.Block a len1 ⋆ (Mem.Block (a + BitVec.ofNat 64 len1) len2 ⋆ F)) :
    m =⋆ Mem.Block a (len1 + len2) ⋆ F := by
  obtain ⟨_, bs1, rfl, h1⟩ := Mem.Block.sep_elim h
  rw [sep_comm_l] at h1
  obtain ⟨_, bs2, rfl, h2⟩ := Mem.Block.sep_elim h1
  rw [sep_comm_l, ← sep_assoc, ← Mem.At_append_sep bs1 bs2 a hw] at h2
  exact Mem.Block.sep_intro (List.length_append ..) hw h2

private theorem block_split {a : BitVec 64} {len1 len2 : Nat} {F : DataMem → Prop} {m : DataMem}
    (h : m =⋆ Mem.Block a (len1 + len2) ⋆ F) :
    m =⋆ Mem.Block a len1 ⋆ (Mem.Block (a + BitVec.ofNat 64 len1) len2 ⋆ F) := by
  obtain ⟨hw, bs, hlen, h'⟩ := Mem.Block.sep_elim h
  have hbs : bs = bs.take len1 ++ bs.drop len1 := (List.take_append_drop len1 bs).symm
  have ht : (bs.take len1).length = len1 := by simp only [List.length_take]; omega
  have hd : (bs.drop len1).length = len2 := by simp only [List.length_drop]; omega
  rw [hbs, Mem.At_append_sep _ _ a (by omega), ht, sep_assoc] at h'
  apply Mem.Block.sep_intro ht (by omega)
  rw [sep_comm_l]
  apply Mem.Block.sep_intro hd (by omega)
  rw [sep_comm_l]
  exact h'

private theorem sep_rot4 (A B C D E R : DataMem → Prop) :
    A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ R)))) = D ⋆ (C ⋆ (E ⋆ (B ⋆ (A ⋆ R)))) := by ac_rfl

private theorem sep_ws_frame (A B C D R : DataMem → Prop) :
    A ⋆ (B ⋆ (C ⋆ (D ⋆ R))) = D ⋆ (B ⋆ (A ⋆ (C ⋆ R))) := by ac_rfl

private theorem BnSqr8xBlockContext.n0Loaded {d x modulus n0 blocks}
    (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    d.dmem.loadInt (d.regs.get64 .rsp + 40) 8 =
      some (Int.ofBytes (Int.toBytes 8 n0.toInt)) := by
  obtain ⟨R, hw⟩ := h.workspace
  rw [sep_rot4] at hw
  exact Mem.loadInt_sep _ _ 8 _ _ hw (Int.toBytes_length 8 n0.toInt) (by decide)

private theorem BnSqr8xBlockContext.stack {d x modulus n0 blocks}
    (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∃ R : DataMem → Prop, d.dmem =⋆
      Mem.Block (d.regs.get64 .rsp) (128 * blocks + 64) ⋆
      (Eq ((modulus.flatMap fun w => Int.toBytes 8 w.toInt).At
        ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64)) ⋆
      (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At (d.regs.get64 .rsi)) ⋆ R)) := by
  have h_size_bound := h.sizeBound
  obtain ⟨R, hw⟩ := h.workspace
  rw [sep_rot4] at hw
  have hw2 := Mem.Block.sep_intro (Int.toBytes_length 8 n0.toInt) (by decide) hw
  rw [sep_comm_l] at hw2
  have hw3 := block_append (by decide) hw2
  have h48 : 8 * (16 * blocks + 2) = 128 * blocks + 16 := by omega
  have ha48 : d.regs.get64 .rsp + 48 = d.regs.get64 .rsp + BitVec.ofNat 64 (40 + 8) := rfl
  rw [h48, ha48] at hw3
  have hw4 := block_append (by omega) hw3
  exact ⟨R, by simpa only [show 40 + 8 + (128 * blocks + 16) = 128 * blocks + 64 by omega] using hw4⟩

private theorem BnSqr8xBlockContext.disjoint {d x modulus n0 blocks}
    (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    modulusStackDisjoint (d.regs.get64 .rsp)
      ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64) blocks := by
  obtain ⟨R, hstack⟩ := h.stack
  obtain ⟨_, bs, hlen, hstack'⟩ := Mem.Block.sep_elim hstack
  rw [sep_comm_l] at hstack'
  have h_mod_len := h.modulusLength
  intro i hi j hj
  exact sep_At_ne hstack' i (by rw [length_flatMap_limbs, h_mod_len]; omega) j (by omega)

private theorem BnSqr8xBlockContext.mapped {d x modulus n0 blocks}
    (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∀ j < 16 * blocks + 8,
      (d.dmem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true := by
  obtain ⟨R, hstack⟩ := h.stack
  intro j hj
  apply Mem.Block.loadInt_isSome hstack
  rw [BitVec.add_comm (d.regs.get64 .rsp), BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := h.sizeBound
  omega

private def squareMemory (d : MachineData) (x modulus : List (BitVec 64))
    (blocks : Nat) (mem : DataMem) : Prop :=
  (∃ R : DataMem → Prop, mem =⋆
    Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At (d.regs.get64 .rsi)) ⋆
      (Mem.Block (d.regs.get64 .rsp + 56) (8 * (16 * blocks + 1)) ⋆ R)) ∧
  reductionMemory d.dmem mem (d.regs.get64 .rsp)
    ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64) modulus

private theorem BnSqr8xBlockContext.memory {d x modulus n0 blocks}
    (h : BnSqr8xBlockContext d x modulus n0 blocks) : squareMemory d x modulus blocks d.dmem := by
  obtain ⟨R, hstack⟩ := h.stack
  have h_mod_len := h.modulusLength
  have h_size_bound := h.sizeBound
  refine ⟨?_, Mem.SubDom.refl _, ?_, fun _ _ => rfl⟩
  · have hsplit : 128 * blocks + 64 = 56 + 8 * (16 * blocks + 1) := by omega
    rw [hsplit] at hstack
    have hws := block_split hstack
    rw [sep_ws_frame] at hws
    exact ⟨_, hws⟩
  · rw [sep_comm_l] at hstack
    intro j hj
    exact load_limb hstack (by omega) j hj

private theorem WorkspaceWrites.square_memory {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks)
    {a b : DataMem} (hw : WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) a b)
    (hm : squareMemory d x modulus blocks a) : squareMemory d x modulus blocks b := by
  induction hw with
  | refl => exact hm
  | store _ i hi v ih =>
    obtain ⟨⟨R, hframe⟩, hmem⟩ := ih
    refine ⟨⟨R, ?_⟩, ?_⟩
    · rw [sep_comm_l] at hframe ⊢
      apply Mem.Block.storeInt hframe _ v
      simp only [BitVec.add_comm (d.regs.get64 .rsp + 56), BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      have := h.sizeBound
      omega
    · have hs := reduction_memory_store _ _ _ _ modulus blocks h.modulusLength
        (by have := h.sizeBound; omega) h.disjoint hmem (7 + i) (by omega) (by omega) v
      simpa [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc] using hs

private theorem square_memory_load {d : MachineData} {x modulus : List (BitVec 64)}
    {blocks : Nat} {mem : DataMem} (h : squareMemory d x modulus blocks mem)
    (hb : 8 * x.length < 2 ^ 64) (j : Nat) (hj : j < x.length) :
    mem.loadInt (d.regs.get64 .rsi + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toInt)) := by
  obtain ⟨R, hm⟩ := h.1
  exact load_limb hm hb j hj

private theorem square_memory_mapped {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (hc : BnSqr8xBlockContext d x modulus n0 blocks)
    {mem : DataMem} (h : squareMemory d x modulus blocks mem) (j : Nat) (hj : j < 16 * blocks + 8) :
    (mem.loadInt (d.regs.get64 .rsp + BitVec.ofNat 64 (8 * j)) 8).isSome = true :=
  Mem.SubDom.loadInt_isSome h.2.1 (hc.mapped j hj)


set_option maxRecDepth 8192

private def squareRegisters (d s : MachineData) : Prop :=
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi + d.regs.get64 .r9 ∧ s.zmms = d.zmms

private theorem square_seed_registers (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    squareRegisters d (firstSeed d x blocks) ∧ squareRegisters d (firstDoneSeed d x blocks) ∧
    squareRegisters d (outerSeed d x blocks) ∧ squareRegisters d (productsSeed d x blocks) ∧
    squareRegisters d (diagonalSeed d x blocks) ∧ squareRegisters d (shiftSeed d x blocks) ∧
    squareRegisters d (shiftDoneSeed d x blocks) ∧ squareRegisters d (reductionSeed d x blocks) := by
  simp [squareRegisters, firstSeed, firstDoneSeed, outerSeed, productsSeed, diagonalSeed,
    shiftSeed, shiftDoneSeed, reductionSeed]

private theorem WorkspaceWrites.store_at {base : BitVec 64} {limbs : Nat} {a b : DataMem}
    (h : WorkspaceWrites base limbs a b) (i : Nat) (hi : i < limbs)
    {addr : BitVec 64} (ha : addr = base + BitVec.ofNat 64 (8 * i)) (v : Int) :
    WorkspaceWrites base limbs a (b.storeInt addr 8 v) := by
  rw [ha]
  exact h.store i hi v

private theorem first_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (firstSeed d x blocks).dmem := by
  have hn : 16 * (4 * blocks - 2) + 32 = 64 * blocks := by have := h.positive; omega
  have hf := first_preamble_result_fields d (4 * blocks - 2) x (by rw [hn]; exact h.size)
  change WorkspaceWrites _ _ _ (sqr4xFirstPreambleResult d (4 * blocks - 2) x).memory
  rw [hf.2.2.2]
  refine WorkspaceWrites.store_at ?_ 3 (by have := h.positive; omega) (by grind) _
  refine WorkspaceWrites.store_at ?_ 2 (by have := h.positive; omega) (by grind) _
  exact WorkspaceWrites.store_at (.refl _) 1 (by have := h.positive; omega) (by grind) _

private theorem first_done_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (firstDoneSeed d x blocks).dmem := by
  let s := firstSeed d x blocks
  let n := 4 * blocks - 2
  have hb : s.regs.get64 .rdi - BitVec.ofNat 64 (16 * n) =
      (d.regs.get64 .rsp + 56) + BitVec.ofNat 64 (8 * 4) := by
    have hn : 16 * n + 32 = 64 * blocks := by dsimp [n]; have := h.positive; omega
    simp only [s, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size, ← hn, BitVec.ofNat_add]
    grind
  have hw := inner_fold_writes (s.regs.get64 .r14) (s.regs.get64 .r15) (x.drop 4)
    (List.replicate (2 * n) 0) (s.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))
    ⟨s.regs.get64 .rax, s.regs.get64 .r11, s.regs.get64 .r13, s.dmem⟩ n (2 * n) (by omega)
  rw [hb] at hw
  apply (first_seed_writes h).trans
  change WorkspaceWrites _ _ s.dmem
    (sqr4xInnerFold (s.regs.get64 .r14) (s.regs.get64 .r15) (x.drop 4)
      (List.replicate (2 * n) 0) (s.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))
      ⟨s.regs.get64 .rax, s.regs.get64 .r11, s.regs.get64 .r13, s.dmem⟩ n).memory
  rw [hb]
  exact hw.shift (total := 16 * blocks + 1) (offset := 4) (by dsimp [n]; have := h.positive; omega)

private theorem outer_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (outerSeed d x blocks).dmem := by
  dsimp only [outerSeed]
  refine WorkspaceWrites.store_at ?_ (8 * blocks + 1) (by have := h.positive; omega) ?_ _
  · refine WorkspaceWrites.store_at (first_done_seed_writes h) (8 * blocks) (by have := h.positive; omega) ?_ _
    simp only [firstDoneSeed, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size]
    simp only [show 8 * (8 * blocks) = 64 * blocks by omega]
    grind
  · simp only [firstDoneSeed, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size]
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, show 8 * (8 * blocks) = 64 * blocks by omega]
    grind

private theorem products_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (productsSeed d x blocks).dmem := by
  let s := outerSeed d x blocks
  let n := 4 * blocks - 3
  have hf := (square_seed_registers d x blocks).2.2.1
  have hb : s.regs.get64 .rsp + s.regs.get64 .r9 * 2 + 56 - BitVec.ofNat 64 (32 * n + 64) =
      (d.regs.get64 .rsp + 56) + BitVec.ofNat 64 (8 * 4) := by
    have hn : 32 * n + 64 + 32 = 128 * blocks := by dsimp [n]; have := h.positive; omega
    rw [hf.1, hf.2.1, h.size]
    have he : BitVec.ofNat 64 (64 * blocks) * 2 = BitVec.ofNat 64 (128 * blocks) := by
      calc
        _ = BitVec.ofNat 64 (64 * blocks * 2) := by simpa using (BitVec.ofNat_mul (n := 64) (64 * blocks) 2).symm
        _ = _ := by congr 1; omega
    rw [he, ← hn, BitVec.ofNat_add]
    grind
  have hw := outer_fold_writes (x.drop 2) (s.regs.get64 .rsp + s.regs.get64 .r9 * 2 + 56)
    n ⟨outerAccumulator d x blocks, s.dmem⟩ n (by omega)
  rw [hb] at hw
  apply (outer_seed_writes h).trans
  change WorkspaceWrites _ _ s.dmem
    (sqr4xOuterFold (x.drop 2) (s.regs.get64 .rsp + s.regs.get64 .r9 * 2 + 56)
      n ⟨outerAccumulator d x blocks, s.dmem⟩ n).memory
  exact hw.shift (total := 16 * blocks + 1) (offset := 4) (by dsimp [n]; have := h.positive; omega)

private theorem diagonal_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (diagonalSeed d x blocks).dmem := by
  let s := productsSeed d x blocks
  have hf := (square_seed_registers d x blocks).2.2.2.1
  have hs (mem : DataMem) (j : Nat) (hj : j < 7) (v : Int)
      (hw : WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem mem) :
      WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem
        (mem.storeInt (finalProductBase s + BitVec.ofNat 64 (8 * j)) 8 v) := by
    apply hw.store_at (16 * blocks - 7 + j) (by have := h.positive; omega) _ v
    have hn : 8 * (16 * blocks - 7 + j) + 56 = 128 * blocks + 8 * j := by have := h.positive; omega
    dsimp only [finalProductBase]
    rw [hf.1, hf.2.1, h.size]
    have he : BitVec.ofNat 64 (64 * blocks) * 2 = BitVec.ofNat 64 (128 * blocks) := by
      calc
        _ = BitVec.ofNat 64 (64 * blocks * 2) := by simpa using (BitVec.ofNat_mul (n := 64) (64 * blocks) 2).symm
        _ = _ := by congr 1; omega
    rw [he]
    have := congrArg (BitVec.ofNat 64) hn
    simp only [BitVec.ofNat_add] at this
    grind
  exact hs _ 6 (by decide) _ (hs _ 5 (by decide) _ (hs _ 4 (by decide) _ (hs _ 4 (by decide) _
    (hs _ 3 (by decide) _ (hs _ 2 (by decide) _ (hs _ 1 (by decide) _ (hs _ 0 (by decide) _
      (products_seed_writes h))))))))

private theorem shift_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (shiftSeed d x blocks).dmem := by
  have hf := (square_seed_registers d x blocks).2.2.2.2.1
  dsimp only [shiftSeed]
  refine WorkspaceWrites.store_at ?_ 3 (by have := h.positive; omega) (by rw [hf.1]; grind) _
  refine WorkspaceWrites.store_at ?_ 2 (by have := h.positive; omega) (by rw [hf.1]; grind) _
  refine WorkspaceWrites.store_at ?_ 1 (by have := h.positive; omega) (by rw [hf.1]; grind) _
  exact WorkspaceWrites.store_at (diagonal_seed_writes h) 0 (by have := h.positive; omega)
    (by rw [hf.1]; grind) _

private theorem shift_done_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (shiftDoneSeed d x blocks).dmem := by
  let s := shiftSeed d x blocks
  let n := 2 * blocks - 1
  have hf := (square_seed_registers d x blocks).2.2.2.2.1
  have hb : s.regs.get64 .rdi + (-32#64) =
      (d.regs.get64 .rsp + 56) + BitVec.ofNat 64 (8 * 4) := by
    simp only [s, shiftSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [hf.1]
    grind
  have hw := shift_fold_writes (x.drop 2) (shiftAccumulator d x blocks) (s.regs.get64 .rdi + (-32#64))
    ⟨s.regs.get64 .r14, s.regs.get64 .r15, s.dmem⟩ n (8 * n) (by omega)
  rw [hb] at hw
  apply (shift_seed_writes h).trans
  change WorkspaceWrites _ _ s.dmem
    (sqr4xShiftFold (x.drop 2) (shiftAccumulator d x blocks) (s.regs.get64 .rdi + (-32#64))
      ⟨s.regs.get64 .r14, s.regs.get64 .r15, s.dmem⟩ n).memory
  rw [hb]
  exact hw.shift (total := 16 * blocks + 1) (offset := 4) (by dsimp [n]; have := h.positive; omega)

private theorem reduction_seed_writes {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem (reductionSeed d x blocks).dmem := by
  let s := shiftDoneSeed d x blocks
  have hf := (square_seed_registers d x blocks).2.2.2.2.1
  have hp : s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) := by
    have hn : 64 * (2 * blocks - 1) + 64 = 128 * blocks := by have := h.positive; omega
    simp only [s, shiftDoneSeed, shiftSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [hf.1, ← hn, BitVec.ofNat_add]
    grind
  have hs (mem : DataMem) (j : Nat) (hj : j < 4) (v : Int)
      (hw : WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem mem) :
      WorkspaceWrites (d.regs.get64 .rsp + 56) (16 * blocks + 1) d.dmem
        (mem.storeInt (s.regs.get64 .rdi + (-32#64 + BitVec.ofNat 64 (8 * j))) 8 v) := by
    apply hw.store_at (16 * blocks - 4 + j) (by have := h.positive; omega) _ v
    have hn : 8 * (16 * blocks - 4 + j) + 32 = 128 * blocks + 8 * j := by have := h.positive; omega
    rw [hp]
    have := congrArg (BitVec.ofNat 64) hn
    simp only [BitVec.ofNat_add] at this
    grind
  dsimp only [reductionSeed]
  simpa [s, BitVec.reduceAdd] using
    hs _ 3 (by decide) _ (hs _ 2 (by decide) _ (hs _ 1 (by decide) _
      (hs _ 0 (by decide) _ (shift_done_seed_writes h))))


private def firstAccumulator (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : List (BitVec 64) :=
  ((snapshotLimbs (firstSeed d x blocks).dmem (d.regs.get64 .rsp + 56)
    (16 * blocks + 1)).drop 4).take (2 * (4 * blocks - 2))

private theorem first_seed_frame {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∃ R : DataMem → Prop, firstFrame (firstSeed d x blocks) (4 * blocks - 2)
      (x.drop 4) (firstAccumulator d x blocks) R := by
  let s := firstSeed d x blocks
  let n := 4 * blocks - 2
  have hp := h.positive
  obtain ⟨R, hm⟩ := ((first_seed_writes h).square_memory h h.memory).1
  obtain ⟨F, hf⟩ := frame_windows s.dmem x (d.regs.get64 .rsi) (d.regs.get64 .rsp + 56)
    (16 * blocks + 1) 4 (2 * n) 4 (2 * n) R
    (by rw [h.inputLength]; dsimp [n]; omega) (by dsimp [n]; omega)
    (by rw [h.inputLength]; have := h.sizeBound; omega) hm
  have hx : (x.drop 4).take (2 * n) = x.drop 4 := by
    apply List.take_of_length_le
    rw [List.length_drop, h.inputLength]
    dsimp [n]; omega
  have hn : 16 * n + 32 = 64 * blocks := by dsimp [n]; omega
  have ha : s.regs.get64 .rsi - BitVec.ofNat 64 (16 * n) = d.regs.get64 .rsi + BitVec.ofNat 64 (8 * 4) := by
    simp only [s, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size, ← hn, BitVec.ofNat_add]; grind
  have hb : s.regs.get64 .rdi - BitVec.ofNat 64 (16 * n) = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * 4) := by
    simp only [s, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size, ← hn, BitVec.ofNat_add]; grind
  refine ⟨F, ?_⟩
  change s.dmem =⋆ Eq (((x.drop 4).flatMap fun w => Int.toBytes 8 w.toInt).At
    (s.regs.get64 .rsi - BitVec.ofNat 64 (16 * n))) ⋆
    (Eq (((firstAccumulator d x blocks).flatMap fun w => Int.toBytes 8 w.toInt).At
      (s.regs.get64 .rdi - BitVec.ofNat 64 (16 * n))) ⋆ F)
  rw [ha, hb]
  simpa only [hx, firstAccumulator] using hf

private theorem outer_seed_frame {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∃ R : DataMem → Prop, outerMemInv (outerSeed d x blocks) (4 * blocks - 3)
      (x.drop 2) R (outerAccumulator d x blocks) (outerSeed d x blocks).dmem := by
  let s := outerSeed d x blocks
  let n := 4 * blocks - 3
  have hp := h.positive
  have hr := (square_seed_registers d x blocks).2.2.1
  obtain ⟨R, hm⟩ := ((outer_seed_writes h).square_memory h h.memory).1
  obtain ⟨F, hf⟩ := frame_windows s.dmem x (d.regs.get64 .rsi) (d.regs.get64 .rsp + 56)
    (16 * blocks + 1) 2 (2 * n + 4) 4 (16 * blocks - 4) R
    (by rw [h.inputLength]; dsimp [n]; omega) (by omega)
    (by rw [h.inputLength]; have := h.sizeBound; omega) hm
  have hx : (x.drop 2).take (2 * n + 4) = x.drop 2 := by
    apply List.take_of_length_le
    rw [List.length_drop, h.inputLength]; dsimp [n]; omega
  have ha : s.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32) =
      d.regs.get64 .rsi + BitVec.ofNat 64 (8 * 2) := by
    have hn : 16 * n + 32 + 16 = 64 * blocks := by dsimp [n]; omega
    rw [hr.2.2.1, h.size, ← hn, BitVec.ofNat_add]; grind
  have hb : s.regs.get64 .rsp + s.regs.get64 .r9 * 2 + 56 - BitVec.ofNat 64 (32 * n + 64) =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * 4) := by
    have hn : 32 * n + 64 + 32 = 128 * blocks := by dsimp [n]; omega
    rw [hr.1, hr.2.1, h.size]
    have he : BitVec.ofNat 64 (64 * blocks) * 2 = BitVec.ofNat 64 (128 * blocks) := by
      calc
        _ = BitVec.ofNat 64 (64 * blocks * 2) := by simpa using (BitVec.ofNat_mul (n := 64) (64 * blocks) 2).symm
        _ = _ := by congr 1; omega
    rw [he, ← hn, BitVec.ofNat_add]; grind
  refine ⟨F, ?_, ?_⟩
  · simp only [outerAccumulator, List.length_take, List.length_drop, snapshot_length]
    omega
  · change s.dmem =⋆ Eq (((x.drop 2).flatMap fun w => Int.toBytes 8 w.toInt).At
      (s.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))) ⋆
      (Eq (((outerAccumulator d x blocks).flatMap fun w => Int.toBytes 8 w.toInt).At
        (s.regs.get64 .rsp + s.regs.get64 .r9 * 2 + 56 - BitVec.ofNat 64 (32 * n + 64))) ⋆ F)
    rw [ha, hb]
    simpa only [hx, outerAccumulator] using hf

private theorem shift_seed_frame {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∃ R : DataMem → Prop, shiftFrame (shiftSeed d x blocks) (2 * blocks - 1)
      (x.drop 2) (shiftAccumulator d x blocks) R := by
  let s := shiftSeed d x blocks
  let n := 2 * blocks - 1
  have hp := h.positive
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.1
  obtain ⟨R, hm⟩ := ((shift_seed_writes h).square_memory h h.memory).1
  obtain ⟨F, hf⟩ := frame_windows s.dmem x (d.regs.get64 .rsi) (d.regs.get64 .rsp + 56)
    (16 * blocks + 1) 2 (4 * n + 2) 4 (16 * blocks - 4) R
    (by rw [h.inputLength]; dsimp [n]; omega) (by omega)
    (by rw [h.inputLength]; have := h.sizeBound; omega) hm
  have hx : (x.drop 2).take (4 * n + 2) = x.drop 2 := by
    apply List.take_of_length_le
    rw [List.length_drop, h.inputLength]; dsimp [n]; omega
  have ha : s.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64) =
      d.regs.get64 .rsi + BitVec.ofNat 64 (8 * 2) := by
    have hn : 32 * n + 32 = 64 * blocks := by dsimp [n]; omega
    rw [hr.2.2.1, h.size, ← hn, BitVec.ofNat_add]; grind
  have hb : s.regs.get64 .rdi + (-32#64) =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * 4) := by
    simp only [s, shiftSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [(square_seed_registers d x blocks).2.2.2.2.1.1]; grind
  refine ⟨F, ?_⟩
  change s.dmem =⋆ Eq (((x.drop 2).flatMap fun w => Int.toBytes 8 w.toInt).At
    (s.regs.get64 .rsi - BitVec.ofNat 64 (32 * n) + (-16#64))) ⋆
    (Eq (((shiftAccumulator d x blocks).flatMap fun w => Int.toBytes 8 w.toInt).At
      (s.regs.get64 .rdi + (-32#64))) ⋆ F)
  rw [ha, hb]
  simpa only [hx, shiftAccumulator] using hf


private def firstLoopInvariant (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (s : MachineData) : Prop := firstInvariant d n x s

private def firstLoopPost (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (s : MachineData) : Prop :=
  s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.regs.get64 .r9 = d.regs.get64 .r9 ∧
  s.regs.get64 .rbp = d.regs.get64 .rbp ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rdi = d.regs.get64 .rdi ∧
  s.regs.get64 .r14 = d.regs.get64 .r14 ∧ s.regs.get64 .r15 = d.regs.get64 .r15 ∧
  s.regs.get64 .rcx = 0 ∧
  s.regs.get64 .rax = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).previous ∧
  s.regs.get64 .r11 = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).carry0 ∧
  s.regs.get64 .r13 = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).carry1 ∧
  s.dmem = (sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) n).memory

private def sqr4x_first_cycle : Program :=
  sqr4x_first_iteration ++ parse("cmpq $0,%rcx\njne .Lsqr4x_1st")

section
attribute [local irreducible] innerOffset innerIndex sqr4xInnerPrefix firstFrame
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some
  CondCode.interp_nz StatusFlags.zf_from_result
attribute [local irreducible] sqr4xFirstResult sqr4xInnerResult sqr4xMac
attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
  sqr4xMac_eq BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero bv_add_zero bv_zero_add
  CondCode.interp_nz StatusFlags.zf_from_result
  Sqr4xInnerResult.out0_mk Sqr4xInnerResult.out1_mk
  Sqr4xInnerResult.carry0_mk Sqr4xInnerResult.carry1_mk
  Sqr4xFirstResult.out0_mk Sqr4xFirstResult.out1_mk Sqr4xFirstResult.out2_mk Sqr4xFirstResult.out3_mk
  Sqr4xFirstResult.carry0_mk Sqr4xFirstResult.carry1_mk
attribute [local grind =] ofInt_limb prefix_zero offset_initial_index offset_step_two offset_zero
  first_prefetch_2_0 first_prefetch_3_0 first_prefetch_3_1
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8
local grind_pattern offset_facts => innerOffset n k
local grind_pattern offset_continue_two => innerOffset n j + 32
local grind_pattern first_prefix_step => innerOffset n j + 32,
  sqr4xInnerPrefix d n x (List.replicate (2 * n) 0) j
local grind_pattern first_iteration_accesses =>
  innerIndex n (s.regs.get64 .rcx), firstFrame d n x t R


attribute [local grind unfold] firstLoopInvariant firstLoopPost
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem first_cycle_correct [CodeEnv] (d s0 : MachineData) (n : Nat) (x t : List (BitVec 64))
    (hb : 16 * n < 2 ^ 63) (heven : n % 2 = 0) (hxl : x.length = 2 * n) (htl : t.length = 2 * n)
    (R : DataMem → Prop) (hm : firstFrame d n x t R) :
    ⦃ fun s => s = s0 ∧ firstLoopInvariant d n x s ⦄ sqr4x_first_cycle
    ⦃ fun _ s => firstLoopPost d n x s;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_1st" ∧
        firstLoopInvariant d n x s ∧
        2 ^ 64 - (s.regs.get64 .rcx).toNat < 2 ^ 64 - (s0.regs.get64 .rcx).toNat ⦄ := by
  vcgen [sqr4x_first_cycle, (fun s => sqr4x_first_iteration_correct s
    (Int.ofBytes (Int.toBytes 8 (x.getD (2 * innerIndex n (s.regs.get64 .rcx)) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (2 * innerIndex n (s.regs.get64 .rcx) + 1) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (2 * innerIndex n (s.regs.get64 .rcx) + 2) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (2 * innerIndex n (s.regs.get64 .rcx) + 3) 0).toInt)))] simplifying_assumptions with
    finish (ematch := 16) (splits := 4) (hom := false) (canonHeartbeats := 5)
end


private def outerLoopInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop := outerInvariant d n x t s
private def outerBodyInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop := outerInnerInvariant d n x t s
private def outerLoopPost (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧ s.regs.get64 .rbp = 0 ∧ s.regs.get64 .rcx = 0 ∧
  s.zmms = d.zmms ∧
  s.regs.get64 .r10 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 1) 0 ∧
  s.regs.get64 .r13 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 2) 0 ∧
  s.regs.get64 .r12 = (sqr4xOuterPrefix d n x t n).limbs.getD (4 * n + 3) 0 ∧
  s.dmem = (sqr4xOuterPrefix d n x t n).memory

private def sqr4x_outer_cycle : Program :=
  sqr4x_inner_iteration ++ parse("cmpq $0,%rcx\njne .Lsqr4x_inner") ++ sqr4x_outer_tail

section
attribute [local irreducible] sqr4xMac innerIndex innerOffset sqr4xOuterPrefix sqr4xOuterInnerPrefix
attribute [local sym_simp] Option.map_none BitVec.zero_add BitVec.sub_zero CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind unfold] sqr4xInnerResult
attribute [local grind norm]
  sqr4xMac_eq Kraken.Fold.fst_mk Kraken.Fold.snd_mk
  BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.xor_self BitVec.zero_add BitVec.sub_zero
  CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind =] ofInt_limb offset_initial_index offset_step

local grind_pattern offset_continue => innerOffset n k + 16
local grind_pattern offset_done => innerOffset n k + 16
local grind_pattern outer_offset_continue => innerOffset n k + 16
local grind_pattern outer_inner_prefix_self_fields =>
  sqr4xOuterInnerPrefix d n x t i i, sqr4xOuterPrefix d n x t i
local grind_pattern outer_inner_prefix_step_fields =>
  sqr4xOuterInnerPrefix d n x t i j, innerOffset n j + 16
local grind_pattern outer_prefix_step_mem =>
  (sqr4xOuterPrefix d n x t k).memory, sqr4xOuterInnerPrefix d n x t i j

local grind_pattern outer_final_words =>
  sqr4xOuterInnerPrefix d n x t i j, sqr4xOuterPrefix d n x t n

local grind_pattern outer_preamble_loads =>
  sqr4xOuterPrefix d n x t (innerIndex n (s.regs.get64 .rbp)),
  Std.ExtHashMap.sep (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))))
    (Std.ExtHashMap.sep (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (32 * n + 64)))) R) d.dmem

local grind_pattern outer_inner_loads =>
  sqr4xOuterInnerPrefix d n x t (innerIndex n (s.regs.get64 .rbp)) (innerIndex n (s.regs.get64 .rcx)),
  Std.ExtHashMap.sep (Eq ((x.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsi - BitVec.ofNat 64 (16 * n + 32))))
    (Std.ExtHashMap.sep (Eq ((t.flatMap fun w => Int.toBytes 8 w.toInt).At
      (d.regs.get64 .rsp + d.regs.get64 .r9 * 2#64 + 56#64 -
        BitVec.ofNat 64 (32 * n + 64)))) R) d.dmem


attribute [local grind unfold] outerLoopInvariant outerBodyInvariant outerLoopPost
attribute [local grind norm] Width.scaleFactor_W16 bv_add_zero bv_zero_add bv_sub_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  StatusFlags.cf_from_result StatusFlags.from_result.Remaining.cf_mk
attribute [local grind =] ofInt_limb_opaque add_16_innerOffset load_after_store_24_16
  load_after_store_24_8 load_after_store_16_8
local grind_pattern bound_16_of_32 => 32 * n + 64
local grind_pattern offset_facts => innerOffset n k
local grind_pattern storeInt_loadInt_isSome => (m.storeInt a 8 v).loadInt b 8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem outer_entry_correct [CodeEnv] (d s0 : MachineData) (n : Nat) (x t : List (BitVec 64))
    (hb : 32 * n + 64 < 2 ^ 63) (hxl : x.length = 2 * n + 4)
    (R : DataMem → Prop) (hm : outerMemInv d n x R t d.dmem) :
    ⦃ fun s => s = s0 ∧ outerLoopInvariant d n x t s ⦄ sqr4x_outer_preamble
    ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_inner" ∧
        outerBodyInvariant d n x t s ∧
        sqr4x_outer_var ".Lsqr4x_inner" s < sqr4x_outer_var ".Lsqr4x_outer" s0 ⦄ := by
  obtain ⟨htl, hm⟩ := hm
  vcgen [sqr4x_outer_preamble] simplifying_assumptions with finish

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem outer_cycle_correct [CodeEnv] (d s0 : MachineData) (n : Nat) (x t : List (BitVec 64))
    (hb : 32 * n + 64 < 2 ^ 63) (hxl : x.length = 2 * n + 4)
    (R : DataMem → Prop) (hm : outerMemInv d n x R t d.dmem) :
    ⦃ fun s => s = s0 ∧ outerBodyInvariant d n x t s ⦄ sqr4x_outer_cycle
    ⦃ fun _ s => outerLoopPost d n x t s;
      fun pc s =>
        (pc = (_root_.Executable.labels cenv).label ".Lsqr4x_inner" ∧ outerBodyInvariant d n x t s ∧
          sqr4x_outer_var ".Lsqr4x_inner" s < sqr4x_outer_var ".Lsqr4x_inner" s0) ∨
        (pc = (_root_.Executable.labels cenv).label ".Lsqr4x_outer" ∧ outerLoopInvariant d n x t s ∧
          sqr4x_outer_var ".Lsqr4x_outer" s < sqr4x_outer_var ".Lsqr4x_inner" s0) ⦄ := by
  obtain ⟨htl, hm⟩ := hm
  vcgen [sqr4x_outer_cycle, sqr4x_inner_iteration, sqr4x_outer_tail]
    simplifying_assumptions with finish
end


private def shiftLoopInvariant (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop := shiftInvariant d n x t s

private def shiftLoopPost (d : MachineData) (n : Nat) (x t : List (BitVec 64))
    (s : MachineData) : Prop :=
  s.regs.get64 .rbp = 0 ∧ s.regs.get64 .rcx = 0 ∧
  s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 (64 * n) ∧
  s.regs.get64 .rsi = d.regs.get64 .rsi ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ∧
  s.regs.get64 .r9 = d.regs.get64 .r9 ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rax = x.getD (4 * n) 0 ∧ s.regs.get64 .r10 = t.getD (8 * n) 0 ∧
  s.regs.get64 .r11 = t.getD (8 * n + 1) 0 ∧
  s.regs.get64 .r14 = (sqr4xShiftPrefix d x t n).shiftCarry ∧
  s.regs.get64 .r15 = (sqr4xShiftPrefix d x t n).addCarry ∧
  s.dmem = (sqr4xShiftPrefix d x t n).memory

private def sqr4x_shift_cycle : Program :=
  sqr4x_shift_iteration ++ parse("addq $32,%rbp\njnz .Lsqr4x_shift_n_add")

section
attribute [local irreducible] shiftOffset shiftIndex shiftFrame sqr4xShiftPrefix
attribute [local grind unfold] shiftLoopInvariant shiftLoopPost
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  BitVec.add_zero bv_add_zero bv_zero_add
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 Width.scaleFactor_W8 BitVec.mul_one
  Option.map_none Option.map_some CondCode.interp_nz StatusFlags.zf_from_result
attribute [local sym_simp] BitVec.zero_add Option.map_none Option.map_some CondCode.interp_nz StatusFlags.zf_from_result
attribute [local grind =] shift_counter_zero shift_counter_step shift_counter_initial
local grind_pattern shift_prefix_zero => sqr4xShiftPrefix d x t 0
local grind_pattern shift_counter_facts => shiftOffset n k
local grind_pattern shift_counter_continue => 32 + shiftOffset n k

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem shift_cycle_correct [CodeEnv] (d s0 : MachineData) (n : Nat) (x t : List (BitVec 64))
    (hb : 64 * n + 64 < 2 ^ 63) (hxl : x.length = 4 * n + 2) (htl : t.length = 8 * n + 4)
    (R : DataMem → Prop) (hm : shiftFrame d n x t R) :
    ⦃ fun s => s = s0 ∧ shiftLoopInvariant d n x t s ⦄ sqr4x_shift_cycle
    ⦃ fun _ s => shiftLoopPost d n x t s;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_shift_n_add" ∧
        shiftLoopInvariant d n x t s ∧
        2 ^ 64 - (s.regs.get64 .rbp).toNat < 2 ^ 64 - (s0.regs.get64 .rbp).toNat ⦄ := by
  vcgen [sqr4x_shift_cycle, shift_iteration_from_prefix d n x t R hb hxl htl hm]
    simplifying_assumptions with finish (ematch := 12) (splits := 16)
end


private theorem square_memory_disjoint {d : MachineData} {x modulus : List (BitVec 64)}
    {blocks : Nat} {mem : DataMem} (h : squareMemory d x modulus blocks mem) :
    ∀ i < 8 * x.length, ∀ j < 8 * (16 * blocks + 1),
      d.regs.get64 .rsi + BitVec.ofNat 64 i ≠ d.regs.get64 .rsp + 56 + BitVec.ofNat 64 j := by
  obtain ⟨R, hm⟩ := h.1
  rw [sep_comm_l] at hm
  have hs := snapshot_block mem (d.regs.get64 .rsp + 56) (16 * blocks + 1) _ hm
  rw [sep_comm_l] at hs
  simpa only [length_flatMap_limbs, snapshot_length] using sep_At_ne hs

private theorem square_start_access {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    (∀ j < 4, d.dmem.loadInt (d.regs.get64 .rsi + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toInt))) ∧
    (d.dmem.loadInt (d.regs.get64 .rsp + 64) 8).isSome = true ∧
    (d.dmem.loadInt (d.regs.get64 .rsp + 72) 8).isSome = true ∧
    (d.dmem.loadInt (d.regs.get64 .rsp + 80) 8).isSome = true ∧
    firstWindowsDisjoint (d.regs.get64 .rsi) (d.regs.get64 .rsp + 64) := by
  have hp := h.positive
  refine ⟨?_, h.mapped 8 (by omega), h.mapped 9 (by omega), h.mapped 10 (by omega), ?_⟩
  · intro j hj
    exact square_memory_load h.memory (by rw [h.inputLength]; have := h.sizeBound; omega)
      j (by rw [h.inputLength]; omega)
  · intro u hu v hv
    have hn := square_memory_disjoint h.memory u (by rw [h.inputLength]; omega) (8 + v) (by omega)
    have he : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 + v) =
        d.regs.get64 .rsp + 64 + BitVec.ofNat 64 v := by
      simp only [BitVec.ofNat_add]; grind
    rw [he] at hn
    exact hn

private theorem first_seed_fields (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := firstSeed d x blocks
    let r := sqr4xFirstPreambleResult d (4 * blocks - 2) x
    squareRegisters d s ∧
    s.regs.get64 .rdi = d.regs.get64 .rsp + d.regs.get64 .r9 + 56 ∧
    s.regs.get64 .rbp = 32 - d.regs.get64 .r9 ∧ s.regs.get64 .rcx = 32 - d.regs.get64 .r9 ∧
    s.regs.get64 .r14 = x.getD 0 0 ∧ s.regs.get64 .r15 = x.getD 1 0 ∧
    s.regs.get64 .rax = r.previous ∧ s.regs.get64 .r11 = r.carry0 ∧
    s.regs.get64 .r13 = r.carry1 ∧ s.dmem = r.memory := by
  simp [firstSeed, squareRegisters]

private theorem square_first_counter {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let n := 4 * blocks - 2
    2 ≤ n ∧ n % 2 = 0 ∧ 16 * n < 2 ^ 63 ∧
    d.regs.get64 .r9 = BitVec.ofNat 64 (16 * n + 32) ∧
    32 - d.regs.get64 .r9 = innerOffset n 0 ∧
    innerIndex n (32 - d.regs.get64 .r9) = 0 := by
  have hp := h.positive
  have hb := h.sizeBound
  have hn : 16 * (4 * blocks - 2) + 32 = 64 * blocks := by omega
  have he : 32 - d.regs.get64 .r9 = 0#64 - BitVec.ofNat 64 (16 * (4 * blocks - 2)) := by
    rw [h.size, ← hn, BitVec.ofNat_add]; grind
  refine ⟨by omega, by omega, by omega, by rw [hn]; exact h.size, ?_, ?_⟩
  · rw [he]; rfl
  · rw [he]; exact offset_initial_index _ (by omega) (by omega)

section
attribute [local irreducible] firstSeed sqr4xInnerPrefix sqr4xFirstPreambleResult innerIndex innerOffset
attribute [local grind unfold] firstLoopInvariant squareRegisters
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local grind =] prefix_zero
local grind_pattern first_seed_fields => firstSeed d x blocks

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem square_start_correct [CodeEnv] (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ fun s => s = d ⦄ sqr4x_first_preamble ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_1st" ∧
        firstLoopInvariant (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) s ⦄ := by
  vcgen [sqr4x_first_preamble_correct d (4 * blocks - 2) x]
    simplifying_assumptions with finish (ematch := 16) (splits := 16)
      [square_start_access h, square_first_counter h, h.offset]
end

private theorem first_done_post (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    firstLoopPost (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) (firstDoneSeed d x blocks) := by
  simp [firstLoopPost, firstDoneSeed]

private theorem outer_seed_fields (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := firstDoneSeed d x blocks
    let r := outerSeed d x blocks
    r.regs.get64 .rsp = s.regs.get64 .rsp ∧ r.regs.get64 .r9 = s.regs.get64 .r9 ∧
    r.regs.get64 .rsi = s.regs.get64 .rsi ∧ r.zmms = s.zmms ∧
    r.regs.get64 .rbp = s.regs.get64 .rbp + 16 ∧
    r.dmem = (s.dmem.storeInt (s.regs.get64 .rdi) 8 (firstTailResult s).1.toIntOpaque).storeInt
      (s.regs.get64 .rdi + 8) 8 (firstTailResult s).2.toIntOpaque := by
  simp [outerSeed]

private theorem square_outer_counter {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let n := 4 * blocks - 3
    0 < n ∧ 32 * n + 64 < 2 ^ 63 ∧
    (firstDoneSeed d x blocks).regs.get64 .rbp + 16 = innerOffset n 0 ∧
    innerIndex n ((firstDoneSeed d x blocks).regs.get64 .rbp + 16) = 0 := by
  have hp := h.positive
  have hb := h.sizeBound
  have hn : 16 * (4 * blocks - 3) + 48 = 64 * blocks := by omega
  have he : (firstDoneSeed d x blocks).regs.get64 .rbp + 16 =
      0#64 - BitVec.ofNat 64 (16 * (4 * blocks - 3)) := by
    simp only [firstDoneSeed, firstSeed, MachineData.regs_mk, Reg64s.get64_set64]
    rw [h.size, ← hn, BitVec.ofNat_add]; grind
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [he]; rfl
  · rw [he]; exact offset_initial_index _ (by omega) (by omega)

private theorem first_done_tail_mapped {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let s := firstDoneSeed d x blocks
    (s.dmem.loadInt (s.regs.get64 .rdi) 8).isSome = true ∧
      (s.dmem.loadInt (s.regs.get64 .rdi + 8) 8).isSome = true := by
  let s := firstDoneSeed d x blocks
  have hp : s.regs.get64 .rdi = d.regs.get64 .rsp + d.regs.get64 .r9 + 56 := by
    simp [s, firstDoneSeed, firstSeed]
  have hm := (first_done_seed_writes h).square_memory h h.memory
  have hl (j : Nat) (hj : j < 2) :
      (s.dmem.loadInt (s.regs.get64 .rdi + BitVec.ofNat 64 (8 * j)) 8).isSome = true := by
    have ha : s.regs.get64 .rdi + BitVec.ofNat 64 (8 * j) =
        d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (8 * blocks + 7 + j)) := by
      rw [hp, h.size]
      simp only [Nat.mul_add, BitVec.ofNat_add, show 8 * (8 * blocks) = 64 * blocks by omega]
      grind
    rw [ha]
    exact square_memory_mapped h hm (8 * blocks + 7 + j) (by have := h.positive; omega)
  exact ⟨by simpa using hl 0 (by decide), by simpa using hl 1 (by decide)⟩

section
attribute [local irreducible] firstSeed firstDoneSeed outerSeed sqr4xInnerPrefix sqr4xOuterPrefix
  innerIndex innerOffset sqr4xMac
attribute [local grind unfold] firstLoopPost outerLoopInvariant
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
local grind_pattern first_done_post => firstDoneSeed d x blocks
local grind_pattern outer_seed_fields => outerSeed d x blocks
attribute [local grind =] outer_prefix_zero_mem

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem square_first_tail_correct [CodeEnv] (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ firstLoopPost (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) ⦄ sqr4x_first_tail
    ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_outer" ∧
        outerLoopInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2)
          (outerAccumulator d x blocks) s ⦄ := by
  vcgen [sqr4x_first_tail_correct] simplifying_assumptions with
    finish (ematch := 16) (splits := 16) [square_outer_counter h, first_done_tail_mapped h]
end

private theorem snapshot_getD (mem : DataMem) (a : BitVec 64) (n i : Nat) (hi : i < n) :
    (snapshotLimbs mem a n).getD i 0 = readWord mem (a + BitVec.ofNat 64 (8 * i)) := by
  simp [snapshotLimbs, List.getD_eq_getElem?_getD, hi]

private theorem snapshot_slice_getD (mem : DataMem) (a : BitVec 64) (n offset len i : Nat)
    (hb : offset + len ≤ n) (hi : i < len) :
    (((snapshotLimbs mem a n).drop offset).take len).getD i 0 =
      readWord mem (a + BitVec.ofNat 64 (8 * (offset + i))) := by
  simp [snapshotLimbs, List.getD_eq_getElem?_getD, hi, show offset + i < n by omega]

private theorem read_word_store (mem : DataMem) (addr write : BitVec 64) (v : Int)
    (hd : readWindowDisjoint addr write 8) :
    readWord (mem.storeInt write 8 v) addr = readWord mem addr := by
  simp only [readWord, load_after_disjoint_store mem write addr v hd]

private theorem shift_seed_prefetch {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let t := snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)
    (shiftAccumulator d x blocks).getD 0 0 = t.getD 4 0 ∧
    (shiftAccumulator d x blocks).getD 1 0 = t.getD 5 0 := by
  have hp := h.positive
  have hr := (square_seed_registers d x blocks).2.2.2.2.1
  have he (j : Nat) (hj : j < 2) :
      (shiftAccumulator d x blocks).getD j 0 =
        (snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD (4 + j) 0 := by
    rw [shiftAccumulator, snapshot_slice_getD _ _ _ _ _ _ (by omega) (by omega),
      snapshot_getD _ _ _ _ (by omega)]
    have hd (k : Nat) (hk : k < 4) := stack_words_disjoint (d.regs.get64 .rsp + 56) (4 + j) k
      (by omega) (by omega) (by omega)
    dsimp only [shiftSeed]
    rw [hr.1]
    rw [read_word_store _ _ _ _ (by simpa [BitVec.add_assoc] using hd 3 (by decide)),
      read_word_store _ _ _ _ (by simpa [BitVec.add_assoc] using hd 2 (by decide)),
      read_word_store _ _ _ _ (by simpa [BitVec.add_assoc] using hd 1 (by decide)),
      read_word_store _ _ _ _ (by simpa [BitVec.add_assoc] using hd 0 (by decide))]
  exact ⟨he 0 (by decide), he 1 (by decide)⟩

private theorem products_seed_post (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    outerLoopPost (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2)
      (outerAccumulator d x blocks) (productsSeed d x blocks) := by
  simp [outerLoopPost, productsSeed]

private def diagonalMatch (r s : MachineData) : Prop :=
  s.regs.get64 .rsp = r.regs.get64 .rsp ∧ s.regs.get64 .r9 = r.regs.get64 .r9 ∧
  s.regs.get64 .rsi = r.regs.get64 .rsi ∧ s.zmms = r.zmms ∧ s.regs.get64 .rcx = 0 ∧
  s.regs.get64 .rbp = r.regs.get64 .rbp ∧ s.regs.get64 .r14 = r.regs.get64 .r14 ∧
  s.regs.get64 .r15 = r.regs.get64 .r15 ∧ s.dmem = r.dmem

private theorem diagonal_seed_fields (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := productsSeed d x blocks
    let r := sqr4xFinalProducts (x.getD (8 * blocks - 4) 0) (x.getD (8 * blocks - 3) 0)
      (x.getD (8 * blocks - 2) 0) (x.getD (8 * blocks - 1) 0)
      (s.regs.get64 .r10) (s.regs.get64 .r13) (s.regs.get64 .r12)
    let base := finalProductBase s
    let t := diagonalSeed d x blocks
    t.regs.get64 .rsp = s.regs.get64 .rsp ∧ t.regs.get64 .r9 = s.regs.get64 .r9 ∧
    t.regs.get64 .rsi = s.regs.get64 .rsi ∧ t.zmms = s.zmms ∧
    t.regs.get64 .rbp = 16 - s.regs.get64 .r9 ∧ t.regs.get64 .r14 = 0 ∧ t.regs.get64 .r15 = 0 ∧
    t.dmem = ((((((((s.dmem.storeInt (base + 0) 8 r.1.w1.toIntOpaque).storeInt
      (base + 8) 8 r.1.w2.toIntOpaque).storeInt (base + 16) 8 r.1.w3.toIntOpaque).storeInt
      (base + 24) 8 r.1.w4.toIntOpaque).storeInt (base + 32) 8 r.2.toIntOpaque).storeInt
      (base + 32) 8 r.1.w5.toIntOpaque).storeInt (base + 40) 8 r.1.w6.toIntOpaque).storeInt
      (base + 48) 8 r.1.w7.toIntOpaque) := by
  simp [diagonalSeed]

private theorem square_products_access {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let s := productsSeed d x blocks
    (∀ j < 4, s.dmem.loadInt (s.regs.get64 .rsi + (-32#64) + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 4 + j) 0).toInt))) ∧
    (∀ j < 7, (s.dmem.loadInt (finalProductBase s + BitVec.ofNat 64 (8 * j)) 8).isSome = true) ∧
    finalProductDisjoint (s.regs.get64 .rsi) (finalProductBase s) := by
  let s := productsSeed d x blocks
  have hp := h.positive
  have hr := (square_seed_registers d x blocks).2.2.2.1
  have hm := (products_seed_writes h).square_memory h h.memory
  have he : BitVec.ofNat 64 (64 * blocks) * 2 = BitVec.ofNat 64 (128 * blocks) := by
    calc
      _ = BitVec.ofNat 64 (64 * blocks * 2) := by simpa using (BitVec.ofNat_mul (n := 64) (64 * blocks) 2).symm
      _ = _ := by congr 1; omega
  have ha (j : Nat) : s.regs.get64 .rsi + (-32#64) + BitVec.ofNat 64 (8 * j) =
      d.regs.get64 .rsi + BitVec.ofNat 64 (8 * (8 * blocks - 4 + j)) := by
    have hn : 8 * (8 * blocks - 4 + j) + 32 = 64 * blocks + 8 * j := by omega
    rw [hr.2.2.1, h.size]
    have := congrArg (BitVec.ofNat 64) hn
    simp only [BitVec.ofNat_add] at this
    grind
  have hb (j : Nat) : finalProductBase s + BitVec.ofNat 64 (8 * j) =
      d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (16 * blocks + j)) := by
    dsimp only [finalProductBase]
    rw [hr.1, hr.2.1, h.size, he]
    simp [Nat.mul_add, show 8 * (16 * blocks) = 128 * blocks by omega, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [ha]
    exact square_memory_load hm (by rw [h.inputLength]; have := h.sizeBound; omega) _
      (by rw [h.inputLength]; omega)
  · intro j hj
    rw [hb]
    exact square_memory_mapped h hm _ (by omega)
  · intro j hj u hu v hv
    have hd := square_memory_disjoint hm (8 * (8 * blocks - 4) + u)
      (by rw [h.inputLength]; omega) (8 * (16 * blocks - 7 + j) + v) (by omega)
    have ha0 : s.regs.get64 .rsi + (-32#64) = d.regs.get64 .rsi + BitVec.ofNat 64 (8 * (8 * blocks - 4)) := by
      simpa using ha 0
    have hb0 : finalProductBase s + BitVec.ofNat 64 (8 * j) =
        d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * (16 * blocks - 7 + j)) := by
      rw [hb]
      have hn : 8 * (16 * blocks - 7 + j) + 56 = 8 * (16 * blocks + j) := by omega
      rw [← hn, BitVec.ofNat_add]; grind
    rw [ha0, hb0]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hd

section
attribute [local irreducible] outerSeed productsSeed diagonalSeed sqr4xOuterPrefix sqr4xFinalProducts
attribute [local grind unfold] outerLoopPost diagonalMatch
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local grind =] ofInt_limb
local grind_pattern products_seed_post => productsSeed d x blocks
local grind_pattern diagonal_seed_fields => diagonalSeed d x blocks

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem square_products_correct [CodeEnv] (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ outerLoopPost (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) ⦄
      sqr4x_final_products ⦃ fun _ s => diagonalMatch (diagonalSeed d x blocks) s ⦄ := by
  vcgen [(fun s => sqr4x_final_products_correct s
    (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 4) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 3) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 2) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 1) 0).toInt)))]
    simplifying_assumptions with finish (ematch := 16) (splits := 16)
      [
        h.positive,
        (square_products_access h).2.2,
        (square_products_access h).1 0 (by decide),
        (square_products_access h).1 1 (by decide),
        (square_products_access h).1 2 (by decide),
        (square_products_access h).1 3 (by decide),
        (square_products_access h).2.1 0 (by decide),
        (square_products_access h).2.1 1 (by decide),
        (square_products_access h).2.1 2 (by decide),
        (square_products_access h).2.1 3 (by decide),
        (square_products_access h).2.1 4 (by decide),
        (square_products_access h).2.1 5 (by decide),
        (square_products_access h).2.1 6 (by decide)]
end

private theorem limb_drop_getD (xs : List (BitVec 64)) (n i : Nat) :
    (xs.drop n).getD i 0 = xs.getD (n + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem square_diagonal_registers (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := diagonalSeed d x blocks
    squareRegisters d s ∧ s.regs.get64 .rbp = 16 - d.regs.get64 .r9 ∧
      s.regs.get64 .r14 = 0 ∧ s.regs.get64 .r15 = 0 := by
  simp [squareRegisters, diagonalSeed, productsSeed, outerSeed, firstDoneSeed, firstSeed]

private theorem square_shift_counter {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let n := 2 * blocks - 1
    0 < n ∧ 64 * n + 64 < 2 ^ 63 ∧
    (diagonalSeed d x blocks).regs.get64 .rbp + 16 = shiftOffset n 0 ∧
    shiftIndex n ((diagonalSeed d x blocks).regs.get64 .rbp + 16) = 0 := by
  have hp := h.positive
  have hb := h.sizeBound
  have hn : 32 * (2 * blocks - 1) + 32 = 64 * blocks := by omega
  have he : (diagonalSeed d x blocks).regs.get64 .rbp + 16 =
      0#64 - BitVec.ofNat 64 (32 * (2 * blocks - 1)) := by
    rw [(square_diagonal_registers d x blocks).2.1, h.size, ← hn, BitVec.ofNat_add]; grind
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [he, shift_counter_zero]
  · rw [he]; exact shift_counter_initial _ (by omega) (by omega)

private theorem square_bootstrap_access {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let s := diagonalSeed d x blocks
    let t := snapshotLimbs s.dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)
    (∀ j < 3, s.dmem.loadInt (s.regs.get64 .rsi + s.regs.get64 .rbp + (-16#64) + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD j 0).toInt))) ∧
    (∀ j < 6, s.dmem.loadInt (s.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (t.getD j 0).toInt))) ∧
    shiftPreambleDisjoint (s.regs.get64 .rsi + s.regs.get64 .rbp) (s.regs.get64 .rsp) := by
  let s := diagonalSeed d x blocks
  have hp := h.positive
  have hr := square_diagonal_registers d x blocks
  have hm := (diagonal_seed_writes h).square_memory h h.memory
  have ha : s.regs.get64 .rsi + s.regs.get64 .rbp = d.regs.get64 .rsi + 16 := by
    rw [hr.1.2.2.1, hr.2.1]; grind
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [ha, show d.regs.get64 .rsi + 16 + (-16#64) = d.regs.get64 .rsi from by grind]
    exact square_memory_load hm (by rw [h.inputLength]; have := h.sizeBound; omega) j
      (by rw [h.inputLength]; omega)
  · intro j hj
    rw [hr.1.1, snapshot_getD _ _ _ _ (by omega)]
    apply read_word_load
    have ha : d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (8 * j) =
        d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + j)) := by
      simp only [Nat.mul_add, BitVec.ofNat_add]; grind
    rw [ha]
    exact square_memory_mapped h hm _ (by omega)
  · dsimp only [shiftPreambleDisjoint, shiftFrameDisjoint, shiftWindowsDisjoint]
    rw [ha, hr.1.1]
    intro u hu v hv
    have hd := square_memory_disjoint hm (8 + u) (by rw [h.inputLength]; omega) v (by omega)
    have ha' : d.regs.get64 .rsi + 16 + (-8#64) + BitVec.ofNat 64 u =
        d.regs.get64 .rsi + BitVec.ofNat 64 (8 + u) := by
      simp only [BitVec.ofNat_add]; grind
    have hb' : d.regs.get64 .rsp + 88 + (-32#64) + BitVec.ofNat 64 v =
        d.regs.get64 .rsp + 56 + BitVec.ofNat 64 v := by grind
    rw [ha', hb']
    exact hd

private theorem shift_seed_fields (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := diagonalSeed d x blocks
    let t := snapshotLimbs s.dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)
    let r := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0
    let out := shiftSeed d x blocks
    out.regs.get64 .rsp = s.regs.get64 .rsp ∧ out.regs.get64 .r9 = s.regs.get64 .r9 ∧
    out.regs.get64 .rsi = s.regs.get64 .rsi ∧ out.zmms = s.zmms ∧
    out.regs.get64 .rbp = s.regs.get64 .rbp + 16 ∧ out.regs.get64 .rdi = s.regs.get64 .rsp + 120 ∧
    out.regs.get64 .rax = x.getD 2 0 ∧ out.regs.get64 .r10 = t.getD 4 0 ∧ out.regs.get64 .r11 = t.getD 5 0 ∧
    out.regs.get64 .r14 = r.2.shiftCarry ∧ out.regs.get64 .r15 = r.2.addCarry ∧
    out.dmem = (((s.dmem.storeInt (s.regs.get64 .rsp + 56) 8 r.1.lo.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 64) 8 r.1.hi.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 72) 8 r.2.lo.toIntOpaque).storeInt
      (s.regs.get64 .rsp + 80) 8 r.2.hi.toIntOpaque := by
  simp [shiftSeed]

private theorem shift_initial_intro (d s : MachineData) (n : Nat) (x t : List (BitVec 64))
    (hn : 0 < n) (hi : shiftIndex n (s.regs.get64 .rbp) = 0)
    (hb : s.regs.get64 .rbp = shiftOffset n 0)
    (hdi : s.regs.get64 .rdi = d.regs.get64 .rdi)
    (hsi : s.regs.get64 .rsi = d.regs.get64 .rsi) (hsp : s.regs.get64 .rsp = d.regs.get64 .rsp)
    (h9 : s.regs.get64 .r9 = d.regs.get64 .r9) (hz : s.zmms = d.zmms)
    (hcx : s.regs.get64 .rcx = 0) (hax : s.regs.get64 .rax = x.getD 0 0)
    (h10 : s.regs.get64 .r10 = t.getD 0 0) (h11 : s.regs.get64 .r11 = t.getD 1 0)
    (h14 : s.regs.get64 .r14 = d.regs.get64 .r14) (h15 : s.regs.get64 .r15 = d.regs.get64 .r15)
    (hm : s.dmem = d.dmem) : shiftLoopInvariant d n x t s := by
  simp only [shiftLoopInvariant, shiftInvariant, hi, Nat.mul_zero, Nat.zero_add,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, sqr4xShiftPrefix, sqr4xShiftFold]
  exact ⟨hn, hb, hdi, hsi, hsp, h9, hz, hcx, hax, h10, h11, h14, h15, hm⟩

section
attribute [local irreducible] diagonalSeed shiftSeed shiftAccumulator sqr4xShiftPrefix
  sqr4xDiagonalPair shiftIndex shiftOffset
attribute [local grind unfold] diagonalMatch squareRegisters
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero limb_drop_getD
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local grind =] ofInt_limb
local grind_pattern shift_initial_intro => shiftLoopInvariant d n x t s
local grind_pattern shift_seed_fields => shiftSeed d x blocks
local grind_pattern shift_prefix_zero => sqr4xShiftPrefix d x t 0
local grind_pattern square_diagonal_registers => diagonalSeed d x blocks

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem square_bootstrap_correct [CodeEnv] (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ diagonalMatch (diagonalSeed d x blocks) ⦄ sqr4x_shift_preamble
    ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_shift_n_add" ∧
        shiftLoopInvariant (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2)
          (shiftAccumulator d x blocks) s ⦄ := by
  vcgen [(fun s => sqr4x_shift_preamble_correct s
    (Int.ofBytes (Int.toBytes 8 (x.getD 0 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD 1 0).toInt))
    (Int.ofBytes (Int.toBytes 8 (x.getD 2 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD 1 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD 2 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD 3 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD 4 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 56) (16 * blocks + 1)).getD 5 0).toInt)))]
    simplifying_assumptions with finish (ematch := 16) (splits := 16)
      [square_shift_counter h, shift_seed_prefetch h, (square_bootstrap_access h).2.2,
        (square_bootstrap_access h).1 0 (by decide), (square_bootstrap_access h).1 1 (by decide),
        (square_bootstrap_access h).1 2 (by decide), (square_bootstrap_access h).2.1 0 (by decide),
        (square_bootstrap_access h).2.1 1 (by decide), (square_bootstrap_access h).2.1 2 (by decide),
        (square_bootstrap_access h).2.1 3 (by decide), (square_bootstrap_access h).2.1 4 (by decide),
        (square_bootstrap_access h).2.1 5 (by decide)]
end

private theorem shift_done_post (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    shiftLoopPost (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2)
      (shiftAccumulator d x blocks) (shiftDoneSeed d x blocks) := by
  simp [shiftLoopPost, shiftDoneSeed]

private theorem shift_done_pointer {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    (shiftDoneSeed d x blocks).regs.get64 .rdi =
      d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) := by
  have hr := (square_seed_registers d x blocks).2.2.2.2.1
  have hn : 64 * (2 * blocks - 1) + 64 = 128 * blocks := by have := h.positive; omega
  simp only [shiftDoneSeed, shiftSeed, MachineData.regs_mk, Reg64s.get64_set64]
  rw [hr.1, ← hn, BitVec.ofNat_add]; grind

private theorem square_shift_tail_access {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let s := shiftDoneSeed d x blocks
    let t := shiftAccumulator d x blocks
    let n := 2 * blocks - 1
    s.dmem.loadInt (s.regs.get64 .rsi + (-8#64)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 1) 0).toInt)) ∧
    (∀ j < 4, s.dmem.loadInt (s.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * j)) 8 =
      some (Int.ofBytes (Int.toBytes 8 (t.getD (8 * n + j) 0).toInt))) := by
  let seed := shiftSeed d x blocks
  let s := shiftDoneSeed d x blocks
  let t := shiftAccumulator d x blocks
  let n := 2 * blocks - 1
  have hp := h.positive
  have hb : 64 * n + 64 < 2 ^ 63 := by dsimp [n]; have := h.sizeBound; omega
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.2.1
  have hm := (shift_done_seed_writes h).square_memory h h.memory
  obtain ⟨R, hf⟩ := shift_seed_frame h
  have htl : t.length = 8 * n + 4 := by
    simp only [t, shiftAccumulator, List.length_take, List.length_drop, snapshot_length]
    dsimp [n]; omega
  obtain ⟨_, _, hptr, _, _, _, _, _, _, _, _, _, hmem⟩ := shift_done_post d x blocks
  refine ⟨?_, ?_⟩
  · have ha : s.regs.get64 .rsi + (-8#64) = d.regs.get64 .rsi + BitVec.ofNat 64 (8 * (8 * blocks - 1)) := by
      have hn : 8 * (8 * blocks - 1) + 8 = 64 * blocks := by omega
      rw [hr.2.2.1, h.size, ← hn, BitVec.ofNat_add]; grind
    rw [ha]
    exact square_memory_load hm (by rw [h.inputLength]; have := h.sizeBound; omega) _
      (by rw [h.inputLength]; omega)
  · intro j hj
    have ha : s.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * j) =
        seed.regs.get64 .rdi + (-32#64) + BitVec.ofNat 64 (8 * (8 * n + j)) := by
      rw [hptr]
      simp only [Nat.mul_add, BitVec.ofNat_add, show 8 * (8 * n) = 64 * n by omega]
      grind
    rw [ha, hmem]
    exact shift_prefix_output seed n (x.drop 2) t R hb htl hf n (8 * n + j) (by omega) (by omega)

private def reductionEntryMatch (r s : MachineData) : Prop :=
  s.regs.get64 .rsp = r.regs.get64 .rsp ∧ s.regs.get64 .rbp = r.regs.get64 .rbp ∧
  s.regs.get64 .r9 = r.regs.get64 .r9 ∧ s.zmms = r.zmms ∧ s.dmem = r.dmem

private theorem reduction_seed_fields (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    let s := shiftDoneSeed d x blocks
    let t := shiftAccumulator d x blocks
    let n := 2 * blocks - 1
    let r := sqr4xDiagonalPair (s.regs.get64 .rax) (x.getD (8 * blocks - 1) 0)
      (s.regs.get64 .r10) (s.regs.get64 .r11) (t.getD (8 * n + 2) 0) (t.getD (8 * n + 3) 0)
      (s.regs.get64 .r14) (s.regs.get64 .r15)
    let out := reductionSeed d x blocks
    out.regs.get64 .rsp = s.regs.get64 .rsp ∧ out.regs.get64 .r9 = s.regs.get64 .r9 ∧
    out.zmms = s.zmms ∧ out.regs.get64 .rbp = (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 ∧
    out.dmem = (((s.dmem.storeInt (s.regs.get64 .rdi + (-32#64)) 8 r.1.lo.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-24#64)) 8 r.1.hi.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-16#64)) 8 r.2.lo.toIntOpaque).storeInt
      (s.regs.get64 .rdi + (-8#64)) 8 r.2.hi.toIntOpaque := by
  simp [reductionSeed]

section
attribute [local irreducible] shiftSeed shiftDoneSeed reductionSeed sqr4xShiftPrefix sqr4xDiagonalPair
attribute [local grind unfold] shiftLoopPost reductionEntryMatch squareRegisters
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local grind =] ofInt_limb
local grind_pattern shift_done_post => shiftDoneSeed d x blocks
local grind_pattern reduction_seed_fields => reductionSeed d x blocks

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem square_shift_tail_correct [CodeEnv] (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ shiftLoopPost (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2) (shiftAccumulator d x blocks) ⦄
      sqr4x_shift_tail ⦃ fun _ s => reductionEntryMatch (reductionSeed d x blocks) s ⦄ := by
  vcgen [(fun s => sqr4x_shift_tail_correct s
    (Int.ofBytes (Int.toBytes 8 (x.getD (8 * blocks - 1) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((shiftAccumulator d x blocks).getD (8 * (2 * blocks - 1) + 2) 0).toInt))
    (Int.ofBytes (Int.toBytes 8 ((shiftAccumulator d x blocks).getD (8 * (2 * blocks - 1) + 3) 0).toInt)))]
    simplifying_assumptions with finish (ematch := 16) (splits := 16)
      [(square_seed_registers d x blocks).2.2.2.2.2.2.1, (square_shift_tail_access h).1,
        (square_shift_tail_access h).2 0 (by decide), (square_shift_tail_access h).2 1 (by decide),
        (square_shift_tail_access h).2 2 (by decide), (square_shift_tail_access h).2 3 (by decide)]
end

private theorem square_reduction_context {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ReductionContext (reductionSeed d x blocks) modulus n0 blocks := by
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.2.2
  have hp : (reductionSeed d x blocks).regs.get64 .rbp =
      (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 := by simp [reductionSeed]
  have hm := (reduction_seed_writes h).square_memory h h.memory
  refine ReductionContext.mk h.positive h.modulusLength ?_ ?_ ?_ ?_ ?_ ?_ h.inverse ?_ ?_
  · rw [hr.1]; exact h.stackBound
  · rw [hp]; exact h.modulusBound
  · rw [hr.1, hp]; exact h.disjoint
  · intro j hj
    rw [hr.1]
    exact square_memory_mapped h hm j hj
  · intro j hj
    rw [hp]
    exact hm.2.2.1 j hj
  · rw [hr.1, show (40 : BitVec 64) = BitVec.ofNat 64 (8 * 5) from rfl, hm.2.2.2 5 (by decide)]
    exact h.n0Loaded
  · rw [hr.2.2.2, hp]
  · rw [hr.2.2.2]; exact h.savedSize

private theorem square_reduction_size {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    (reductionSeed d x blocks).regs.get64 .r9 = BitVec.ofNat 64 (64 * blocks) := by
  rw [(square_seed_registers d x blocks).2.2.2.2.2.2.2.2.1]
  exact h.size

private theorem square_reduction_return {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    (reductionSeed d x blocks).retAddr = d.retAddr := by
  have hm := (reduction_seed_writes h).square_memory h h.memory
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.2.2
  have hl := hm.2.2.2 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at hl
  simp only [MachineData.retAddr, hr.1, hl]

section
attribute [local irreducible] reductionOuterIndex sqr8xReductionPrefix
attribute [local grind unfold] reductionEntryMatch reductionInitialMemory reductionOuterInvariant
attribute [local grind norm] BitVec.unsigned_eq Kraken.Fold.add_assoc_rev BitVec.add_zero
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local grind =] reduction_initial_index
local grind_pattern reduction_prefix_zero => sqr8xReductionPrefix d modulus n0 blocks 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem reduction_setup_matched [CodeEnv] (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : ReductionContext d modulus n0 blocks)
    (h_size : d.regs.get64 .r9 = BitVec.ofNat 64 (64 * blocks)) :
    ⦃ reductionEntryMatch d ⦄ sqr8x_reduction_setup ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".L8x_reduction_loop" ∧
        reductionOuterInvariant d modulus n0 blocks s ⦄ := by
  vcgen [sqr8x_reduction_setup_correct] simplifying_assumptions with
    finish (ematch := 16) (splits := 16)
      [ReductionContext.positive h, ReductionContext.stackBound h,
        ReductionContext.mapped h 1 (by omega), ReductionContext.mapped h 2 (by omega)]
end

private theorem first_stage_cycle [CodeEnv] (d s0 : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ firstLoopInvariant (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) s ⦄ sqr4x_first_cycle
    ⦃ fun _ s => firstLoopPost (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) s;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_1st" ∧
        firstLoopInvariant (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) s ∧
        2 ^ 64 - (s.regs.get64 .rcx).toNat < 2 ^ 64 - (s0.regs.get64 .rcx).toNat ⦄ :=
  first_cycle_correct (firstSeed d x blocks) s0 (4 * blocks - 2) (x.drop 4)
    (firstAccumulator d x blocks) (by have := h.sizeBound; omega)
    (by have := h.positive; omega) (by rw [List.length_drop, h.inputLength]; have := h.positive; omega)
    (by simp only [firstAccumulator, List.length_take, List.length_drop, snapshot_length]; omega)
    (Classical.choose (first_seed_frame h)) (Classical.choose_spec (first_seed_frame h))

private theorem outer_stage_entry [CodeEnv] (d s0 : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ outerLoopInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s ⦄ sqr4x_outer_preamble
    ⦃ fun _ _ => False;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_inner" ∧
        outerBodyInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s ∧
        sqr4x_outer_var ".Lsqr4x_inner" s < sqr4x_outer_var ".Lsqr4x_outer" s0 ⦄ :=
  outer_entry_correct (outerSeed d x blocks) s0 (4 * blocks - 3) (x.drop 2)
    (outerAccumulator d x blocks) (by have := h.sizeBound; omega)
    (by rw [List.length_drop, h.inputLength]; have := h.positive; omega)
    (Classical.choose (outer_seed_frame h)) (Classical.choose_spec (outer_seed_frame h))

private theorem outer_stage_cycle [CodeEnv] (d s0 : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ outerBodyInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s ⦄ sqr4x_outer_cycle
    ⦃ fun _ s => outerLoopPost (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s;
      fun pc s =>
        (pc = (_root_.Executable.labels cenv).label ".Lsqr4x_inner" ∧ outerBodyInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s ∧
          sqr4x_outer_var ".Lsqr4x_inner" s < sqr4x_outer_var ".Lsqr4x_inner" s0) ∨
        (pc = (_root_.Executable.labels cenv).label ".Lsqr4x_outer" ∧ outerLoopInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s ∧
          sqr4x_outer_var ".Lsqr4x_outer" s < sqr4x_outer_var ".Lsqr4x_inner" s0) ⦄ :=
  outer_cycle_correct (outerSeed d x blocks) s0 (4 * blocks - 3) (x.drop 2)
    (outerAccumulator d x blocks) (by have := h.sizeBound; omega)
    (by rw [List.length_drop, h.inputLength]; have := h.positive; omega)
    (Classical.choose (outer_seed_frame h)) (Classical.choose_spec (outer_seed_frame h))

private theorem shift_stage_cycle [CodeEnv] (d s0 : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ⦃ fun s => s = s0 ∧ shiftLoopInvariant (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2) (shiftAccumulator d x blocks) s ⦄ sqr4x_shift_cycle
    ⦃ fun _ s => shiftLoopPost (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2) (shiftAccumulator d x blocks) s;
      fun pc s => pc = (_root_.Executable.labels cenv).label ".Lsqr4x_shift_n_add" ∧
        shiftLoopInvariant (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2) (shiftAccumulator d x blocks) s ∧
        2 ^ 64 - (s.regs.get64 .rbp).toNat < 2 ^ 64 - (s0.regs.get64 .rbp).toNat ⦄ :=
  shift_cycle_correct (shiftSeed d x blocks) s0 (2 * blocks - 1) (x.drop 2)
    (shiftAccumulator d x blocks) (by have := h.sizeBound; omega)
    (by rw [List.length_drop, h.inputLength]; have := h.positive; omega)
    (by simp only [shiftAccumulator, List.length_take, List.length_drop, snapshot_length]; have := h.positive; omega)
    (Classical.choose (shift_seed_frame h)) (Classical.choose_spec (shift_seed_frame h))

private theorem full_view : Program.view bn_sqr8x_internal_prog =
    ([], [("__bn_sqr8x_internal", sqr4x_first_preamble),
      (".Lsqr4x_1st", sqr4x_first_cycle ++ sqr4x_first_tail),
      (".Lsqr4x_outer", sqr4x_outer_preamble),
      (".Lsqr4x_inner", sqr4x_outer_cycle ++ (sqr4x_final_products ++ sqr4x_shift_preamble)),
      (".Lsqr4x_shift_n_add", sqr4x_shift_cycle ++ sqr4x_shift_tail),
      ("__bn_sqr8x_reduction", sqr8x_reduction_setup),
      (".L8x_reduction_loop", sqr8x_reduction_entry),
      (".L8x_reduce", sqr8x_reduce_cycle ++ sqr8x_reduce_tail),
      (".L8x_tail", sqr8x_tail_cycle ++ sqr8x_tail_advance),
      (".L8x_tail_done", sqr8x_tail_carry),
      (".L8x_no_tail", sqr8x_reduction_finish)]) := by
  decide

private abbrev fullTable (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : Label → MachineData → Prop
  | "__bn_sqr8x_internal", s => s = d
  | ".Lsqr4x_1st", s => firstLoopInvariant (firstSeed d x blocks) (4 * blocks - 2) (x.drop 4) s
  | ".Lsqr4x_outer", s => outerLoopInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s
  | ".Lsqr4x_inner", s => outerBodyInvariant (outerSeed d x blocks) (4 * blocks - 3) (x.drop 2) (outerAccumulator d x blocks) s
  | ".Lsqr4x_shift_n_add", s => shiftLoopInvariant (shiftSeed d x blocks) (2 * blocks - 1) (x.drop 2) (shiftAccumulator d x blocks) s
  | "__bn_sqr8x_reduction", s => reductionEntryMatch (reductionSeed d x blocks) s
  | l, s => reductionTable (reductionSeed d x blocks) modulus n0 blocks l s

private abbrev squarePhaseRank : Nat := (2 ^ 64) ^ 3

private abbrev fullVar (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : Label → MachineData → Nat
  | "__bn_sqr8x_internal", _ => 4 * squarePhaseRank
  | ".Lsqr4x_1st", s => 3 * squarePhaseRank + (2 ^ 64 - (s.regs.get64 .rcx).toNat)
  | ".Lsqr4x_outer", s => 2 * squarePhaseRank + sqr4x_outer_var ".Lsqr4x_outer" s
  | ".Lsqr4x_inner", s => 2 * squarePhaseRank + sqr4x_outer_var ".Lsqr4x_inner" s
  | ".Lsqr4x_shift_n_add", s => squarePhaseRank + (2 ^ 64 - (s.regs.get64 .rbp).toNat)
  | l, s => reductionVar (reductionSeed d x blocks) blocks l s

private theorem square_rank_bounds (s : MachineData) :
    sqr4x_outer_var ".Lsqr4x_outer" s < squarePhaseRank ∧
    sqr4x_outer_var ".Lsqr4x_inner" s < squarePhaseRank := by
  simp only [sqr4x_outer_var, squarePhaseRank]
  simp
  omega

/-- Exact result of the internal routine, including its returned carry word,
workspace contents, restored modulus pointer, and stack return. -/
def bnSqr8xPost (d : MachineData) (x modulus : List (BitVec 64)) (n0 : BitVec 64)
    (blocks : Nat) (s : MachineData) : Prop :=
  s.regs.get64 .rax = (bnSqr8xResult d x modulus n0 blocks).carry ∧
  s.dmem = (bnSqr8xResult d x modulus n0 blocks).memory ∧
  s.regs.get64 .rsp = d.regs.get64 .rsp + 8 ∧ s.zmms = d.zmms ∧
  s.regs.get64 .rbp = (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 ∧
  s.regs.get64 .r9 = -BitVec.ofNat 64 (64 * blocks) ∧
  s.regs.get64 .rdi = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rdx = d.regs.get64 .rsp + 56 + BitVec.ofNat 64 (128 * blocks) ∧
  s.regs.get64 .rsi = 0

private theorem reduction_post_full (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (s : MachineData)
    (hp : reductionResultPost (reductionSeed d x blocks) modulus n0 blocks s) :
    bnSqr8xPost d x modulus n0 blocks s := by
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.2.2
  have hb : (reductionSeed d x blocks).regs.get64 .rbp =
      (d.zmms.get (.xmm .mm2)).extractLsb' 0 64 := by simp [reductionSeed]
  dsimp only [bnSqr8xPost, bnSqr8xResult, reductionResultPost, squareRegisters] at *
  grind only

private theorem read_limbs_snapshot (mem : DataMem) (a : BitVec 64) (n : Nat)
    (hm : ∀ i < n, (mem.loadInt (a + BitVec.ofNat 64 (8 * i)) 8).isSome = true) :
    BnSqr8x.readLimbs mem a n = some (snapshotLimbs mem a n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : (mem.loadInt a 8).isSome = true := by simpa using hm 0 (by omega)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h0
    have ht : ∀ i < n, (mem.loadInt (a + 8 + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
      intro i hi
      have he : a + 8 + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (i + 1)) := by
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
        grind
      rw [he]
      exact hm (i + 1) (by omega)
    simp only [BnSqr8x.readLimbs, hv, Option.bind_some, ih _ ht, snapshot_cons,
      readWord, Option.getD_some, pure, bind]

/-- The `N = 8 * blocks` low output limbs of the verified arithmetic fold. -/
def bnSqr8xResultLimbs (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : List (BitVec 64) :=
  snapshotLimbs (bnSqr8xResult d x modulus n0 blocks).memory
    (BnSqr8x.outputAddress (d.regs.get64 .rsp) (8 * blocks)) (8 * blocks)

/-- The complete numerical fold result, including the returned high carry. -/
def bnSqr8xResultValue (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) : Nat :=
  BnSqr8x.limbsToNat (bnSqr8xResultLimbs d x modulus n0 blocks) +
    BnSqr8x.radix (8 * blocks) * (bnSqr8xResult d x modulus n0 blocks).carry.toNat

private theorem bnSqr8xResult_mapped {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    ∀ i < 8 * blocks,
      ((bnSqr8xResult d x modulus n0 blocks).memory.loadInt
        (BnSqr8x.outputAddress (d.regs.get64 .rsp) (8 * blocks) + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  let seed := reductionSeed d x blocks
  have hm := (reduction_seed_writes h).square_memory h (BnSqr8xBlockContext.memory h)
  have hinit : Mem.SubDom seed.dmem (reductionInitialMemory seed blocks) :=
    ((Mem.SubDom.refl _).storeInt _ _ _).storeInt _ _ _
  have hf := reduction_fold_subdom modulus n0 (seed.regs.get64 .rsp) blocks
    (Sqr8xReductionState.mk 0 (reductionInitialMemory seed blocks)) blocks
  have hs : Mem.SubDom d.dmem (bnSqr8xResult d x modulus n0 blocks).memory :=
    subdom_trans hm.2.1 (subdom_trans hinit hf)
  intro i hi
  have ha : BnSqr8x.outputAddress (d.regs.get64 .rsp) (8 * blocks) + BitVec.ofNat 64 (8 * i) =
      d.regs.get64 .rsp + BitVec.ofNat 64 (8 * (7 + 8 * blocks + i)) := by
    simp only [BnSqr8x.outputAddress, Nat.mul_add, BitVec.ofNat_add]
    grind
  rw [ha]
  exact Mem.SubDom.loadInt_isSome hs (h.mapped _ (by omega))

/-- The exact-state contract gives a mapped numerical output at the documented
address. The arithmetic refinement `bnSqr8xResult_montgomery_square` supplies
the Montgomery-square equation for this extracted value. -/
theorem bnSqr8xPost.outputValue {d s : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (hp : bnSqr8xPost d x modulus n0 blocks s) :
    BnSqr8x.outputValue (d.regs.get64 .rsp) x.length s =
      some (bnSqr8xResultValue d x modulus n0 blocks) := by
  unfold BnSqr8x.outputValue
  rw [h.inputLength, hp.1, hp.2.1,
    read_limbs_snapshot _ _ _ (bnSqr8xResult_mapped h)]
  rfl

section Sqr8xFullCFG
attribute [local irreducible] firstSeed outerSeed shiftSeed reductionSeed sqr8xReductionPrefix
  reductionOuterIndex cancellationOuterIndex reductionBlockIndex tailOuterIndex
  cancellationPrefix tailBlocksPrefix tailBlockSum tailIterationPrefix passCarrySum passFinishSum
  passCoefficients sqr8xAddResult readWords limbBlock sqr8xReduceResult reduceCount reduceIndex reduceFrame tailFrame wordsLoaded
attribute [local grind unfold] reductionOuterInvariant cancellationInvariant cancellationDone
  reductionTailInvariant reductionTailDone reductionCarryInvariant reductionFinishInvariant reductionResultPost
attribute [local sym_simp] BitVec.zero_add CondCode.interp_nz StatusFlags.zf_from_result Option.map_none Option.map_some
attribute [local grind norm] Option.map_none Option.map_some set_low32 get_low32
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64 BitVec.unsigned_eq Kraken.Fold.add_assoc_rev
  CondCode.interp_nz StatusFlags.zf_from_result
local grind_pattern BitVec.toNat_ofNat => BitVec.ofNat w x
local grind_pattern square_rank_bounds => MachineData.regs s
local grind_pattern reduction_post_full => bnSqr8xPost d x modulus n0 blocks s

variable [layout : _root_.Layout] [Executable.ValidLayout (layout bn_sqr8x_internal_prog)]
local instance : CodeEnv := ⟨layout bn_sqr8x_internal_prog⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- Total functional correctness of the complete `__bn_sqr8x_internal` CFG
against the composed arithmetic folds, through the final return instruction.

The first postcondition (`False`) forbids normal fallthrough. The second,
after `;`, requires an exit to the saved return address with `bnSqr8xPost`.
The numerical meaning of the output is exposed by `bn_sqr8x_internal_output`.
The refinement `bn_sqr8x_internal_montgomery_square` proves the integer equation
in `BnSqr8x.MathematicalPost`. -/
theorem bn_sqr8x_internal_correct (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (ra : Int64) (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ bn_sqr8x_internal_prog ⦃ fun _ _ => False;
      fun pc s => pc = ra ∧ bnSqr8xPost d x modulus n0 blocks s ⦄ := by
  apply MachineWP.cfg_exit (fullTable d x modulus n0 blocks) (fullVar d x blocks)
  cfg_cases [full_view]
  · vcgen [square_start_correct d x modulus n0 blocks h] simplifying_assumptions with
      finish (splits := 16)
  · vcgen [(fun s => first_stage_cycle d s x modulus n0 blocks h),
        square_first_tail_correct d x modulus n0 blocks h] simplifying_assumptions with
      finish (splits := 16)
  · vcgen [(fun s => outer_stage_entry d s x modulus n0 blocks h)] simplifying_assumptions with
      finish (splits := 16)
  · vcgen [(fun s => outer_stage_cycle d s x modulus n0 blocks h),
        square_products_correct d x modulus n0 blocks h, square_bootstrap_correct d x modulus n0 blocks h]
      simplifying_assumptions with finish (splits := 16)
  · vcgen [(fun s => shift_stage_cycle d s x modulus n0 blocks h),
        square_shift_tail_correct d x modulus n0 blocks h] simplifying_assumptions with
      finish (splits := 16) [h.sizeBound]
  · vcgen [reduction_setup_matched (reductionSeed d x blocks) modulus n0 blocks
        (square_reduction_context h) (square_reduction_size h)] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [h.positive,
        ReductionContext.stackBound (square_reduction_context h),
        reduction_initial_index ((reductionSeed d x blocks).regs.get64 .rsp) blocks
          (ReductionContext.stackBound (square_reduction_context h))]
  · vcgen [(fun s => reduction_entry_establishes (reductionSeed d x blocks) s modulus n0 blocks
        (square_reduction_context h))] simplifying_assumptions with
      finish (ematch := 16) (splits := 16) [ReductionContext.stackBound (square_reduction_context h),
        reduce_index_initial, → cancellation_outer_index ((reductionSeed d x blocks).regs.get64 .rsp) blocks]
  · vcgen [(fun s => cancellation_cycle_correct (reductionSeed d x blocks) s modulus n0 blocks (square_reduction_context h)),
        (fun s => reduction_tail_establishes (reductionSeed d x blocks) s modulus n0 blocks (square_reduction_context h))]
      simplifying_assumptions with finish (ematch := 16) (splits := 16)
        [ReductionContext.stackBound (square_reduction_context h), ReductionContext.modulusBound (square_reduction_context h),
          h.positive, → cancellation_tail_pointers (square_reduction_context h)]
  · vcgen [(fun s => tail_cycle_correct (reductionSeed d x blocks) s modulus n0 blocks (square_reduction_context h)),
        (fun s => tail_advance_establishes (reductionSeed d x blocks) s modulus n0 blocks (square_reduction_context h))]
      simplifying_assumptions with finish (ematch := 16) (splits := 16)
        [ReductionContext.stackBound (square_reduction_context h), ReductionContext.modulusBound (square_reduction_context h),
          h.positive, → tail_iteration_pointers (square_reduction_context h), → tail_advance_pointers (square_reduction_context h)]
  · vcgen [(fun s => reduction_carry_establishes (reductionSeed d x blocks) s modulus n0 blocks (square_reduction_context h))]
      simplifying_assumptions with finish (splits := 16)
  · vcgen [(fun s => reduction_finish_establishes (reductionSeed d x blocks) s modulus n0 blocks ra
        (square_reduction_context h) (by rw [square_reduction_return h]; exact hret))]
      simplifying_assumptions with finish (ematch := 16) (splits := 16)
        [ReductionContext.stackBound (square_reduction_context h), h.positive,
          → reduction_finish_pointers (square_reduction_context h)]

/-- Safety and termination of the complete internal routine, obtained from its
functional contract under the same calling convention and memory assumptions. -/
theorem bn_sqr8x_internal_safe (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (ra : Int64) (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ bn_sqr8x_internal_prog ⦃ fun _ _ => False;
      fun pc _ => pc = ra ⦄ := by
  vcgen [bn_sqr8x_internal_correct d x modulus n0 blocks ra h hret] with finish
/-- Numerical form of the verified fold contract. The output read succeeds,
includes the high carry in `rax`, and agrees with `bnSqr8xResultValue`. -/
theorem bn_sqr8x_internal_output (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (ra : Int64) (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ bn_sqr8x_internal_prog ⦃ fun _ _ => False;
      fun pc s => pc = ra ∧
        BnSqr8x.outputValue (d.regs.get64 .rsp) x.length s =
          some (bnSqr8xResultValue d x modulus n0 blocks) ⦄ := by
  vcgen [bn_sqr8x_internal_correct d x modulus n0 blocks ra h hret] with
    finish [→ bnSqr8xPost.outputValue h]

end Sqr8xFullCFG

end Sqr8xFullSquaring

/-! ## Integer identities for the arithmetic folds

These lemmas interpret limbs in base `2^64`, retain the outgoing carries, and
account for the exact words written by each phase.
-/

section Sqr8xArithmetic
open BnSqr8x Std.ExtHashMap
set_option exponentiation.threshold 1024

section LimbArithmetic

private theorem limbsToNat_append (xs ys : List (BitVec 64)) :
    limbsToNat (xs ++ ys) = limbsToNat xs + radix xs.length * limbsToNat ys := by
  induction xs with
  | nil => simp [limbsToNat, radix_eq_pow]
  | cons x xs ih =>
    simp only [List.cons_append, limbsToNat, ih, List.length_cons, radix_eq_pow, Nat.pow_succ]
    grind

private theorem limbsToNat_set (xs : List (BitVec 64)) (i : Nat) (v : BitVec 64)
    (hi : i < xs.length) :
    limbsToNat (xs.set i v) + radix i * (xs.getD i 0).toNat = limbsToNat xs + radix i * v.toNat := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [limbsToNat, radix_eq_pow]; omega
    | succ i =>
      have hh := ih i (by simp only [List.length_cons] at hi; omega)
      simp only [List.set_cons_succ, limbsToNat, List.getD_cons_succ, radix_eq_pow, Nat.pow_succ] at *
      grind

private def cross : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat * (2 ^ 64) * limbsToNat xs + (2 ^ 64)^2 * cross xs

private def diagonal : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat*x.toNat + (2 ^ 64)^2 * diagonal xs

private theorem square_decomposition (xs : List (BitVec 64)) :
    limbsToNat xs * limbsToNat xs = 2 * cross xs + diagonal xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [limbsToNat, cross, diagonal]
    grind

private theorem limbsToNat_take_set (xs : List (BitVec 64)) (len i : Nat) (v : BitVec 64)
    (hi : i < len) (hlen : len ≤ xs.length) :
    limbsToNat ((xs.set i v).take len) + radix i * (xs.getD i 0).toNat =
      limbsToNat (xs.take len) + radix i * v.toNat := by
  rw [List.take_set]
  have h := limbsToNat_set (xs.take len) i v (by simp [List.length_take]; omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi] using h

private theorem limbsToNat_take_succ (xs : List (BitVec 64)) (n : Nat) (hn : n < xs.length) :
    limbsToNat (xs.take (n + 1)) = limbsToNat (xs.take n) + radix n * (xs.getD n 0).toNat := by
  rw [List.take_succ_eq_append_getElem hn, limbsToNat_append]
  simp [limbsToNat, List.length_take, Nat.min_eq_left (by omega : n ≤ xs.length),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

private theorem limbsToNat_append_two (xs : List (BitVec 64)) (len : Nat) (lo hi : BitVec 64)
    (hlen : len + 2 ≤ xs.length) :
    limbsToNat (((xs.set len lo).set (len + 1) hi).take (len + 2)) =
      limbsToNat (xs.take len) + radix len * (lo.toNat + 2 ^ 64 * hi.toNat) := by
  rw [show len + 2 = (len + 1) + 1 by omega, limbsToNat_take_succ _ _ (by simp only [List.length_set]; omega)]
  rw [limbsToNat_take_succ _ _ (by simpa using show len < xs.length from by omega)]
  simp only [List.take_set]
  have hs0 : (xs.take len).set len lo = xs.take len := List.set_eq_of_length_le (by simp; omega)
  rw [hs0]
  have hs1 : (xs.take len).set (len + 1) hi = xs.take len := List.set_eq_of_length_le (by simp; omega)
  rw [hs1]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set,
    ite_eq_left (by omega : len + 1 < xs.length), ite_eq_left (by omega : len < xs.length),
    ite_eq_left rfl, ite_eq_right (by omega : len + 1 ≠ len), Option.getD_some, radix_eq_pow, Nat.pow_succ]
  grind

private theorem cross_pair (xs : List (BitVec 64)) (hx : 2 ≤ xs.length) :
    cross xs =
      2 ^ 64 * (xs.getD 0 0).toNat * (xs.getD 1 0).toNat +
      (2 ^ 64)^2 * ((xs.getD 0 0).toNat + 2 ^ 64 * (xs.getD 1 0).toNat) * limbsToNat (xs.drop 2) +
      (2 ^ 64)^4 * cross (xs.drop 2) := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    cases xs with
    | nil => simp at hx
    | cons b xs =>
      simp only [cross, limbsToNat, List.getD_cons_zero, List.getD_cons_succ,
        List.drop_succ_cons, List.drop_zero]
      grind

private theorem limbsToNat_two_set (xs : List (BitVec 64)) (len i : Nat) (a b : BitVec 64)
    (hi : i + 2 ≤ len) (hlen : len ≤ xs.length) :
    limbsToNat (((xs.set i a).set (i + 1) b).take len) +
      radix i * ((xs.getD i 0).toNat + 2 ^ 64 * (xs.getD (i + 1) 0).toNat) =
    limbsToNat (xs.take len) + radix i * (a.toNat + 2 ^ 64 * b.toNat) := by
  have h0 := limbsToNat_take_set xs len i a (by omega) hlen
  have h1 := limbsToNat_take_set (xs.set i a) len (i + 1) b (by omega) (by simpa using hlen)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set,
    ite_eq_right (by omega : i ≠ i + 1), radix_eq_pow, Nat.pow_succ] at h0 h1 ⊢
  grind

private theorem inner_result_pending (a0 a1 previous c0 c1 x0 x1 t0 t1 : BitVec 64) :
    let r := sqr4xInnerResult a0 a1 previous c0 c1 x0 x1 t0 t1
    r.out0.toNat + 2 ^ 64 * r.out1.toNat +
      (2 ^ 64)^2 * (r.carry0.toNat + r.carry1.toNat + a1.toNat * x1.toNat) =
    t0.toNat + 2 ^ 64 * t1.toNat + c0.toNat + c1.toNat + a1.toNat * previous.toNat +
      (a0.toNat + 2 ^ 64 * a1.toNat) * (x0.toNat + 2 ^ 64 * x1.toNat) := by
  have h := sqr4xInnerResult_arithmetic a0 a1 previous c0 c1 x0 x1 t0 t1
  dsimp only at h ⊢
  grind

private theorem outer_inner_step_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n i j len : Nat) (s : Sqr4xOuterInnerState)
    (hp : 2 * i + 2 * j + 6 ≤ len) (hlen : len ≤ s.limbs.length) :
    let p := 2 * i + 2 * j + 4
    let a0 := (x.getD (2 * i) 0).toNat
    let a1 := (x.getD (2 * i + 1) 0).toNat
    let out := sqr4xOuterInnerStep x base n i j s
    limbsToNat (out.limbs.take len) +
      radix (p + 2) * (out.carry0.toNat + out.carry1.toNat + a1 * out.previous.toNat) =
    limbsToNat (s.limbs.take len) +
      radix p * (s.carry0.toNat + s.carry1.toNat + a1 * s.previous.toNat) +
      radix p * (a0 + 2 ^ 64 * a1) *
        ((x.getD (2 * j + 4) 0).toNat + 2 ^ 64 * (x.getD (2 * j + 5) 0).toNat) := by
  let p := 2 * i + 2 * j + 4
  let r := sqr4xInnerResult (x.getD (2 * i) 0) (x.getD (2 * i + 1) 0)
    s.previous s.carry0 s.carry1 (x.getD (2 * j + 4) 0) (x.getD (2 * j + 5) 0)
    (s.limbs.getD p 0) (s.limbs.getD (p + 1) 0)
  have hv := limbsToNat_two_set s.limbs len p r.out0 r.out1 (by dsimp [p]; omega) hlen
  have hr := inner_result_pending (x.getD (2 * i) 0) (x.getD (2 * i + 1) 0)
    s.previous s.carry0 s.carry1 (x.getD (2 * j + 4) 0) (x.getD (2 * j + 5) 0)
    (s.limbs.getD p 0) (s.limbs.getD (p + 1) 0)
  have he := congrArg (fun z => radix p * z) hr
  change limbsToNat (((s.limbs.set p r.out0).set (p + 1) r.out1).take len) +
    radix (p + 2) * (r.carry0.toNat + r.carry1.toNat + (x.getD (2 * i + 1) 0).toNat * (x.getD (2 * j + 5) 0).toNat) = _
  change radix p * (r.out0.toNat + 2 ^ 64 * r.out1.toNat + (2 ^ 64)^2 *
    (r.carry0.toNat + r.carry1.toNat + (x.getD (2 * i + 1) 0).toNat * (x.getD (2 * j + 5) 0).toNat)) = _ at he
  simp only [radix_eq_pow, Nat.pow_add] at hv he ⊢
  grind

private theorem limbsToNat_take_two (xs : List (BitVec 64)) (i : Nat) (hi : i + 2 ≤ xs.length) :
    limbsToNat (xs.take (i + 2)) = limbsToNat (xs.take i) +
      radix i * ((xs.getD i 0).toNat + 2 ^ 64 * (xs.getD (i + 1) 0).toNat) := by
  rw [show i + 2 = (i + 1) + 1 by omega, limbsToNat_take_succ _ _ (by omega),
    limbsToNat_take_succ _ _ (by omega)]
  simp only [radix_eq_pow, Nat.pow_succ]
  grind


end LimbArithmetic

section WordArithmetic

private def wordsValue (w : Sqr8xWords) : Nat :=
  BnSqr8x.limbsToNat [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7]

private theorem reduce_result_arithmetic (q : BitVec 64) (m t : Sqr8xWords) :
    (sqr4xMac m.w0 q t.w0 0).1.toNat +
      2 ^ 64 * wordsValue (sqr8xReduceResult q m t) =
    wordsValue t + q.toNat * wordsValue m := by
  let p0 := sqr4xMac m.w0 q t.w0 0
  let p1 := sqr4xMac m.w1 q t.w1 p0.2
  let p2 := sqr4xMac m.w2 q t.w2 p1.2
  let p3 := sqr4xMac m.w3 q t.w3 p2.2
  let p4 := sqr4xMac m.w4 q t.w4 p3.2
  let p5 := sqr4xMac m.w5 q t.w5 p4.2
  let p6 := sqr4xMac m.w6 q t.w6 p5.2
  let p7 := sqr4xMac m.w7 q t.w7 p6.2
  have h0 := sqr4xMac_parts m.w0 q t.w0 0
  change p0.1.toNat + 2 ^ 64 * p0.2.toNat = _ at h0
  have h1 := sqr4xMac_parts m.w1 q t.w1 p0.2
  change p1.1.toNat + 2 ^ 64 * p1.2.toNat = _ at h1
  have h2 := sqr4xMac_parts m.w2 q t.w2 p1.2
  change p2.1.toNat + 2 ^ 64 * p2.2.toNat = _ at h2
  have h3 := sqr4xMac_parts m.w3 q t.w3 p2.2
  change p3.1.toNat + 2 ^ 64 * p3.2.toNat = _ at h3
  have h4 := sqr4xMac_parts m.w4 q t.w4 p3.2
  change p4.1.toNat + 2 ^ 64 * p4.2.toNat = _ at h4
  have h5 := sqr4xMac_parts m.w5 q t.w5 p4.2
  change p5.1.toNat + 2 ^ 64 * p5.2.toNat = _ at h5
  have h6 := sqr4xMac_parts m.w6 q t.w6 p5.2
  change p6.1.toNat + 2 ^ 64 * p6.2.toNat = _ at h6
  have h7 := sqr4xMac_parts m.w7 q t.w7 p6.2
  change p7.1.toNat + 2 ^ 64 * p7.2.toNat = _ at h7
  change p0.1.toNat + 2 ^ 64 * BnSqr8x.limbsToNat [p1.1, p2.1, p3.1, p4.1, p5.1, p6.1, p7.1, p7.2] = _
  simp only [wordsValue, BnSqr8x.limbsToNat, Nat.mul_add, Nat.mul_zero, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl] at *
  simp only [Nat.mul_left_comm q.toNat, Nat.mul_comm q.toNat] at *
  omega

private theorem adc_parts (a b : BitVec 64) (c : Bool) :
    (sqr4xAdc a b c).1.toNat + 2 ^ 64 * (sqr4xAdc a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  simp only [sqr4xAdc, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

private theorem add_result_arithmetic (a b : Sqr8xWords) (c : Bool) :
    wordsValue (sqr8xAddResult a b c).1 + 2 ^ 512 * (sqr8xAddResult a b c).2.toNat =
      wordsValue a + wordsValue b + c.toNat := by
  let p0 := sqr4xAdc b.w0 a.w0 c
  let p1 := sqr4xAdc b.w1 a.w1 p0.2
  let p2 := sqr4xAdc b.w2 a.w2 p1.2
  let p3 := sqr4xAdc b.w3 a.w3 p2.2
  let p4 := sqr4xAdc b.w4 a.w4 p3.2
  let p5 := sqr4xAdc b.w5 a.w5 p4.2
  let p6 := sqr4xAdc b.w6 a.w6 p5.2
  let p7 := sqr4xAdc b.w7 a.w7 p6.2
  have h0 := adc_parts b.w0 a.w0 c
  change p0.1.toNat + 2 ^ 64 * p0.2.toNat = _ at h0
  have h1 := adc_parts b.w1 a.w1 p0.2
  change p1.1.toNat + 2 ^ 64 * p1.2.toNat = _ at h1
  have h2 := adc_parts b.w2 a.w2 p1.2
  change p2.1.toNat + 2 ^ 64 * p2.2.toNat = _ at h2
  have h3 := adc_parts b.w3 a.w3 p2.2
  change p3.1.toNat + 2 ^ 64 * p3.2.toNat = _ at h3
  have h4 := adc_parts b.w4 a.w4 p3.2
  change p4.1.toNat + 2 ^ 64 * p4.2.toNat = _ at h4
  have h5 := adc_parts b.w5 a.w5 p4.2
  change p5.1.toNat + 2 ^ 64 * p5.2.toNat = _ at h5
  have h6 := adc_parts b.w6 a.w6 p5.2
  change p6.1.toNat + 2 ^ 64 * p6.2.toNat = _ at h6
  have h7 := adc_parts b.w7 a.w7 p6.2
  change p7.1.toNat + 2 ^ 64 * p7.2.toNat = _ at h7
  change BnSqr8x.limbsToNat [p0.1, p1.1, p2.1, p3.1, p4.1, p5.1, p6.1, p7.1] + 2 ^ 512 * p7.2.toNat = _
  simp only [wordsValue, BnSqr8x.limbsToNat, Nat.mul_add, Nat.mul_zero, Nat.add_zero] at *
  omega

private theorem snapshot_store_limb (mem : DataMem) (base : BitVec 64) (n i : Nat)
    (v : BitVec 64) (hi : i < n) (hb : 8 * n ≤ 2 ^ 64) :
    snapshotLimbs (mem.storeInt (base + BitVec.ofNat 64 (8 * i)) 8 v.toIntOpaque) base n =
      (snapshotLimbs mem base n).set i v := by
  apply List.ext_getElem (by simp [snapshot_length])
  intro j hj hj'
  have hjn : j < n := by simpa [snapshot_length] using hj
  have hget (mem : DataMem) : (snapshotLimbs mem base n)[j]'(by simpa [snapshot_length]) =
      readWord mem (base + BitVec.ofNat 64 (8 * j)) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (l := snapshotLimbs mem base n) (by rw [snapshot_length]; exact hjn),
      Option.getD_some] using snapshot_getD mem base n j hjn
  rw [List.getElem_set, hget]
  split
  next he =>
    subst j
    simp only [readWord, Mem.loadInt_storeInt mem (base + BitVec.ofNat 64 (8 * i)) 8 v.toIntOpaque (by decide), Option.getD_some]
    exact ofInt_limb_opaque v
  next he =>
    rw [read_word_store _ _ _ _ (stack_words_disjoint base j i (by omega) (by omega) (Ne.symm he))]
    exact (hget mem).symm

private theorem reduce_result_cancelled (q : BitVec 64) (m t : Sqr8xWords)
    (hc : m.w0 * q + t.w0 = 0) :
    2 ^ 64 * wordsValue (sqr8xReduceResult q m t) =
      wordsValue t + q.toNat * wordsValue m := by
  have hp := reduce_result_arithmetic q m t
  have hlow : (sqr4xMac m.w0 q t.w0 0).1 = 0 := by
    rw [sqr4xMac_eq]
    simpa only [macLo, bv_zero_add] using hc
  rw [hlow] at hp
  simpa using hp

private def reduceFoldCoefficient (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) : Nat → Nat
  | 0 => 0
  | k + 1 => reduceFoldCoefficient m n0 sp initial k +
      BnSqr8x.radix k * (sqr8xReduceFold m n0 sp initial k).coefficient.toNat

private theorem reduce_fold_coefficient (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (hq : initial.coefficient = initial.words.w0 * n0) (k : Nat) :
    (sqr8xReduceFold m n0 sp initial k).coefficient =
      (sqr8xReduceFold m n0 sp initial k).words.w0 * n0 := by
  cases k with
  | zero => exact hq
  | succ k => rfl

private theorem reduce_fold_coefficient_bound (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) :
    reduceFoldCoefficient m n0 sp initial k < BnSqr8x.radix k := by
  induction k with
  | zero => simp [reduceFoldCoefficient, BnSqr8x.radix_eq_pow]
  | succ k ih =>
    have hq := (sqr8xReduceFold m n0 sp initial k).coefficient.isLt
    have hmul := Nat.mul_le_mul_left (BnSqr8x.radix k) (Nat.le_sub_one_of_lt hq)
    simp only [reduceFoldCoefficient, BnSqr8x.radix_eq_pow, Nat.pow_succ] at *
    omega

private theorem reduce_fold_arithmetic (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (hq : initial.coefficient = initial.words.w0 * n0)
    (hinv : m.w0 * n0 + 1 = 0) (k : Nat) :
    BnSqr8x.radix k * wordsValue (sqr8xReduceFold m n0 sp initial k).words =
      wordsValue initial.words + wordsValue m * reduceFoldCoefficient m n0 sp initial k := by
  induction k with
  | zero => simp [sqr8xReduceFold, reduceFoldCoefficient, BnSqr8x.radix_eq_pow]
  | succ k ih =>
    have hc : m.w0 * (sqr8xReduceFold m n0 sp initial k).coefficient +
        (sqr8xReduceFold m n0 sp initial k).words.w0 = 0 := by
      rw [reduce_fold_coefficient m n0 sp initial hq]
      grind (hom := false)
    have hs := reduce_result_cancelled (sqr8xReduceFold m n0 sp initial k).coefficient m
      (sqr8xReduceFold m n0 sp initial k).words hc
    have he := congrArg (fun z => BnSqr8x.radix k * z) hs
    simp only [sqr8xReduceFold, reduceFoldCoefficient, BnSqr8x.radix_eq_pow, Nat.pow_succ] at ih he ⊢
    grind

end WordArithmetic

section MemoryArithmetic

private theorem snapshot_append (mem : DataMem) (a : BitVec 64) (n k : Nat) :
    snapshotLimbs mem a (n + k) = snapshotLimbs mem a n ++
      snapshotLimbs mem (a + BitVec.ofNat 64 (8 * n)) k := by
  induction n generalizing a with
  | zero => simp [snapshotLimbs]
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega, snapshot_cons, snapshot_cons, ih]
    simp only [List.cons_append]
    congr 2
    congr 1
    simp only [Nat.mul_succ, BitVec.ofNat_add]
    grind

private theorem snapshot_take (mem : DataMem) (a : BitVec 64) (n k : Nat) (hk : k ≤ n) :
    (snapshotLimbs mem a n).take k = snapshotLimbs mem a k := by
  rw [show n = k + (n - k) by omega, snapshot_append]
  rw [List.take_append_of_le_length (by simp [snapshot_length])]
  exact List.take_of_length_le (by simp [snapshot_length])

private theorem snapshot_store_pair_limbsToNat (mem : DataMem) (a : BitVec 64) (n : Nat)
    (lo hi : BitVec 64) (hb : 8 * (n + 2) ≤ 2 ^ 64) :
    limbsToNat (snapshotLimbs
      ((mem.storeInt (a + BitVec.ofNat 64 (8 * n)) 8 lo.toIntOpaque).storeInt
        (a + BitVec.ofNat 64 (8 * n) + 8) 8 hi.toIntOpaque) a (n + 2)) =
      limbsToNat (snapshotLimbs mem a n) + radix n * (lo.toNat + 2 ^ 64 * hi.toNat) := by
  have ha : a + BitVec.ofNat 64 (8 * n) + 8 = a + BitVec.ofNat 64 (8 * (n + 1)) := by
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  rw [ha, snapshot_store_limb _ _ _ _ _ (by omega) hb,
    snapshot_store_limb _ _ _ _ _ (by omega) hb]
  have hv := limbsToNat_append_two (snapshotLimbs mem a (n + 2)) n lo hi (by simp [snapshot_length])
  rw [List.take_of_length_le (by simp [snapshot_length]), snapshot_take mem a (n + 2) n (by omega)] at hv
  exact hv

private theorem snapshot_store_word_limbsToNat (mem : DataMem) (a : BitVec 64) (n : Nat)
    (v : BitVec 64) (hb : 8 * (n + 1) ≤ 2 ^ 64) :
    limbsToNat (snapshotLimbs (mem.storeInt (a + BitVec.ofNat 64 (8 * n)) 8 v.toIntOpaque) a (n + 1)) =
      limbsToNat (snapshotLimbs mem a n) + radix n * v.toNat := by
  rw [snapshot_store_limb _ _ _ _ _ (by omega) hb]
  have hs := limbsToNat_take_succ ((snapshotLimbs mem a (n + 1)).set n v) n (by simp [snapshot_length])
  have ht : ((snapshotLimbs mem a (n + 1)).take n).set n v =
      (snapshotLimbs mem a (n + 1)).take n := List.set_eq_of_length_le (by simp; omega)
  rw [List.take_of_length_le (by simp [snapshot_length]), List.take_set, ht,
    snapshot_take mem a (n + 1) n (by omega)] at hs
  simpa [List.getD_eq_getElem?_getD, List.getElem?_set, snapshot_length] using hs

end MemoryArithmetic

section OuterInnerArithmetic

attribute [local irreducible] sqr4xOuterInnerStep sqr4xOuterInnerFold BnSqr8x.limbsToNat BnSqr8x.radix
private theorem outer_inner_fold_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n i len : Nat) (initial : Sqr4xOuterInnerState) (k : Nat)
    (hp : 4 * i + 2 * k + 4 ≤ len) (hlen : len ≤ initial.limbs.length)
    (hx : 2 * i + 4 + 2 * k ≤ x.length) :
    let a0 := (x.getD (2 * i) 0).toNat
    let a1 := (x.getD (2 * i + 1) 0).toNat
    let out := sqr4xOuterInnerFold x base n i initial k
    limbsToNat (out.limbs.take len) +
      radix (4 * i + 2 * k + 4) * (out.carry0.toNat + out.carry1.toNat + a1 * out.previous.toNat) =
    limbsToNat (initial.limbs.take len) +
      radix (4 * i + 4) * (initial.carry0.toNat + initial.carry1.toNat + a1 * initial.previous.toNat) +
      radix (4 * i + 4) * (a0 + 2 ^ 64 * a1) * limbsToNat ((x.drop (2 * i + 4)).take (2 * k)) := by
  dsimp only
  induction k with
  | zero =>
    rw [sqr4xOuterInnerFold]
    simp only [Nat.mul_zero, Nat.add_zero, List.take_zero]
    rw [show limbsToNat [] = 0 by unfold limbsToNat; rfl]
    omega
  | succ k ih =>
    have ih := ih (by omega) (by omega)
    have hs := outer_inner_step_arithmetic x base n i (i + k) len
      (sqr4xOuterInnerFold x base n i initial k) (by omega)
      (by rw [outer_inner_fold_length]; exact hlen)
    have hv := limbsToNat_take_two (x.drop (2 * i + 4)) (2 * k) (by simp only [List.length_drop]; omega)
    simp only [limb_drop_getD] at hv
    have he := congrArg (fun z => radix (4 * i + 4) *
      ((x.getD (2 * i) 0).toNat + 2 ^ 64 * (x.getD (2 * i + 1) 0).toNat) * z) hv
    have hp0 : 2 * i + 2 * (i + k) + 4 = 4 * i + 2 * k + 4 := by omega
    have hx0 : 2 * (i + k) + 4 = 2 * i + 4 + 2 * k := by omega
    have hx1 : 2 * (i + k) + 5 = 2 * i + 4 + (2 * k + 1) := by omega
    dsimp only at hs ih ⊢
    rw [hp0, hx0, hx1] at hs
    rw [sqr4xOuterInnerFold]
    generalize sqr4xOuterInnerFold x base n i initial k = st at *
    generalize sqr4xOuterInnerStep x base n i (i + k) st = out at *
    simp only [radix_eq_pow, Nat.mul_add, Nat.mul_one, Nat.pow_add] at hs ih he ⊢
    grind only

end OuterInnerArithmetic

section OuterEndsArithmetic

private theorem limbsToNat_three_set (xs : List (BitVec 64)) (len i : Nat) (a b c : BitVec 64)
    (hi : i + 3 ≤ len) (hlen : len ≤ xs.length) :
    limbsToNat ((((xs.set i a).set (i + 1) b).set (i + 2) c).take len) +
      radix i * ((xs.getD i 0).toNat + 2 ^ 64 * (xs.getD (i + 1) 0).toNat +
        (2 ^ 64)^2 * (xs.getD (i + 2) 0).toNat) =
    limbsToNat (xs.take len) + radix i * (a.toNat + 2 ^ 64 * b.toNat + (2 ^ 64)^2 * c.toNat) := by
  have h0 := limbsToNat_two_set xs len i a b (by omega) hlen
  have h1 := limbsToNat_take_set ((xs.set i a).set (i + 1) b) len (i + 2) c (by omega) (by simpa using hlen)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set,
    ite_eq_right (by omega : i + 1 ≠ i + 2), ite_eq_right (by omega : i ≠ i + 2),
    radix_eq_pow, Nat.pow_add] at h0 h1 ⊢
  grind

private theorem outer_preamble_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n i len : Nat) (s : Sqr4xOuterState)
    (hp : 4 * i + 4 ≤ len) (hlen : len ≤ s.limbs.length) :
    let a0 := (x.getD (2 * i) 0).toNat
    let a1 := (x.getD (2 * i + 1) 0).toNat
    let out := sqr4xOuterPreambleStep x base n i s
    limbsToNat (out.limbs.take len) +
      radix (4 * i + 4) * (out.carry0.toNat + out.carry1.toNat + a1 * out.previous.toNat) =
    limbsToNat (s.limbs.take len) + radix (4 * i + 1) * a0 * a1 +
      radix (4 * i + 2) * (a0 + 2 ^ 64 * a1) *
        ((x.getD (2 * i + 2) 0).toNat + 2 ^ 64 * (x.getD (2 * i + 3) 0).toNat) := by
  let a0 := x.getD (2 * i) 0
  let a1 := x.getD (2 * i + 1) 0
  let a2 := x.getD (2 * i + 2) 0
  let a3 := x.getD (2 * i + 3) 0
  let p1 := sqr4xMac a1 a0 (s.limbs.getD (4 * i + 1) 0) 0
  let p2 := sqr4xMac a2 a0 p1.2 (s.limbs.getD (4 * i + 2) 0)
  let p3 := sqr4xMac a2 a1 0 (s.limbs.getD (4 * i + 3) 0)
  let p4 := sqr4xMac a3 a0 p2.2 p3.1
  have h1 := sqr4xMac_parts a1 a0 (s.limbs.getD (4 * i + 1) 0) 0
  have h2 := sqr4xMac_parts a2 a0 p1.2 (s.limbs.getD (4 * i + 2) 0)
  have h3 := sqr4xMac_parts a2 a1 0 (s.limbs.getD (4 * i + 3) 0)
  have h4 := sqr4xMac_parts a3 a0 p2.2 p3.1
  change p1.1.toNat + 2 ^ 64 * p1.2.toNat = _ at h1
  change p2.1.toNat + 2 ^ 64 * p2.2.toNat = _ at h2
  change p3.1.toNat + 2 ^ 64 * p3.2.toNat = _ at h3
  change p4.1.toNat + 2 ^ 64 * p4.2.toNat = _ at h4
  have hv := limbsToNat_three_set s.limbs len (4 * i + 1) p1.1 p2.1 p4.1 (by omega) hlen
  change limbsToNat ((((s.limbs.set (4 * i + 1) p1.1).set (4 * i + 2) p2.1).set (4 * i + 3) p4.1).take len) +
    radix (4 * i + 4) * (p4.2.toNat + p3.2.toNat + a1.toNat * a3.toNat) =
    limbsToNat (s.limbs.take len) + radix (4 * i + 1) * a0.toNat * a1.toNat +
    radix (4 * i + 2) * (a0.toNat + 2 ^ 64 * a1.toNat) * (a2.toNat + 2 ^ 64 * a3.toNat)
  have hs : p1.1.toNat + 2 ^ 64 * p2.1.toNat + (2 ^ 64)^2 * p4.1.toNat +
      (2 ^ 64)^3 * (p4.2.toNat + p3.2.toNat + a1.toNat * a3.toNat) =
    (s.limbs.getD (4 * i + 1) 0).toNat + 2 ^ 64 * (s.limbs.getD (4 * i + 2) 0).toNat +
      (2 ^ 64)^2 * (s.limbs.getD (4 * i + 3) 0).toNat + a0.toNat * a1.toNat +
      2 ^ 64 * (a0.toNat + 2 ^ 64 * a1.toNat) * (a2.toNat + 2 ^ 64 * a3.toNat) := by
    simp only [show (0 : BitVec 64).toNat = 0 from rfl] at h1 h3
    grind
  have he := congrArg (fun z => radix (4 * i + 1) * z) hs
  simp only [radix_eq_pow, Nat.pow_add] at hv he ⊢
  grind

private theorem outer_tail_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n i : Nat) (s : Sqr4xOuterInnerState) (hlen : 2 * i + 2 * n + 6 ≤ s.limbs.length) :
    limbsToNat ((sqr4xOuterTailStep x base n i s).limbs.take (2 * i + 2 * n + 6)) =
      limbsToNat (s.limbs.take (2 * i + 2 * n + 4)) +
      radix (2 * i + 2 * n + 4) *
        (s.carry0.toNat + s.carry1.toNat + (x.getD (2 * i + 1) 0).toNat * s.previous.toNat) := by
  let r := sqr4xMac s.previous (x.getD (2 * i + 1) 0) s.carry1 s.carry0
  have hv := limbsToNat_append_two s.limbs (2 * i + 2 * n + 4) r.1 r.2 hlen
  have hr := sqr4xMac_parts s.previous (x.getD (2 * i + 1) 0) s.carry1 s.carry0
  change r.1.toNat + 2 ^ 64 * r.2.toNat = _ at hr
  change limbsToNat (((s.limbs.set (2 * i + 2 * n + 4) r.1).set (2 * i + 2 * n + 5) r.2).take
    (2 * i + 2 * n + 6)) = _
  rw [hv, hr]
  grind

end OuterEndsArithmetic

section OuterFoldArithmetic

private theorem limbsToNat_drop_two (x : List (BitVec 64)) (i : Nat) :
    limbsToNat (x.drop i) = (x.getD i 0).toNat + 2 ^ 64 * (x.getD (i + 1) 0).toNat +
      (2 ^ 64)^2 * limbsToNat (x.drop (i + 2)) := by
  have hh (ys : List (BitVec 64)) : limbsToNat ys = (ys.getD 0 0).toNat +
      2 ^ 64 * (ys.getD 1 0).toNat + (2 ^ 64)^2 * limbsToNat (ys.drop 2) := by
    cases ys with
    | nil => simp [limbsToNat]
    | cons a ys =>
      cases ys with
      | nil => simp [limbsToNat]
      | cons b ys =>
        simp only [limbsToNat, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
        omega
  simpa only [limb_drop_getD, Nat.add_zero, List.drop_drop] using hh (x.drop i)

attribute [local irreducible] BnSqr8x.limbsToNat sqr4xOuterInnerStep sqr4xOuterInnerFold
  sqr4xOuterPreambleStep sqr4xOuterTailStep sqr4xOuterFold

private theorem outer_iteration_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n i : Nat) (s : Sqr4xOuterState) (hi : i < n)
    (hx : x.length = 2 * n + 4) (hlen : s.limbs.length = 4 * n + 8) :
    let pre := sqr4xOuterPreambleStep x base n i s
    let inner := sqr4xOuterInnerFold x base n i pre (n - i)
    let out := sqr4xOuterTailStep x base n i inner
    limbsToNat (out.limbs.take (2 * i + 2 * n + 6)) =
      limbsToNat (s.limbs.take (2 * i + 2 * n + 4)) +
      radix (4 * i + 1) * (x.getD (2 * i) 0).toNat * (x.getD (2 * i + 1) 0).toNat +
      radix (4 * i + 2) * ((x.getD (2 * i) 0).toNat + 2 ^ 64 * (x.getD (2 * i + 1) 0).toNat) *
        limbsToNat (x.drop (2 * i + 2)) := by
  let pre := sqr4xOuterPreambleStep x base n i s
  let inner := sqr4xOuterInnerFold x base n i pre (n - i)
  have hprelen : pre.limbs.length = 4 * n + 8 := by
    simp only [pre, sqr4xOuterPreambleStep, List.length_set, hlen]
  have hinnerlen : inner.limbs.length = 4 * n + 8 := by
    dsimp only [inner]
    rw [outer_inner_fold_length, hprelen]
  have hp := outer_preamble_arithmetic x base n i (2 * i + 2 * n + 4) s (by omega) (by omega)
  have hin := outer_inner_fold_arithmetic x base n i (2 * i + 2 * n + 4) pre (n - i)
    (by omega) (by omega) (by omega)
  have ht := outer_tail_arithmetic x base n i inner (by omega)
  have hv := limbsToNat_drop_two x (2 * i + 2)
  have he := congrArg (fun z => radix (4 * i + 2) *
    ((x.getD (2 * i) 0).toNat + 2 ^ 64 * (x.getD (2 * i + 1) 0).toNat) * z) hv
  have htaken : (x.drop (2 * i + 4)).take (2 * (n - i)) = x.drop (2 * i + 4) :=
    List.take_of_length_le (by simp only [List.length_drop, hx]; omega)
  dsimp only at hp hin ht ⊢
  rw [htaken, show 4 * i + 2 * (n - i) + 4 = 2 * i + 2 * n + 4 by omega] at hin
  change limbsToNat (pre.limbs.take _) + _ = _ at hp
  change limbsToNat (inner.limbs.take _) + _ = _ at hin
  change limbsToNat ((sqr4xOuterTailStep x base n i inner).limbs.take _) = _
  rw [ht]
  simp only [Nat.add_assoc, radix_eq_pow, Nat.pow_add] at hp hin he ⊢
  grind only

private theorem outer_fold_arithmetic (x : List (BitVec 64)) (base : BitVec 64)
    (n : Nat) (initial : Sqr4xOuterState) (k : Nat) (hk : k ≤ n)
    (hx : x.length = 2 * n + 4) (hlen : initial.limbs.length = 4 * n + 8) :
    limbsToNat ((sqr4xOuterFold x base n initial k).limbs.take (2 * k + 2 * n + 4)) +
      radix (4 * k) * cross (x.drop (2 * k)) =
    limbsToNat (initial.limbs.take (2 * n + 4)) + cross x := by
  induction k with
  | zero =>
    rw [sqr4xOuterFold]
    simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, radix_eq_pow, Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    have ih := ih (by omega)
    have hs := outer_iteration_arithmetic x base n k (sqr4xOuterFold x base n initial k)
      (by omega) hx (by rw [outer_fold_length]; exact hlen)
    have hc := cross_pair (x.drop (2 * k)) (by simp only [List.length_drop, hx]; omega)
    have he := congrArg (fun z => radix (4 * k) * z) hc
    simp only [limb_drop_getD, Nat.add_zero, List.drop_drop] at he
    rw [sqr4xOuterFold]
    dsimp only at hs
    simp only [show 2 * (k + 1) + 2 * n + 4 = 2 * k + 2 * n + 6 by omega]
    rw [hs]
    simp only [radix_eq_pow, Nat.pow_add, Nat.mul_add, Nat.mul_one] at ih he ⊢
    grind only

end OuterFoldArithmetic

section DiagonalArithmetic

private theorem carry_mask_bool (c : Bool) :
    (-(BitVec.ofNat 64 c.toNat) != 0) = c := by cases c <;> decide

private theorem double_pair_parts (t0 t1 sc : BitVec 64) (hsc : sc.toNat ≤ 1) :
    (BitVec.ofNat 64 (2 * t0.toNat + sc.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (2 * t1.toNat + t0.toNat / 2 ^ 63)).toNat +
      (2 ^ 64)^2 * (BitVec.ofNat 64 (t1.toNat / 2 ^ 63)).toNat =
    2 * (t0.toNat + 2 ^ 64 * t1.toNat) + sc.toNat := by
  have h0 := t0.isLt
  have h1 := t1.isLt
  simp only [BitVec.toNat_ofNat]
  omega

private theorem diagonal_result_arithmetic (x t0 t1 sc ac : BitVec 64) (hsc : sc.toNat ≤ 1) :
    let r := sqr4xDiagonalResult x t0 t1 sc ac
    r.lo.toNat + 2 ^ 64 * r.hi.toNat +
      (2 ^ 64)^2 * (r.shiftCarry.toNat + (r.addCarry != 0).toNat) =
    x.toNat*x.toNat + 2 * (t0.toNat + 2 ^ 64 * t1.toNat) + sc.toNat + (ac != 0).toNat := by
  let lo := BitVec.ofNat 64 (2 * t0.toNat + sc.toNat)
  let hi := BitVec.ofNat 64 (2 * t1.toNat + t0.toNat / 2 ^ 63)
  let a := sqr4xAdc (x * x) lo (ac != 0)
  let b := sqr4xAdc (mulHi x x) hi a.2
  have ha := adc_parts (x * x) lo (ac != 0)
  have hb := adc_parts (mulHi x x) hi a.2
  have hp := mul_wide_eq x x
  have hd := double_pair_parts t0 t1 sc hsc
  change a.1.toNat + 2 ^ 64 * a.2.toNat = _ at ha
  change b.1.toNat + 2 ^ 64 * b.2.toNat = _ at hb
  change a.1.toNat + 2 ^ 64 * b.1.toNat +
    (2 ^ 64)^2 * ((BitVec.ofNat 64 (t1.toNat / 2 ^ 63)).toNat +
      (-(BitVec.ofNat 64 b.2.toNat) != 0).toNat) = _
  rw [carry_mask_bool]
  change lo.toNat + 2 ^ 64 * hi.toNat + _ = _ at hd
  omega

private theorem diagonal_result_carry_bound (x t0 t1 sc ac : BitVec 64) :
    (sqr4xDiagonalResult x t0 t1 sc ac).shiftCarry.toNat ≤ 1 := by
  have ht := t1.isLt
  simp only [sqr4xDiagonalResult, BitVec.toNat_ofNat]
  omega

end DiagonalArithmetic

section StoredLimbArithmetic

private def storeLimbList (mem : DataMem) (base : BitVec 64) (start : Nat) : List (BitVec 64) → DataMem
  | [] => mem
  | w :: ws => storeLimbList (mem.storeInt (base + BitVec.ofNat 64 (8 * start)) 8 w.toIntOpaque) base (start + 1) ws

private theorem limbsToNat_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    limbsToNat (w :: ws) = w.toNat + 2 ^ 64 * limbsToNat ws := rfl

attribute [local irreducible] BnSqr8x.limbsToNat
private theorem store_list_append_limbsToNat (ws : List (BitVec 64)) (mem : DataMem)
    (base : BitVec 64) (start : Nat) (hb : 8 * (start + ws.length) ≤ 2 ^ 64) :
    limbsToNat (snapshotLimbs (storeLimbList mem base start ws) base (start + ws.length)) =
      limbsToNat (snapshotLimbs mem base start) + radix start * limbsToNat ws := by
  induction ws generalizing mem start with
  | nil =>
    simp only [storeLimbList, List.length_nil, Nat.add_zero]
    rw [show limbsToNat [] = 0 by unfold limbsToNat; rfl]
    omega
  | cons w ws ih =>
    have hi := ih (mem.storeInt (base + BitVec.ofNat 64 (8 * start)) 8 w.toIntOpaque)
      (start + 1) (by simp only [List.length_cons] at hb; omega)
    have hs := snapshot_store_word_limbsToNat mem base start w (by simp only [List.length_cons] at hb; omega)
    simp only [storeLimbList, List.length_cons, show start + (ws.length + 1) = start + 1 + ws.length by omega]
    rw [hi, hs]
    rw [limbsToNat_cons]
    simp only [radix_eq_pow, Nat.pow_succ]
    grind only

private theorem store_words_list (mem : DataMem) (base : BitVec 64) (start : Nat) (w : Sqr8xWords) :
    storeSqr8xWords mem (base + BitVec.ofNat 64 (8 * start)) w =
      storeLimbList mem base start [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7] := by
  have ha (j : Nat) : base + BitVec.ofNat 64 (8 * (start + j)) =
      base + BitVec.ofNat 64 (8 * start) + BitVec.ofNat 64 (8 * j) := by
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  simp only [storeLimbList, storeSqr8xWords, Nat.add_assoc, Nat.reduceAdd, ha,
    Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]

private theorem store_words_append_limbsToNat (mem : DataMem) (base : BitVec 64) (start : Nat)
    (w : Sqr8xWords) (hb : 8 * (start + 8) ≤ 2 ^ 64) :
    limbsToNat (snapshotLimbs (storeSqr8xWords mem (base + BitVec.ofNat 64 (8 * start)) w) base (start + 8)) =
      limbsToNat (snapshotLimbs mem base start) + radix start * wordsValue w := by
  rw [store_words_list]
  exact store_list_append_limbsToNat _ mem base start hb

end StoredLimbArithmetic

section ShiftBlockArithmetic

private theorem shift_result_arithmetic (x0 x1 x2 x3 : BitVec 64) (t : Sqr8xWords)
    (sc ac : BitVec 64) (hsc : sc.toNat ≤ 1) :
    let r := sqr4xShiftResult x0 x1 x2 x3 t sc ac
    wordsValue r.words + radix 8 * (r.shiftCarry.toNat + (r.addCarry != 0).toNat) =
      diagonal [x0, x1, x2, x3] + 2 * wordsValue t + sc.toNat + (ac != 0).toNat := by
  let p0 := sqr4xDiagonalResult x0 t.w0 t.w1 sc ac
  let p1 := sqr4xDiagonalResult x1 t.w2 t.w3 p0.shiftCarry p0.addCarry
  let p2 := sqr4xDiagonalResult x2 t.w4 t.w5 p1.shiftCarry p1.addCarry
  let p3 := sqr4xDiagonalResult x3 t.w6 t.w7 p2.shiftCarry p2.addCarry
  have h0 := diagonal_result_arithmetic x0 t.w0 t.w1 sc ac hsc
  have h1 := diagonal_result_arithmetic x1 t.w2 t.w3 p0.shiftCarry p0.addCarry
    (diagonal_result_carry_bound _ _ _ _ _)
  have h2 := diagonal_result_arithmetic x2 t.w4 t.w5 p1.shiftCarry p1.addCarry
    (diagonal_result_carry_bound _ _ _ _ _)
  have h3 := diagonal_result_arithmetic x3 t.w6 t.w7 p2.shiftCarry p2.addCarry
    (diagonal_result_carry_bound _ _ _ _ _)
  change p0.lo.toNat + 2 ^ 64 * p0.hi.toNat + (2 ^ 64)^2 * (p0.shiftCarry.toNat + (p0.addCarry != 0).toNat) = _ at h0
  change p1.lo.toNat + 2 ^ 64 * p1.hi.toNat + (2 ^ 64)^2 * (p1.shiftCarry.toNat + (p1.addCarry != 0).toNat) = _ at h1
  change p2.lo.toNat + 2 ^ 64 * p2.hi.toNat + (2 ^ 64)^2 * (p2.shiftCarry.toNat + (p2.addCarry != 0).toNat) = _ at h2
  change p3.lo.toNat + 2 ^ 64 * p3.hi.toNat + (2 ^ 64)^2 * (p3.shiftCarry.toNat + (p3.addCarry != 0).toNat) = _ at h3
  change limbsToNat [p0.lo, p0.hi, p1.lo, p1.hi, p2.lo, p2.hi, p3.lo, p3.hi] +
    radix 8 * (p3.shiftCarry.toNat + (p3.addCarry != 0).toNat) = _
  simp only [wordsValue, limbsToNat, diagonal, radix_eq_pow, Nat.mul_add, Nat.mul_zero, Nat.add_zero] at *
  omega

private theorem shift_result_carry_bound (x0 x1 x2 x3 : BitVec 64) (t : Sqr8xWords) (sc ac : BitVec 64) :
    (sqr4xShiftResult x0 x1 x2 x3 t sc ac).shiftCarry.toNat ≤ 1 :=
  diagonal_result_carry_bound x3 t.w6 t.w7 0 0

private theorem diagonal_append (xs ys : List (BitVec 64)) :
    diagonal (xs ++ ys) = diagonal xs + radix (2 * xs.length) * diagonal ys := by
  induction xs with
  | nil => simp [diagonal, radix_eq_pow]
  | cons x xs ih =>
    simp only [List.cons_append, diagonal, ih, List.length_cons, radix_eq_pow, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    grind only

private theorem diagonal_take_succ (xs : List (BitVec 64)) (n : Nat) (hn : n < xs.length) :
    diagonal (xs.take (n + 1)) = diagonal (xs.take n) +
      radix (2 * n) * ((xs.getD n 0).toNat * (xs.getD n 0).toNat) := by
  rw [List.take_succ_eq_append_getElem hn, diagonal_append]
  simp [diagonal, List.length_take, Nat.min_eq_left (by omega : n ≤ xs.length),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

end ShiftBlockArithmetic

section ShiftFoldArithmetic

private theorem limb_slice_eq (xs : List (BitVec 64)) (start n : Nat)
    (h : start + n ≤ xs.length) :
    (xs.drop start).take n = (List.range n).map (fun j => xs.getD (start + j) 0) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp only [List.length_take, List.length_drop] at h1; omega), Option.getD_some]

private theorem limbsToNat_take_chunk (xs : List (BitVec 64)) (start n : Nat)
    (h : start + n ≤ xs.length) :
    limbsToNat (xs.take (start + n)) = limbsToNat (xs.take start) +
      radix start * limbsToNat ((List.range n).map (fun j => xs.getD (start + j) 0)) := by
  rw [List.take_add, limbsToNat_append, limb_slice_eq xs start n h]
  rw [List.length_take, Nat.min_eq_left (by omega)]

private theorem diagonal_take_chunk (xs : List (BitVec 64)) (start n : Nat)
    (h : start + n ≤ xs.length) :
    diagonal (xs.take (start + n)) = diagonal (xs.take start) +
      radix (2 * start) * diagonal ((List.range n).map (fun j => xs.getD (start + j) 0)) := by
  rw [List.take_add, diagonal_append, limb_slice_eq xs start n h]
  rw [List.length_take, Nat.min_eq_left (by omega)]

private theorem shift_fold_carry_bound (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xShiftState) (h : initial.shiftCarry.toNat ≤ 1) (k : Nat) :
    (sqr4xShiftFold x t base initial k).shiftCarry.toNat ≤ 1 := by
  cases k with
  | zero => exact h
  | succ k => exact diagonal_result_carry_bound 0 0 (t.getD (8*k+7) 0) 0 0

attribute [local irreducible] BnSqr8x.limbsToNat diagonal sqr4xShiftFold sqr4xShiftResult
private theorem shift_fold_arithmetic (x t : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr4xShiftState) (hsc : initial.shiftCarry.toNat ≤ 1) (k : Nat)
    (hb : 64 * k ≤ 2 ^ 64) (hx : 4 * k ≤ x.length) (ht : 8 * k ≤ t.length) :
    let s := sqr4xShiftFold x t base initial k
    limbsToNat (snapshotLimbs s.memory base (8 * k)) +
      radix (8 * k) * (s.shiftCarry.toNat + (s.addCarry != 0).toNat) =
        2 * limbsToNat (t.take (8 * k)) + diagonal (x.take (4 * k)) +
          initial.shiftCarry.toNat + (initial.addCarry != 0).toNat := by
  dsimp only
  induction k with
  | zero =>
    rw [sqr4xShiftFold]
    simp only [Nat.mul_zero, snapshotLimbs, List.range_zero, List.map_nil, List.take_zero]
    rw [show limbsToNat [] = 0 by unfold limbsToNat; rfl, show diagonal [] = 0 by unfold diagonal; rfl]
    simp [radix_eq_pow]
  | succ k ih =>
    have ih := ih (by omega) (by omega) (by omega)
    let s := sqr4xShiftFold x t base initial k
    let w : Sqr8xWords := ⟨t.getD (8*k) 0, t.getD (8*k+1) 0, t.getD (8*k+2) 0,
      t.getD (8*k+3) 0, t.getD (8*k+4) 0, t.getD (8*k+5) 0, t.getD (8*k+6) 0, t.getD (8*k+7) 0⟩
    let r := sqr4xShiftResult (x.getD (4*k) 0) (x.getD (4*k+1) 0)
      (x.getD (4*k+2) 0) (x.getD (4*k+3) 0) w s.shiftCarry s.addCarry
    have ha := shift_result_arithmetic (x.getD (4*k) 0) (x.getD (4*k+1) 0)
      (x.getD (4*k+2) 0) (x.getD (4*k+3) 0) w s.shiftCarry s.addCarry
      (shift_fold_carry_bound x t base initial hsc k)
    have hs := store_words_append_limbsToNat s.memory base (8*k) r.words (by omega)
    have hv := limbsToNat_take_chunk t (8*k) 8 (by omega)
    have hd := diagonal_take_chunk x (4*k) 4 (by omega)
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, Nat.add_zero] at hv hd
    change limbsToNat (t.take (8*k+8)) = limbsToNat (t.take (8*k)) + radix (8*k) * wordsValue w at hv
    change wordsValue r.words + radix 8 * (r.shiftCarry.toNat + (r.addCarry != 0).toNat) = _ at ha
    rw [sqr4xShiftFold]
    change limbsToNat (snapshotLimbs (storeSqr8xWords s.memory (base + BitVec.ofNat 64 (64*k)) r.words) base (8*(k+1))) +
      radix (8*(k+1)) * (r.shiftCarry.toNat + (r.addCarry != 0).toNat) = _
    rw [show 64*k = 8*(8*k) by omega, show 8*(k+1) = 8*k+8 by omega, hs, hv]
    rw [show 4*(k+1) = 4*k+4 by omega, hd]
    change limbsToNat (snapshotLimbs s.memory base (8*k)) + radix (8*k) * (s.shiftCarry.toNat + (s.addCarry != 0).toNat) = _ at ih
    simp only [show 2*(4*k) = 8*k by omega, radix_eq_pow, Nat.pow_add] at ha ih ⊢
    grind only

end ShiftFoldArithmetic

section InnerFoldArithmetic

attribute [local irreducible] BnSqr8x.limbsToNat sqr4xInnerFold sqr4xInnerResult

private theorem inner_fold_arithmetic (a0 a1 : BitVec 64) (x t : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr4xInnerState) (k : Nat)
    (hb : 16 * k ≤ 2 ^ 64) (hx : 2 * k ≤ x.length) (ht : 2 * k ≤ t.length) :
    let out := sqr4xInnerFold a0 a1 x t base initial k
    limbsToNat (snapshotLimbs out.memory base (2 * k)) +
      radix (2 * k) * (out.carry0.toNat + out.carry1.toNat + a1.toNat * out.previous.toNat) =
    initial.carry0.toNat + initial.carry1.toNat + a1.toNat * initial.previous.toNat +
      (a0.toNat + 2 ^ 64 * a1.toNat) * limbsToNat (x.take (2 * k)) + limbsToNat (t.take (2 * k)) := by
  dsimp only
  induction k with
  | zero =>
    rw [sqr4xInnerFold]
    simp only [Nat.mul_zero, List.take_zero, show limbsToNat [] = 0 by unfold limbsToNat; rfl,
      show ∀ mem base, snapshotLimbs mem base 0 = [] from by intros; rfl,
      radix_eq_pow, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    have ih := ih (by omega) (by omega) (by omega)
    let st := sqr4xInnerFold a0 a1 x t base initial k
    let r := sqr4xInnerResult a0 a1 st.previous st.carry0 st.carry1
      (x.getD (2 * k) 0) (x.getD (2 * k + 1) 0) (t.getD (2 * k) 0) (t.getD (2 * k + 1) 0)
    have hr := inner_result_pending a0 a1 st.previous st.carry0 st.carry1
      (x.getD (2 * k) 0) (x.getD (2 * k + 1) 0) (t.getD (2 * k) 0) (t.getD (2 * k + 1) 0)
    have he := congrArg (fun z => radix (2 * k) * z) hr
    have hm := snapshot_store_pair_limbsToNat st.memory base (2 * k) r.out0 r.out1 (by omega)
    have hxt := limbsToNat_take_two x (2 * k) (by omega)
    have htt := limbsToNat_take_two t (2 * k) (by omega)
    have hxe := congrArg (fun z => (a0.toNat + 2 ^ 64 * a1.toNat) * z) hxt
    rw [sqr4xInnerFold]
    change limbsToNat (snapshotLimbs ((st.memory.storeInt (base + BitVec.ofNat 64 (16 * k)) 8 r.out0.toIntOpaque).storeInt
        (base + BitVec.ofNat 64 (16 * k) + 8) 8 r.out1.toIntOpaque) base (2 * (k + 1))) +
      radix (2 * (k + 1)) * (r.carry0.toNat + r.carry1.toNat + a1.toNat * (x.getD (2 * k + 1) 0).toNat) = _
    change limbsToNat (snapshotLimbs st.memory base (2 * k)) + _ = _ at ih
    change radix (2 * k) * (r.out0.toNat + 2 ^ 64 * r.out1.toNat +
      (2 ^ 64)^2 * (r.carry0.toNat + r.carry1.toNat + a1.toNat * (x.getD (2 * k + 1) 0).toNat)) = _ at he
    simp only [show 8 * (2 * k) = 16 * k by omega] at hm
    simp only [Nat.mul_add, Nat.mul_one, radix_eq_pow, Nat.pow_add] at ih he hm hxe htt ⊢
    grind only

end InnerFoldArithmetic

section TailFoldArithmetic

attribute [local irreducible] BnSqr8x.limbsToNat sqr8xTailFold sqr8xReduceResult

private theorem tail_fold_coefficient (m : Sqr8xWords) (q : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr8xReduceState)
    (hq : initial.coefficient = q.getD 0 0) (k : Nat) :
    (sqr8xTailFold m q base initial k).coefficient = q.getD k 0 := by
  cases k with
  | zero => rw [sqr8xTailFold]; exact hq
  | succ k => rw [sqr8xTailFold]

private theorem tail_fold_arithmetic (m : Sqr8xWords) (q : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr8xReduceState)
    (hq : initial.coefficient = q.getD 0 0) (k : Nat)
    (hb : 8 * k ≤ 2 ^ 64) (hlen : k ≤ q.length) :
    limbsToNat (snapshotLimbs (sqr8xTailFold m q base initial k).memory base k) +
      radix k * wordsValue (sqr8xTailFold m q base initial k).words =
    wordsValue initial.words + wordsValue m * limbsToNat (q.take k) := by
  induction k with
  | zero =>
    rw [sqr8xTailFold]
    simp only [show ∀ mem base, snapshotLimbs mem base 0 = [] from by intros; rfl,
      List.take_zero, show limbsToNat [] = 0 by unfold limbsToNat; rfl, radix_eq_pow, Nat.pow_zero,
      Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    have ih := ih (by omega) (by omega)
    let st := sqr8xTailFold m q base initial k
    let low := (sqr4xMac m.w0 st.coefficient st.words.w0 0).1
    have hs := reduce_result_arithmetic st.coefficient m st.words
    have he := congrArg (fun z => radix k * z) hs
    have hm := snapshot_store_word_limbsToNat st.memory base k low (by omega)
    have hc := tail_fold_coefficient m q base initial hq k
    have hv := limbsToNat_take_succ q k (by omega)
    have hve := congrArg (fun z => wordsValue m * z) hv
    change st.coefficient = q.getD k 0 at hc
    change radix k * (low.toNat + 2 ^ 64 * wordsValue (sqr8xReduceResult st.coefficient m st.words)) = _ at he
    rw [sqr8xTailFold]
    change limbsToNat (snapshotLimbs (st.memory.storeInt (base + BitVec.ofNat 64 (8 * k)) 8 low.toIntOpaque) base (k + 1)) +
      radix (k + 1) * wordsValue (sqr8xReduceResult st.coefficient m st.words) = _
    change limbsToNat (snapshotLimbs st.memory base k) + radix k * wordsValue st.words = _ at ih
    rw [hm]
    simp only [radix_eq_pow, Nat.pow_succ] at ih he hve ⊢
    rw [hc] at he ⊢
    grind only

end TailFoldArithmetic

section CoefficientArithmetic

attribute [local irreducible] BnSqr8x.limbsToNat sqr8xReduceFold

private theorem reduce_saved_word (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k j : Nat) (hk : k ≤ 8) (hj : j < k) :
    readWord (sqr8xReduceFold m n0 sp initial k).memory
      (sp + BitVec.ofNat 64 (112 - 8 * j)) =
    (sqr8xReduceFold m n0 sp initial j).coefficient := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [sqr8xReduceFold]
    dsimp only
    by_cases he : j = k
    · subst j
      simp only [readWord, Mem.loadInt_storeInt (sqr8xReduceFold m n0 sp initial k).memory (sp + BitVec.ofNat 64 (112 - 8 * k)) 8 (sqr8xReduceFold m n0 sp initial k).coefficient.toIntOpaque (by decide), Option.getD_some]
      exact ofInt_limb_opaque _
    · rw [read_word_store]
      · exact ih (by omega) (by omega)
      · have hd := stack_words_disjoint sp (14 - j) (14 - k) (by omega) (by omega) (by omega)
        have hj' : 112 - 8 * j = 8 * (14 - j) := by omega
        have hk' : 112 - 8 * k = 8 * (14 - k) := by omega
        simpa only [hj', hk'] using hd

private theorem saved_coefficients_get (mem : DataMem) (sp : BitVec 64) (j : Nat) (hj : j < 9) :
    (savedCoefficients mem sp).getD j 0 = readWord mem (sp + BitVec.ofNat 64 (112 - 8 * j)) := by
  simp [savedCoefficients, List.getD_eq_getElem?_getD, hj]

private theorem reduce_saved_limbsToNat (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) (hk : k ≤ 8) :
    limbsToNat ((savedCoefficients (sqr8xReduceFold m n0 sp initial 8).memory sp).take k) =
      reduceFoldCoefficient m n0 sp initial k := by
  induction k with
  | zero =>
    simp only [List.take_zero, show limbsToNat [] = 0 by unfold limbsToNat; rfl, reduceFoldCoefficient]
  | succ k ih =>
    rw [limbsToNat_take_succ _ _ (by simp only [savedCoefficients, List.length_map, List.length_range]; omega),
      ih (by omega), saved_coefficients_get _ _ k (by omega),
      reduce_saved_word m n0 sp initial 8 k (by decide) (by omega), reduceFoldCoefficient]

end CoefficientArithmetic

section MemoryFrameArithmetic

private theorem snapshot_from_limbs (mem : DataMem) (base : BitVec 64)
    (xs : List (BitVec 64)) (R : DataMem → Prop)
    (hb : 8 * xs.length < 2 ^ 64)
    (hm : mem =⋆ Eq ((xs.flatMap fun w => Int.toBytes 8 w.toInt).At base) ⋆ R) :
    snapshotLimbs mem base xs.length = xs := by
  apply List.ext_getElem
  · exact snapshot_length mem base xs.length
  · intro i hi hi'
    have hl := load_limb hm hb i hi'
    simp only [snapshotLimbs, List.getElem_map, List.getElem_range, readWord, hl,
      Option.getD_some, ofInt_limb]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

private theorem snapshot_writes_before {base : BitVec 64} {start len : Nat} {a b : DataMem}
    (h : WorkspaceWrites (base + BitVec.ofNat 64 (8 * start)) len a b)
    (hb : 8 * (start + len) ≤ 2 ^ 64) :
    snapshotLimbs b base start = snapshotLimbs a base start := by
  induction h with
  | refl => rfl
  | store prev j hj v ih =>
    rw [← ih]
    apply List.map_congr_left
    intro i hi
    have hil : i < start := List.mem_range.mp hi
    have hd := stack_words_disjoint base i (start + j) (by omega) (by omega) (by omega)
    simp only [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc] at hd
    exact read_word_store _ _ _ _ hd

private theorem snapshot_limbsToNat_append (mem : DataMem) (base : BitVec 64) (n k : Nat) :
    limbsToNat (snapshotLimbs mem base (n+k)) = limbsToNat (snapshotLimbs mem base n) +
      radix n * limbsToNat (snapshotLimbs mem (base + BitVec.ofNat 64 (8*n)) k) := by
  rw [snapshot_append, limbsToNat_append, snapshot_length]

private theorem snapshot_store_outside (mem : DataMem) (base : BitVec 64) (start n i : Nat)
    (v : Int) (hbefore : i < start ∨ start + n ≤ i)
    (hb : 8 * (start + n) ≤ 2 ^ 64) (hi : 8 * i + 8 ≤ 2 ^ 64) :
    snapshotLimbs (mem.storeInt (base + BitVec.ofNat 64 (8*i)) 8 v)
      (base + BitVec.ofNat 64 (8*start)) n =
    snapshotLimbs mem (base + BitVec.ofNat 64 (8*start)) n := by
  apply List.map_congr_left
  intro j hj
  have hjl := List.mem_range.mp hj
  have hd := stack_words_disjoint base (start + j) i (by omega) hi (by omega)
  simp only [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc] at hd
  exact read_word_store _ _ _ _ hd

private theorem snapshot_read_words (mem : DataMem) (base : BitVec 64) :
    limbsToNat (snapshotLimbs mem base 8) = wordsValue (readWords mem base) := by
  simp only [snapshotLimbs, List.range_succ, List.range_zero, List.map_append,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, Nat.add_zero,
    Nat.reduceMul, BitVec.ofNat_eq_ofNat, readWords, wordsValue]

end MemoryFrameArithmetic

section FirstPassArithmetic

attribute [local irreducible] sqr4xMac

private theorem first_preamble_arithmetic (d : MachineData) (n : Nat) (x : List (BitVec 64))
    (hr9 : d.regs.get64 .r9 = BitVec.ofNat 64 (16*n+32)) :
    let r := sqr4xFirstPreambleResult d n x
    limbsToNat (snapshotLimbs r.memory (d.regs.get64 .rsp + 64) 3) +
      radix 3 * (r.carry0.toNat + r.carry1.toNat + (x.getD 1 0).toNat * r.previous.toNat) =
      (x.getD 0 0).toNat * (x.getD 1 0).toNat +
        2^64 * ((x.getD 0 0).toNat + 2^64*(x.getD 1 0).toNat) *
          ((x.getD 2 0).toNat + 2^64*(x.getD 3 0).toNat) := by
  let a0 := x.getD 0 0
  let a1 := x.getD 1 0
  let a2 := x.getD 2 0
  let a3 := x.getD 3 0
  let p1 := sqr4xMac a1 a0 0 0
  let p2 := sqr4xMac a2 a0 p1.2 0
  let p3 := sqr4xMac a2 a1 0 0
  let p4 := sqr4xMac a3 a0 p2.2 p3.1
  have h1 := sqr4xMac_parts a1 a0 0 0
  have h2 := sqr4xMac_parts a2 a0 p1.2 0
  have h3 := sqr4xMac_parts a2 a1 0 0
  have h4 := sqr4xMac_parts a3 a0 p2.2 p3.1
  have hf := first_preamble_result_fields d n x hr9
  dsimp only at hf ⊢
  rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
  have hm := store_list_append_limbsToNat [p1.1, p2.1, p4.1] d.dmem (d.regs.get64 .rsp + 64) 0 (by simp only [List.length_cons, List.length_nil]; decide)
  simp only [storeLimbList, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, List.length_cons, List.length_nil] at hm
  dsimp only [p1, p2, p3, p4, a0, a1, a2, a3] at hm
  simp only [BitVec.ofNat_eq_ofNat] at hm ⊢
  rw [hm]
  change p1.1.toNat + 2^64*p1.2.toNat = _ at h1
  change p2.1.toNat + 2^64*p2.2.toNat = _ at h2
  change p3.1.toNat + 2^64*p3.2.toNat = _ at h3
  change p4.1.toNat + 2^64*p4.2.toNat = _ at h4
  change limbsToNat (snapshotLimbs d.dmem (d.regs.get64 .rsp + 64) 0) + radix 0 * limbsToNat [p1.1,p2.1,p4.1] +
    radix 3 * (p4.2.toNat + p3.2.toNat + a1.toNat*a3.toNat) = _
  simp only [snapshotLimbs, List.range_zero, List.map_nil, limbsToNat, radix_eq_pow,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at h1 h2 h3 h4 ⊢
  have addEq {a b c d : Nat} (h : a = b) (g : c = d) : a + c = b + d :=
    congr (congrArg Nat.add h) g
  have e := addEq h1 (addEq (congrArg (fun z => 2^64*z) h2)
    (addEq (congrArg (fun z => (2^64)^2*z) h3) (congrArg (fun z => (2^64)^2*z) h4)))
  clear h1 h2 h3 h4 hm hf
  simp only [a0, a1, a2, a3] at e ⊢
  simp only [BitVec.ofNat_eq_ofNat] at e ⊢
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_left_comm (x.getD 0 (0#64)).toNat (2^64), Nat.mul_left_comm (x.getD 1 (0#64)).toNat (2^64),
    Nat.mul_comm (x.getD 1 (0#64)).toNat (x.getD 0 (0#64)).toNat,
    Nat.mul_comm (x.getD 2 (0#64)).toNat (x.getD 0 (0#64)).toNat,
    Nat.mul_comm (x.getD 3 (0#64)).toNat (x.getD 0 (0#64)).toNat,
    Nat.mul_comm (x.getD 2 (0#64)).toNat (x.getD 1 (0#64)).toNat] at e ⊢
  omega

private theorem limbsToNat_replicate_zero (n : Nat) : limbsToNat (List.replicate n (0 : BitVec 64)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, limbsToNat_cons, ih]
    rfl

attribute [local irreducible] BnSqr8x.limbsToNat sqr4xInnerFold
private theorem first_inner_complete_arithmetic (a0 a1 : BitVec 64) (x : List (BitVec 64))
    (base : BitVec 64) (initial : Sqr4xInnerState) (n : Nat)
    (hb : 16*n+16 ≤ 2^64) (hx : x.length = 2*n) :
    let s := sqr4xInnerFold a0 a1 x (List.replicate (2*n) 0) base initial n
    let r := sqr4xMac s.previous a1 s.carry1 s.carry0
    let mem := (s.memory.storeInt (base + BitVec.ofNat 64 (16*n)) 8 r.1.toIntOpaque).storeInt
      (base + BitVec.ofNat 64 (16*n) + 8) 8 r.2.toIntOpaque
    limbsToNat (snapshotLimbs mem base (2*n+2)) =
      initial.carry0.toNat + initial.carry1.toNat + a1.toNat*initial.previous.toNat +
        (a0.toNat + 2^64*a1.toNat)*limbsToNat x := by
  dsimp only
  have hi := inner_fold_arithmetic a0 a1 x (List.replicate (2*n) 0) base initial n
    (by omega) (by omega) (by simp)
  rw [List.take_of_length_le (by omega : x.length ≤ 2*n), List.take_replicate,
    Nat.min_self, limbsToNat_replicate_zero, Nat.add_zero] at hi
  let s := sqr4xInnerFold a0 a1 x (List.replicate (2*n) 0) base initial n
  have hm := snapshot_store_pair_limbsToNat s.memory base (2*n)
    (sqr4xMac s.previous a1 s.carry1 s.carry0).1 (sqr4xMac s.previous a1 s.carry1 s.carry0).2 (by omega)
  have hr := sqr4xMac_parts (sqr4xInnerFold a0 a1 x (List.replicate (2*n) 0) base initial n).previous a1
    (sqr4xInnerFold a0 a1 x (List.replicate (2*n) 0) base initial n).carry1
    (sqr4xInnerFold a0 a1 x (List.replicate (2*n) 0) base initial n).carry0
  rw [show 16*n = 8*(2*n) by omega, hm, hr]
  dsimp only at hi
  grind only

end FirstPassArithmetic

section FirstRowArithmetic

set_option maxRecDepth 2048

attribute [local irreducible] sqr4xMac sqr4xFirstPreambleResult sqr4xInnerFold BnSqr8x.limbsToNat
private theorem first_row_arithmetic {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    limbsToNat (snapshotLimbs (outerSeed d x blocks).dmem (d.regs.get64 .rsp + 64) (8*blocks+1)) =
      (x.getD 0 0).toNat * (x.getD 1 0).toNat +
        2^64 * ((x.getD 0 0).toNat + 2^64*(x.getD 1 0).toNat) * limbsToNat (x.drop 2) := by
  let n := 4*blocks-2
  let base := d.regs.get64 .rsp + 88
  let r := sqr4xFirstPreambleResult d n x
  let initial : Sqr4xInnerState := ⟨r.previous, r.carry0, r.carry1, r.memory⟩
  let s := sqr4xInnerFold (x.getD 0 0) (x.getD 1 0) (x.drop 4) (List.replicate (2*n) 0) base initial n
  let p := sqr4xMac s.previous (x.getD 1 0) s.carry1 s.carry0
  let mem := (s.memory.storeInt (base + BitVec.ofNat 64 (16*n)) 8 p.1.toIntOpaque).storeInt
    (base + BitVec.ofNat 64 (16*n) + 8) 8 p.2.toIntOpaque
  have hp := h.positive
  have hb := h.sizeBound
  have hn : 16*n+32 = 64*blocks := by dsimp [n]; omega
  have haddr : d.regs.get64 .rsp + d.regs.get64 .r9 + 56 - BitVec.ofNat 64 (16*n) = base := by
    rw [h.size, ← hn, BitVec.ofNat_add]; dsimp [base]; grind
  have htail : d.regs.get64 .rsp + d.regs.get64 .r9 + 56 = base + BitVec.ofNat 64 (16*n) := by
    rw [h.size, ← hn, BitVec.ofNat_add]; dsimp [base]; grind
  have hmem : (outerSeed d x blocks).dmem = mem := by
    simp only [outerSeed, firstDoneSeed, firstSeed, sqr4xInnerPrefix, firstTailResult,
      MachineData.dmem_mk, MachineData.regs_mk, Reg64s.get64_set64,
      ite_true, ite_false, reduceCtorEq]
    change ((sqr4xInnerFold (x.getD 0 0) (x.getD 1 0) (x.drop 4) (List.replicate (2*n) 0)
      (d.regs.get64 .rsp + d.regs.get64 .r9 + 56 - BitVec.ofNat 64 (16*n)) initial n).memory.storeInt
      (d.regs.get64 .rsp + d.regs.get64 .r9 + 56) 8 _).storeInt
      (d.regs.get64 .rsp + d.regs.get64 .r9 + 56 + 8) 8 _ = mem
    rw [haddr, htail]
  have hnum := first_inner_complete_arithmetic (x.getD 0 0) (x.getD 1 0) (x.drop 4) base initial n
    (by dsimp [n]; omega) (by rw [List.length_drop, h.inputLength]; dsimp [n]; omega)
  change limbsToNat (snapshotLimbs mem base (2*n+2)) = _ at hnum
  have hw := inner_fold_writes (x.getD 0 0) (x.getD 1 0) (x.drop 4) (List.replicate (2*n) 0)
    base initial n (2*n+2) (by omega)
  have hw' : WorkspaceWrites base (2*n+2) r.memory mem := by
    apply WorkspaceWrites.store_at (WorkspaceWrites.store_at hw (2*n) (by omega) (by congr 2; omega) _) (2*n+1) (by omega) _ _
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    rw [show 8*(2*n) = 16*n by omega]
    simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  have hlow : snapshotLimbs mem (d.regs.get64 .rsp + 64) 3 =
      snapshotLimbs r.memory (d.regs.get64 .rsp + 64) 3 := by
    have ha : base = (d.regs.get64 .rsp + 64) + BitVec.ofNat 64 (8*3) := by dsimp [base]; grind
    rw [ha] at hw'
    exact snapshot_writes_before hw' (by dsimp [n]; omega)
  have hpre := first_preamble_arithmetic d n x (by rw [hn]; exact h.size)
  have hx' : limbsToNat (x.drop 2) = (x.getD 2 0).toNat + 2^64*(x.getD 3 0).toNat +
      (2^64)^2 * limbsToNat (x.drop 4) := by
    have hs := limbsToNat_drop_two x 2
    simpa only [Nat.reduceAdd] using hs
  rw [hmem, show 8*blocks+1 = 3+(2*n+2) by dsimp [n]; omega, snapshot_limbsToNat_append, hlow]
  have ha : d.regs.get64 .rsp + 64 + BitVec.ofNat 64 (8*3) = base := by dsimp [base]; grind
  rw [ha, hnum, hx']
  dsimp only [initial] at hnum ⊢
  dsimp only at hpre
  change limbsToNat (snapshotLimbs r.memory (d.regs.get64 .rsp + 64) 3) + radix 3 *
    (r.carry0.toNat + r.carry1.toNat + (x.getD 1 0).toNat*r.previous.toNat) = _ at hpre
  simp only [radix_eq_pow] at hpre ⊢
  grind only

end FirstRowArithmetic

section SnapshotSlices
private theorem snapshot_slice (mem : DataMem) (base : BitVec 64) (total start len : Nat)
    (h : start + len ≤ total) :
    ((snapshotLimbs mem base total).drop start).take len =
      snapshotLimbs mem (base + BitVec.ofNat 64 (8*start)) len := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, snapshot_length]; omega
  · intro i h1 h2
    simp only [snapshotLimbs, List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
end SnapshotSlices


section FinalProductArithmetic
set_option exponentiation.threshold 1024

private theorem final_products_arithmetic (x0 x1 x2 x3 t1 t2 t3 : BitVec 64) :
    wordsValue (sqr4xFinalProducts x0 x1 x2 x3 t1 t2 t3).1 =
      2 ^ 64 * t1.toNat + (2 ^ 64)^2 * t2.toNat + (2 ^ 64)^3 * t3.toNat +
        cross [x0, x1, x2, x3] := by
  let p1 := sqr4xMac x1 x0 t1 0
  let p2 := sqr4xMac x2 x0 p1.2 t2
  let p3 := sqr4xMac x2 x1 t3 0
  let p4 := sqr4xMac x3 x0 p2.2 p3.1
  let p5 := sqr4xMac x3 x1 p3.2 p4.2
  let p6 := sqr4xMac x2 x3 p5.2 0
  have h1 := sqr4xMac_parts x1 x0 t1 0
  have h2 := sqr4xMac_parts x2 x0 p1.2 t2
  have h3 := sqr4xMac_parts x2 x1 t3 0
  have h4 := sqr4xMac_parts x3 x0 p2.2 p3.1
  have h5 := sqr4xMac_parts x3 x1 p3.2 p4.2
  have h6 := sqr4xMac_parts x2 x3 p5.2 0
  change p1.1.toNat + 2 ^ 64 * p1.2.toNat = _ at h1
  change p2.1.toNat + 2 ^ 64 * p2.2.toNat = _ at h2
  change p3.1.toNat + 2 ^ 64 * p3.2.toNat = _ at h3
  change p4.1.toNat + 2 ^ 64 * p4.2.toNat = _ at h4
  change p5.1.toNat + 2 ^ 64 * p5.2.toNat = _ at h5
  change p6.1.toNat + 2 ^ 64 * p6.2.toNat = _ at h6
  change limbsToNat [0, p1.1, p2.1, p4.1, p5.1, p6.1, p6.2, 0] = _
  clear_value p1 p2 p3 p4 p5 p6
  have addEq {a b c d : Nat} (h : a = b) (g : c = d) : a + c = b + d :=
    congr (congrArg Nat.add h) g
  have e := addEq (congrArg (fun z => 2^64*z) h1)
    (addEq (congrArg (fun z => (2^64)^2*z) h2)
    (addEq (congrArg (fun z => (2^64)^3*z) h3)
    (addEq (congrArg (fun z => (2^64)^3*z) h4)
    (addEq (congrArg (fun z => (2^64)^4*z) h5)
      (congrArg (fun z => (2^64)^5*z) h6)))))
  clear h1 h2 h3 h4 h5 h6
  simp (implicitDefEqProofs := false) only [limbsToNat, cross]
  simp (implicitDefEqProofs := false) only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_left_comm x0.toNat (2^64), Nat.mul_left_comm x1.toNat (2^64), Nat.mul_left_comm x2.toNat (2^64),
    Nat.mul_comm x1.toNat x0.toNat, Nat.mul_comm x2.toNat x0.toNat, Nat.mul_comm x3.toNat x0.toNat,
    Nat.mul_comm x2.toNat x1.toNat, Nat.mul_comm x3.toNat x1.toNat] at e ⊢
  omega
end FinalProductArithmetic


section ProductsPrefixArithmetic
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048
attribute [local irreducible] BnSqr8x.limbsToNat sqr4xOuterFold

private theorem products_prefix_arithmetic {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    2^64 * limbsToNat (snapshotLimbs (productsSeed d x blocks).dmem (d.regs.get64 .rsp + 64) (16*blocks-5)) +
      radix (16*blocks-8) * cross (x.drop (8*blocks-4)) = cross x := by
  let seed := outerSeed d x blocks
  let n := 4*blocks-3
  let t := outerAccumulator d x blocks
  let base := seed.regs.get64 .rsp + seed.regs.get64 .r9*2+56
  let st := sqr4xOuterPrefix seed n (x.drop 2) t n
  have hp := h.positive
  have hb := h.sizeBound
  have hxl : (x.drop 2).length = 2*n+4 := by rw [List.length_drop, h.inputLength]; dsimp [n]; omega
  obtain ⟨R, hlen, hframe⟩ := outer_seed_frame h
  have hlen' : t.length = 4*n+8 := hlen
  have hr := (square_seed_registers d x blocks).2.2.1
  have hbase : base - BitVec.ofNat 64 (32*n+64) = d.regs.get64 .rsp + 88 := by
    have hn : 32*n+64+32 = 128*blocks := by dsimp [n]; omega
    dsimp only [base]
    rw [hr.1, hr.2.1, h.size]
    have he : BitVec.ofNat 64 (64*blocks)*2 = BitVec.ofNat 64 (128*blocks) := by
      calc
        _ = BitVec.ofNat 64 (64*blocks*2) := by
          simpa only [BitVec.ofNat_eq_ofNat] using (BitVec.ofNat_mul (n := 64) (64*blocks) 2).symm
        _ = _ := by congr 1; omega
    rw [he, ← hn, BitVec.ofNat_add]
    grind
  have hi := outer_prefix_mem_inv seed n (x.drop 2) t R (by dsimp [n]; omega) hlen' hframe n (by omega)
  have hstlen : st.limbs.length = 4*n+8 := hi.1
  have hfull : snapshotLimbs st.memory (d.regs.get64 .rsp + 88) (4*n+8) = st.limbs := by
    have hm := hi.2
    change st.memory =⋆ Eq _ ⋆ (Eq ((st.limbs.flatMap fun w => Int.toBytes 8 w.toInt).At
      (base - BitVec.ofNat 64 (32*n+64))) ⋆ R) at hm
    rw [hbase, sep_comm_l] at hm
    rw [← hstlen]
    exact snapshot_from_limbs _ _ _ _ (by rw [hstlen]; dsimp [n]; omega) hm
  have hmid : limbsToNat (snapshotLimbs st.memory (d.regs.get64 .rsp + 88) (4*n+4)) =
      limbsToNat (st.limbs.take (4*n+4)) := by
    rw [← snapshot_take _ _ (4*n+8) (4*n+4) (by omega), hfull]
  have hinit : limbsToNat (t.take (2*n+4)) =
      limbsToNat (snapshotLimbs seed.dmem (d.regs.get64 .rsp + 88) (2*n+4)) := by
    dsimp only [t, outerAccumulator]
    rw [List.take_take, Nat.min_eq_left (by dsimp [n]; omega), snapshot_slice _ _ _ _ _ (by dsimp [n]; omega)]
    congr 2
    grind
  have hw := outer_fold_writes (x.drop 2) base n ⟨t,seed.dmem⟩ n (by omega)
  rw [hbase] at hw
  have hlow : snapshotLimbs st.memory (d.regs.get64 .rsp + 64) 3 =
      snapshotLimbs seed.dmem (d.regs.get64 .rsp + 64) 3 := by
    have he : d.regs.get64 .rsp + 88 = (d.regs.get64 .rsp + 64) + BitVec.ofNat 64 (8*3) := by grind
    rw [he] at hw
    exact snapshot_writes_before (start := 3) (len := 4*n+8) hw (by dsimp [n]; omega)
  have ha := outer_fold_arithmetic (x.drop 2) base n ⟨t,seed.dmem⟩ n (by omega) hxl hlen'
  change limbsToNat (st.limbs.take (2*n+2*n+4)) + radix (4*n)*cross ((x.drop 2).drop (2*n)) =
    limbsToNat (t.take (2*n+4)) + cross (x.drop 2) at ha
  rw [show 2*n+2*n+4 = 4*n+4 by omega, ← hmid, hinit, List.drop_drop] at ha
  have hfirst := first_row_arithmetic h
  have hc := cross_pair x (by rw [h.inputLength]; omega)
  change 2^64 * limbsToNat (snapshotLimbs st.memory (d.regs.get64 .rsp + 64) (16*blocks-5)) + _ = _
  rw [show 16*blocks-5 = 3+(4*n+4) by dsimp [n]; omega, snapshot_limbsToNat_append, hlow]
  rw [show 8*blocks+1 = 3+(2*n+4) by dsimp [n]; omega, snapshot_limbsToNat_append] at hfirst
  have had : d.regs.get64 .rsp + 64 + BitVec.ofNat 64 (8*3) = d.regs.get64 .rsp + 88 := by grind
  rw [had]
  rw [had] at hfirst
  have he := congrArg (fun z => radix 4*z) ha
  have hn : 16*blocks-8 = 4+4*n := by dsimp [n]; omega
  have hxdrop : 2+2*n = 8*blocks-4 := by dsimp [n]; omega
  rw [hxdrop] at he
  rw [hn, hc]
  simp only [radix_eq_pow, Nat.pow_add] at he hfirst ⊢
  grind only
end ProductsPrefixArithmetic


section FinalCrossArithmetic
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048
attribute [local irreducible] BnSqr8x.limbsToNat

private theorem store_int_shadow (mem : DataMem) (a : BitVec 64) (v w : Int) :
    (mem.storeInt a 8 v).storeInt a 8 w = mem.storeInt a 8 w := by
  exact Mem.storeBytes_storeBytes mem a (Int.toBytes 8 v) (Int.toBytes 8 w) (by rfl)

private theorem final_stores_limbsToNat (mem : DataMem) (base : BitVec 64) (start : Nat)
    (w : Sqr8xWords) (tmp : BitVec 64) (hb : 8*(start+7) ≤ 2^64) :
    let a := base + BitVec.ofNat 64 (8*start)
    let out := ((((((((mem.storeInt (a+0) 8 w.w1.toIntOpaque).storeInt
      (a+8) 8 w.w2.toIntOpaque).storeInt (a+16) 8 w.w3.toIntOpaque).storeInt
      (a+24) 8 w.w4.toIntOpaque).storeInt (a+32) 8 tmp.toIntOpaque).storeInt
      (a+32) 8 w.w5.toIntOpaque).storeInt (a+40) 8 w.w6.toIntOpaque).storeInt
      (a+48) 8 w.w7.toIntOpaque)
    limbsToNat (snapshotLimbs out base (start+7)) =
      limbsToNat (snapshotLimbs mem base start) + radix start * limbsToNat [w.w1,w.w2,w.w3,w.w4,w.w5,w.w6,w.w7] := by
  dsimp only
  rw [store_int_shadow]
  have he := store_list_append_limbsToNat [w.w1,w.w2,w.w3,w.w4,w.w5,w.w6,w.w7] mem base start hb
  have ha (j : Nat) : base + BitVec.ofNat 64 (8*(start+j)) =
      base + BitVec.ofNat 64 (8*start) + BitVec.ofNat 64 (8*j) := by
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  simpa only [storeLimbList, List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd,
    ha, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he

private theorem products_tail_words {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let s := productsSeed d x blocks
    snapshotLimbs s.dmem (finalProductBase s) 3 =
      [s.regs.get64 .r10, s.regs.get64 .r13, s.regs.get64 .r12] := by
  let seed := outerSeed d x blocks
  let n := 4*blocks-3
  let t := outerAccumulator d x blocks
  let base := seed.regs.get64 .rsp + seed.regs.get64 .r9*2+56
  let st := sqr4xOuterPrefix seed n (x.drop 2) t n
  have hp := h.positive
  have hb := h.sizeBound
  have hxl : (x.drop 2).length = 2*n+4 := by rw [List.length_drop, h.inputLength]; dsimp [n]; omega
  obtain ⟨R, hlen, hframe⟩ := outer_seed_frame h
  have hlen' : t.length = 4*n+8 := hlen
  have hr := (square_seed_registers d x blocks).2.2.1
  have hbase : base - BitVec.ofNat 64 (32*n+64) = d.regs.get64 .rsp + 88 := by
    have hn : 32*n+64+32 = 128*blocks := by dsimp [n]; omega
    dsimp only [base]
    rw [hr.1, hr.2.1, h.size]
    have he : BitVec.ofNat 64 (64*blocks)*2 = BitVec.ofNat 64 (128*blocks) := by
      calc
        _ = BitVec.ofNat 64 (64*blocks*2) := by
          simpa only [BitVec.ofNat_eq_ofNat] using (BitVec.ofNat_mul (n := 64) (64*blocks) 2).symm
        _ = _ := by congr 1; omega
    rw [he, ← hn, BitVec.ofNat_add]
    grind
  have hi := outer_prefix_mem_inv seed n (x.drop 2) t R (by dsimp [n]; omega) hlen' hframe n (by omega)
  have hstlen : st.limbs.length = 4*n+8 := hi.1
  have hfull : snapshotLimbs st.memory (d.regs.get64 .rsp + 88) (4*n+8) = st.limbs := by
    have hm := hi.2
    change st.memory =⋆ Eq _ ⋆ (Eq ((st.limbs.flatMap fun w => Int.toBytes 8 w.toInt).At
      (base - BitVec.ofNat 64 (32*n+64))) ⋆ R) at hm
    rw [hbase, sep_comm_l] at hm
    rw [← hstlen]
    exact snapshot_from_limbs _ _ _ _ (by rw [hstlen]; dsimp [n]; omega) hm
  have haddr : finalProductBase (productsSeed d x blocks) =
      (d.regs.get64 .rsp + 88) + BitVec.ofNat 64 (8*(4*n+1)) := by
    have hs := (square_seed_registers d x blocks).2.2.2.1
    dsimp only [finalProductBase]
    rw [hs.1, hs.2.1, h.size]
    have hn : 88 + 8*(4*n+1) = 128*blocks := by dsimp [n]; omega
    have hn' := congrArg (BitVec.ofNat 64) hn
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul] at hn'
    grind
  dsimp only
  change snapshotLimbs st.memory (finalProductBase (productsSeed d x blocks)) 3 = _
  rw [haddr, ← snapshot_slice st.memory (d.regs.get64 .rsp + 88) (4*n+8) (4*n+1) 3 (by omega), hfull]
  rw [limb_slice_eq _ _ _ (by rw [hstlen]; omega)]
  simp only [show List.range 3 = [0,1,2] from rfl, List.map_cons, List.map_nil,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  rfl

private theorem final_cross_arithmetic {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    2^64 * limbsToNat (snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp + 64) (16*blocks-1)) =
      cross x := by
  let s := productsSeed d x blocks
  let r := sqr4xFinalProducts (x.getD (8*blocks-4) 0) (x.getD (8*blocks-3) 0)
    (x.getD (8*blocks-2) 0) (x.getD (8*blocks-1) 0)
    (s.regs.get64 .r10) (s.regs.get64 .r13) (s.regs.get64 .r12)
  let a := d.regs.get64 .rsp + 64
  let k := 16*blocks-8
  have hp := h.positive
  have hb := h.sizeBound
  have ha : finalProductBase s = a + BitVec.ofNat 64 (8*k) := by
    have hs := (square_seed_registers d x blocks).2.2.2.1
    dsimp only [finalProductBase, a]
    rw [hs.1, hs.2.1, h.size]
    have hn : 64+8*k = 128*blocks := by dsimp [k]; omega
    have hn' := congrArg (BitVec.ofNat 64) hn
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul] at hn'
    grind
  have ht := products_tail_words h
  change snapshotLimbs s.dmem (finalProductBase s) 3 = _ at ht
  have hf := final_products_arithmetic (x.getD (8*blocks-4) 0) (x.getD (8*blocks-3) 0)
    (x.getD (8*blocks-2) 0) (x.getD (8*blocks-1) 0)
    (s.regs.get64 .r10) (s.regs.get64 .r13) (s.regs.get64 .r12)
  have hx : x.drop (8*blocks-4) = [x.getD (8*blocks-4) 0, x.getD (8*blocks-3) 0,
      x.getD (8*blocks-2) 0, x.getD (8*blocks-1) 0] := by
    have hh := limb_slice_eq x (8*blocks-4) 4 (by rw [h.inputLength]; omega)
    rw [List.take_of_length_le (by rw [List.length_drop,h.inputLength]; omega)] at hh
    simpa only [show List.range 4 = [0,1,2,3] from rfl, List.map_cons, List.map_nil,
      show 8*blocks-4+0 = 8*blocks-4 by omega, show 8*blocks-4+1 = 8*blocks-3 by omega,
      show 8*blocks-4+2 = 8*blocks-2 by omega, show 8*blocks-4+3 = 8*blocks-1 by omega] using hh
  have hc := products_prefix_arithmetic h
  rw [← hx] at hf
  change wordsValue r.1 = _ at hf
  have hw0 : r.1.w0 = 0 := rfl
  have hv := final_stores_limbsToNat s.dmem a k r.1 r.2 (by dsimp [k]; omega)
  have hd : (diagonalSeed d x blocks).dmem =
      ((((((((s.dmem.storeInt (finalProductBase s+0) 8 r.1.w1.toIntOpaque).storeInt
      (finalProductBase s+8) 8 r.1.w2.toIntOpaque).storeInt (finalProductBase s+16) 8 r.1.w3.toIntOpaque).storeInt
      (finalProductBase s+24) 8 r.1.w4.toIntOpaque).storeInt (finalProductBase s+32) 8 r.2.toIntOpaque).storeInt
      (finalProductBase s+32) 8 r.1.w5.toIntOpaque).storeInt (finalProductBase s+40) 8 r.1.w6.toIntOpaque).storeInt
      (finalProductBase s+48) 8 r.1.w7.toIntOpaque) := rfl
  rw [show 16*blocks-1 = k+7 by dsimp [k]; omega, hd, ha]
  rw [hv]
  rw [show 16*blocks-5 = k+3 by dsimp [k]; omega, snapshot_limbsToNat_append, ← ha, ht] at hc
  unfold wordsValue at hf
  rw [limbsToNat_cons, hw0] at hf
  simp (implicitDefEqProofs := false) only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at hf
  simp (implicitDefEqProofs := false) only [limbsToNat, Nat.mul_zero, Nat.add_zero] at hc
  change 2^64 * (limbsToNat (snapshotLimbs s.dmem a k) + radix k * _) = _
  change 2^64 * (limbsToNat (snapshotLimbs s.dmem a k) + radix k * _) + radix k * _ = _ at hc
  grind only
end FinalCrossArithmetic


section TailWorkspaceArithmetic
set_option exponentiation.threshold 1024

private theorem workspace_snapshot_outside {base : BitVec 64} {start len off n : Nat} {a b : DataMem}
    (h : WorkspaceWrites (base + BitVec.ofNat 64 (8*start)) len a b)
    (ho : off+n ≤ start ∨ start+len ≤ off)
    (hb : 8*(start+len) ≤ 2^64) (hn : 8*(off+n) ≤ 2^64) :
    snapshotLimbs b (base + BitVec.ofNat 64 (8*off)) n =
      snapshotLimbs a (base + BitVec.ofNat 64 (8*off)) n := by
  induction h with
  | refl => rfl
  | store prev i hi v ih =>
    rw [← ih]
    have ha : base + BitVec.ofNat 64 (8*start) + BitVec.ofNat 64 (8*i) =
      base + BitVec.ofNat 64 (8*(start+i)) := by simp (implicitDefEqProofs := false) only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    rw [ha]
    exact snapshot_store_outside _ base off n (start+i) v (by omega) hn (by omega)

private theorem tail_fold_writes (m : Sqr8xWords) (q : List (BitVec 64)) (base : BitVec 64)
    (initial : Sqr8xReduceState) (k len : Nat) (hk : k ≤ len) :
    WorkspaceWrites base len initial.memory (sqr8xTailFold m q base initial k).memory := by
  induction k with
  | zero => exact WorkspaceWrites.refl _
  | succ k ih => exact (ih (by omega)).store k (by omega) _

private theorem tail_blocks_writes (modulus q : List (BitVec 64)) (sp : BitVec 64)
    (pass : Nat) (initial : Sqr8xBlockState) (b : Nat) :
    WorkspaceWrites (sp+56+BitVec.ofNat 64 (64*(pass+1))) (8*b) initial.memory
      (sqr8xTailBlocksFold modulus q sp pass initial b).memory := by
  induction b with
  | zero => exact WorkspaceWrites.refl _
  | succ b ih =>
    have prev : WorkspaceWrites (sp+56+BitVec.ofNat 64 (64*(pass+1))) (8*(b+1)) initial.memory
        (sqr8xTailBlocksFold modulus q sp pass initial b).memory := by
      have hh := (show WorkspaceWrites ((sp+56+BitVec.ofNat 64 (64*(pass+1))) + BitVec.ofNat 64 (8*0)) (8*b) initial.memory (sqr8xTailBlocksFold modulus q sp pass initial b).memory from by simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ih).shift (offset := 0) (total := 8*(b+1)) (by omega)
      simpa (implicitDefEqProofs := false) only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hh
    apply prev.trans
    dsimp only [sqr8xTailBlocksFold, sqr8xTailBlockStep]
    have ha : sp+56+BitVec.ofNat 64 (64*(pass+b+1)) =
      (sp+56+BitVec.ofNat 64 (64*(pass+1))) + BitVec.ofNat 64 (8*(8*b)) := by
      rw [show 64*(pass+b+1) = 64*(pass+1)+8*(8*b) by omega, BitVec.ofNat_add]
      simp (implicitDefEqProofs := false) only [BitVec.add_assoc]
    rw [ha]
    exact (tail_fold_writes _ q _ ⟨_,_,_⟩ 8 8 (by omega)).shift (offset := 8*b) (by omega)
end TailWorkspaceArithmetic


section TailBlockArithmetic
set_option exponentiation.threshold 1024
attribute [local irreducible] BnSqr8x.limbsToNat sqr8xTailFold sqr8xAddResult

private theorem limb_block_limbsToNat (xs : List (BitVec 64)) (b : Nat) (hb : 8*b+8 ≤ xs.length) :
    limbsToNat ((xs.drop (8*b)).take 8) = wordsValue (limbBlock xs b) := by
  rw [limb_slice_eq _ _ _ hb]
  simp only [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl, List.map_cons, List.map_nil, Nat.add_zero]
  rfl

private theorem tail_block_arithmetic (modulus q : List (BitVec 64)) (sp : BitVec 64)
    (pass b : Nat) (s : Sqr8xBlockState) (hq : 8 ≤ q.length) :
    let out := sp+56+BitVec.ofNat 64 (64*(pass+b+1))
    let t := sqr8xTailBlockStep modulus q sp pass b s
    limbsToNat (snapshotLimbs t.memory out 8) + radix 8 * (wordsValue t.words + (t.carry != 0).toNat) =
      limbsToNat (snapshotLimbs s.memory out 8) + wordsValue s.words + (s.carry != 0).toNat +
        wordsValue (limbBlock modulus (b+1)) * limbsToNat (q.take 8) := by
  let out := sp+56+BitVec.ofNat 64 (64*(pass+b+1))
  let sum := sqr8xAddResult s.words (readWords s.memory out) (s.carry != 0)
  have ha := add_result_arithmetic s.words (readWords s.memory out) (s.carry != 0)
  have ht := tail_fold_arithmetic (limbBlock modulus (b+1)) q out
    ⟨sum.1,q.getD 0 0,s.memory⟩ rfl 8 (by decide) hq
  dsimp only [sqr8xTailBlockStep]
  rw [carry_mask_bool, snapshot_read_words s.memory _]
  change wordsValue sum.1 + 2^512 * sum.2.toNat = _ at ha
  change limbsToNat (snapshotLimbs (sqr8xTailFold _ _ out _ 8).memory out 8) +
    radix 8 * (wordsValue (sqr8xTailFold _ _ out _ 8).words + sum.2.toNat) = _
  dsimp only [sum, out] at ht ha ⊢
  simp only [radix_eq_pow, BitVec.ofNat_eq_ofNat] at ht ha ⊢
  omega

private theorem tail_blocks_arithmetic (modulus q : List (BitVec 64)) (sp : BitVec 64)
    (pass : Nat) (initial : Sqr8xBlockState) (b : Nat)
    (hq : 8 ≤ q.length) (hm : 8*(b+1) ≤ modulus.length) (hb : 64*b ≤ 2^64) :
    let base := sp+56+BitVec.ofNat 64 (64*(pass+1))
    let t := sqr8xTailBlocksFold modulus q sp pass initial b
    limbsToNat (snapshotLimbs t.memory base (8*b)) +
      radix (8*b) * (wordsValue t.words + (t.carry != 0).toNat) =
    limbsToNat (snapshotLimbs initial.memory base (8*b)) + wordsValue initial.words + (initial.carry != 0).toNat +
      limbsToNat ((modulus.drop 8).take (8*b)) * limbsToNat (q.take 8) := by
  dsimp only
  induction b with
  | zero => simp (implicitDefEqProofs := false) only [sqr8xTailBlocksFold, Nat.mul_zero,
      snapshotLimbs, List.range_zero, List.map_nil, List.take_zero,
      show limbsToNat [] = 0 by unfold limbsToNat; rfl, radix_eq_pow, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_mul, Nat.add_zero]
  | succ b ih =>
    have ih := ih (by omega) (by omega)
    let base := sp+56+BitVec.ofNat 64 (64*(pass+1))
    let s := sqr8xTailBlocksFold modulus q sp pass initial b
    let t := sqr8xTailBlockStep modulus q sp pass b s
    have hptr : sp+56+BitVec.ofNat 64 (64*(pass+b+1)) = base+BitVec.ofNat 64 (8*(8*b)) := by
      dsimp only [base]
      rw [show 64*(pass+b+1) = 64*(pass+1)+8*(8*b) by omega, BitVec.ofNat_add]
      simp only [BitVec.add_assoc]
    have hs := tail_block_arithmetic modulus q sp pass b s hq
    dsimp only at hs
    rw [hptr] at hs
    have hw := tail_fold_writes (limbBlock modulus (b+1)) q
      (sp+56+BitVec.ofNat 64 (64*(pass+b+1)))
      ⟨(sqr8xAddResult s.words (readWords s.memory (sp+56+BitVec.ofNat 64 (64*(pass+b+1)))) (s.carry != 0)).1,q.getD 0 0,s.memory⟩ 8 8 (by omega)
    change WorkspaceWrites _ 8 s.memory t.memory at hw
    rw [hptr] at hw
    have hlo := snapshot_writes_before (start := 8*b) (len := 8) hw (by omega)
    have hnext : snapshotLimbs s.memory (base+BitVec.ofNat 64 (8*(8*b))) 8 =
        snapshotLimbs initial.memory (base+BitVec.ofNat 64 (8*(8*b))) 8 := by
      have hw' := tail_blocks_writes modulus q sp pass initial b
      change WorkspaceWrites base (8*b) initial.memory s.memory at hw'
      have hw'' : WorkspaceWrites (base+BitVec.ofNat 64 (8*0)) (8*b) initial.memory s.memory := by
        simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw'
      exact workspace_snapshot_outside hw'' (by omega) (by omega) (by omega)
    have hv : limbsToNat ((modulus.drop 8).take (8*(b+1))) =
        limbsToNat ((modulus.drop 8).take (8*b)) + radix (8*b) * wordsValue (limbBlock modulus (b+1)) := by
      rw [show 8*(b+1) = 8*b+8 by omega, List.take_add, limbsToNat_append,
        List.length_take, List.length_drop, Nat.min_eq_left (by omega), List.drop_drop]
      rw [show 8+8*b = 8*(b+1) by omega, limb_block_limbsToNat _ _ (by omega)]
    rw [sqr8xTailBlocksFold]
    change limbsToNat (snapshotLimbs t.memory base (8*(b+1))) + radix (8*(b+1))*(wordsValue t.words + (t.carry != 0).toNat) = _
    rw [show 8*(b+1) = 8*b+8 by omega, snapshot_limbsToNat_append, hlo, snapshot_limbsToNat_append]
    rw [hnext] at hs
    rw [← show 8*(b+1) = 8*b+8 by omega, hv]
    change limbsToNat (snapshotLimbs t.memory (base+BitVec.ofNat 64 (8*(8*b))) 8) + radix 8 * (wordsValue t.words + (t.carry != 0).toNat) = _ at hs
    have he := congrArg (fun z => radix (8*b)*z) hs
    change limbsToNat (snapshotLimbs s.memory base (8*b)) + radix (8*b)*(wordsValue s.words + (s.carry != 0).toNat) = limbsToNat (snapshotLimbs initial.memory base (8*b)) + wordsValue initial.words + (initial.carry != 0).toNat + _ at ih
    simp only [radix_eq_pow, Nat.pow_add, Nat.mul_add, BitVec.ofNat_eq_ofNat] at he ih ⊢
    grind (splits := 0) only
end TailBlockArithmetic


section DiagonalPairArithmetic
set_option exponentiation.threshold 1024

private theorem diagonal_pair_arithmetic (x0 x1 t0 t1 t2 t3 sc ac : BitVec 64) (hsc : sc.toNat ≤ 1) :
    let p := sqr4xDiagonalPair x0 x1 t0 t1 t2 t3 sc ac
    limbsToNat [p.1.lo,p.1.hi,p.2.lo,p.2.hi] + radix 4*(p.2.shiftCarry.toNat+(p.2.addCarry != 0).toNat) =
      2*limbsToNat [t0,t1,t2,t3]+diagonal [x0,x1]+sc.toNat+(ac != 0).toNat := by
  have h0 := diagonal_result_arithmetic x0 t0 t1 sc ac hsc
  have h1 := diagonal_result_arithmetic x1 t2 t3
    (sqr4xDiagonalResult x0 t0 t1 sc ac).shiftCarry (sqr4xDiagonalResult x0 t0 t1 sc ac).addCarry
    (diagonal_result_carry_bound x0 t0 t1 sc ac)
  have h2 := congrArg (fun z => (2^64)^2*z) h1
  dsimp only [sqr4xDiagonalPair]
  simp (implicitDefEqProofs := false) only [limbsToNat, diagonal, radix_eq_pow, Nat.mul_zero, Nat.add_zero,
    Nat.mul_add, Nat.mul_assoc] at h0 h2 ⊢
  omega

private theorem pair_stores_limbsToNat (mem : DataMem) (base : BitVec 64) (start : Nat)
    (p : Sqr4xDiagonalResult × Sqr4xDiagonalResult) (hb : 8*(start+4) ≤ 2^64) :
    let a := base+BitVec.ofNat 64 (8*start)
    limbsToNat (snapshotLimbs ((((mem.storeInt a 8 p.1.lo.toIntOpaque).storeInt (a+8) 8 p.1.hi.toIntOpaque).storeInt
      (a+16) 8 p.2.lo.toIntOpaque).storeInt (a+24) 8 p.2.hi.toIntOpaque) base (start+4)) =
      limbsToNat (snapshotLimbs mem base start) + radix start * limbsToNat [p.1.lo,p.1.hi,p.2.lo,p.2.hi] := by
  have he := store_list_append_limbsToNat [p.1.lo,p.1.hi,p.2.lo,p.2.hi] mem base start hb
  have ha (j : Nat) : base+BitVec.ofNat 64 (8*(start+j)) =
      base+BitVec.ofNat 64 (8*start)+BitVec.ofNat 64 (8*j) := by
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  simpa only [storeLimbList, List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd,ha,
    Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using he
end DiagonalPairArithmetic


section CompleteDiagonalArithmetic
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048

private def storeDiagonalPair (mem : DataMem) (a : BitVec 64)
    (p : Sqr4xDiagonalResult × Sqr4xDiagonalResult) : DataMem :=
  (((mem.storeInt a 8 p.1.lo.toIntOpaque).storeInt (a+8) 8 p.1.hi.toIntOpaque).storeInt
    (a+16) 8 p.2.lo.toIntOpaque).storeInt (a+24) 8 p.2.hi.toIntOpaque

private theorem pair_store_append (mem : DataMem) (base : BitVec 64) (start : Nat)
    (p : Sqr4xDiagonalResult × Sqr4xDiagonalResult) (hb : 8*(start+4) ≤ 2^64) :
    limbsToNat (snapshotLimbs (storeDiagonalPair mem (base+BitVec.ofNat 64 (8*start)) p) base (start+4)) =
      limbsToNat (snapshotLimbs mem base start)+radix start*limbsToNat [p.1.lo,p.1.hi,p.2.lo,p.2.hi] :=
  pair_stores_limbsToNat mem base start p hb

private theorem list_four_slice (xs : List (BitVec 64)) (i : Nat) (hi : i+4 ≤ xs.length) :
    (xs.drop i).take 4 = [xs.getD i 0,xs.getD (i+1) 0,xs.getD (i+2) 0,xs.getD (i+3) 0] := by
  rw [limb_slice_eq _ _ _ hi]
  simp only [show List.range 4 = [0,1,2,3] from rfl,List.map_cons,List.map_nil,Nat.add_zero]

private theorem list_two_slice (xs : List (BitVec 64)) (i : Nat) (hi : i+2 ≤ xs.length) :
    (xs.drop i).take 2 = [xs.getD i 0,xs.getD (i+1) 0] := by
  rw [limb_slice_eq _ _ _ hi]
  simp only [show List.range 2 = [0,1] from rfl,List.map_cons,List.map_nil,Nat.add_zero]

attribute [local irreducible] BnSqr8x.limbsToNat diagonal sqr4xShiftFold sqr4xDiagonalPair
private theorem diagonal_complete_arithmetic (x t : List (BitVec 64)) (base : BitVec 64)
    (mem : DataMem) (n : Nat) (hx : x.length = 4*n+4) (ht : t.length = 8*n+8)
    (h0 : t.getD 0 0 = 0) (hb : 64*n+64 ≤ 2^64) :
    let p := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0
    let boot := storeDiagonalPair mem base p
    let s := sqr4xShiftFold (x.drop 2) (t.drop 4) (base+32) ⟨p.2.shiftCarry,p.2.addCarry,boot⟩ n
    let q := sqr4xDiagonalPair (x.getD (4*n+2) 0) (x.getD (4*n+3) 0)
      (t.getD (8*n+4) 0) (t.getD (8*n+5) 0) (t.getD (8*n+6) 0) (t.getD (8*n+7) 0)
      s.shiftCarry s.addCarry
    limbsToNat (snapshotLimbs (storeDiagonalPair s.memory (base+BitVec.ofNat 64 (8*(8*n+4))) q) base (8*n+8)) +
      radix (8*n+8)*(q.2.shiftCarry.toNat+(q.2.addCarry != 0).toNat) =
      2*limbsToNat t + diagonal x := by
  dsimp only
  let p := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0
  let boot := storeDiagonalPair mem base p
  let initial : Sqr4xShiftState := ⟨p.2.shiftCarry,p.2.addCarry,boot⟩
  let s := sqr4xShiftFold (x.drop 2) (t.drop 4) (base+32) initial n
  let q := sqr4xDiagonalPair (x.getD (4*n+2) 0) (x.getD (4*n+3) 0)
      (t.getD (8*n+4) 0) (t.getD (8*n+5) 0) (t.getD (8*n+6) 0) (t.getD (8*n+7) 0)
      s.shiftCarry s.addCarry
  have hpc : p.2.shiftCarry.toNat ≤ 1 := by
    unfold p sqr4xDiagonalPair
    exact diagonal_result_carry_bound (x.getD 1 0) (t.getD 2 0) (t.getD 3 0) _ _
  have hs := shift_fold_arithmetic (x.drop 2) (t.drop 4) (base+32) initial hpc n (by omega)
    (by rw [List.length_drop,hx]; omega) (by rw [List.length_drop,ht]; omega)
  have hsc : s.shiftCarry.toNat ≤ 1 := shift_fold_carry_bound _ _ _ initial hpc n
  have hp := diagonal_pair_arithmetic (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0 (by decide)
  have hq := diagonal_pair_arithmetic (x.getD (4*n+2) 0) (x.getD (4*n+3) 0)
    (t.getD (8*n+4) 0) (t.getD (8*n+5) 0) (t.getD (8*n+6) 0) (t.getD (8*n+7) 0)
    s.shiftCarry s.addCarry hsc
  have hw := shift_fold_writes (x.drop 2) (t.drop 4) (base+32) initial n (8*n) (by omega)
  have hw' : WorkspaceWrites (base+BitVec.ofNat 64 (8*4)) (8*n) boot s.memory := hw
  have hlow := snapshot_writes_before hw' (by omega)
  have hboot := pair_store_append mem base 0 p (by omega)
  simp only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.zero_add,
    snapshotLimbs,List.range_zero,List.map_nil,radix_eq_pow,Nat.pow_zero,Nat.one_mul] at hboot
  rw [show limbsToNat [] = 0 by unfold limbsToNat; rfl,Nat.zero_add] at hboot
  change limbsToNat (snapshotLimbs boot base 4) = _ at hboot
  have hpair := pair_store_append s.memory base (8*n+4) q (by omega)
  have hv : limbsToNat t = limbsToNat (t.take 4) + radix 4 *
      (limbsToNat ((t.drop 4).take (8*n)) + radix (8*n) * limbsToNat ((t.drop (8*n+4)).take 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 t]
    rw [limbsToNat_append,List.length_take,Nat.min_eq_left (by omega)]
    conv => lhs; rhs; rhs; rw [← List.take_append_drop (8*n) (t.drop 4)]
    rw [limbsToNat_append,List.length_take,List.length_drop,Nat.min_eq_left (by omega),List.drop_drop,
      show 4+8*n = 8*n+4 by omega,show (t.drop (8*n+4)).take 4 = t.drop (8*n+4) from List.take_of_length_le (by rw [List.length_drop,ht]; omega)]
  have hd : diagonal x = diagonal (x.take 2) + radix 4 *
      (diagonal ((x.drop 2).take (4*n)) + radix (8*n) * diagonal ((x.drop (4*n+2)).take 2)) := by
    conv => lhs; rw [← List.take_append_drop 2 x]
    rw [diagonal_append,List.length_take,Nat.min_eq_left (by omega)]
    conv => lhs; rhs; rhs; rw [← List.take_append_drop (4*n) (x.drop 2)]
    rw [diagonal_append,List.length_take,List.length_drop,Nat.min_eq_left (by omega),List.drop_drop,
      show 2+4*n = 4*n+2 by omega,show 2*(4*n)=8*n by omega,
      show (x.drop (4*n+2)).take 2 = x.drop (4*n+2) from List.take_of_length_le (by rw [List.length_drop,hx]; omega)]
  rw [show t.take 4 = (t.drop 0).take 4 from rfl, list_four_slice t 0 (by omega)] at hv
  simp only [List.drop_zero,Nat.zero_add] at hv
  rw [h0, list_four_slice _ _ (by omega)] at hv
  rw [show x.take 2 = (x.drop 0).take 2 from rfl, list_two_slice x 0 (by omega)] at hd
  simp only [List.drop_zero,Nat.zero_add] at hd
  rw [list_two_slice _ _ (by omega)] at hd
  change limbsToNat (snapshotLimbs (storeDiagonalPair s.memory (base+BitVec.ofNat 64 (8*(8*n+4))) q) base (8*n+8)) + radix (8*n+8)*(q.2.shiftCarry.toNat+(q.2.addCarry != 0).toNat) = _
  rw [show 8*n+8=(8*n+4)+4 by omega,hpair,show 8*n+4=4+8*n by omega,snapshot_limbsToNat_append,hlow,hboot]
  change limbsToNat (snapshotLimbs s.memory (base+32) (8*n)) + radix (8*n)*(s.shiftCarry.toNat+(s.addCarry != 0).toNat) =
    2*limbsToNat ((t.drop 4).take (8*n))+diagonal ((x.drop 2).take (4*n))+p.2.shiftCarry.toNat+(p.2.addCarry != 0).toNat at hs
  dsimp only at hp hq
  change limbsToNat [p.1.lo,p.1.hi,p.2.lo,p.2.hi] + radix 4*(p.2.shiftCarry.toNat+(p.2.addCarry != 0).toNat) = _ at hp
  change limbsToNat [q.1.lo,q.1.hi,q.2.lo,q.2.hi] + radix 4*(q.2.shiftCarry.toNat+(q.2.addCarry != 0).toNat) = _ at hq
  have hs' := congrArg (fun z => radix 4*z) hs
  have hq' := congrArg (fun z => radix (4+8*n)*z) hq
  simp (implicitDefEqProofs := false) only [radix_eq_pow,Nat.pow_add,BitVec.ofNat_eq_ofNat,
    show (0 : BitVec 64).toNat=0 from rfl,show ((0 : BitVec 64)!=0).toNat=0 from rfl,Nat.add_zero] at hp hs' hq' ⊢
  simp only [radix_eq_pow,Nat.add_assoc,Nat.reduceAdd,BitVec.ofNat_eq_ofNat] at hv hd
  clear hw hw' hlow hboot hpair hpc hsc hs hq hb h0 hx ht
  clear_value s q p
  simp (implicitDefEqProofs := false) only [show (0#64 : BitVec 64).toNat=0 from rfl,
    show ((0#64 : BitVec 64)!=0#64).toNat=0 from rfl,Nat.add_zero] at hp
  grind (splits := 0) (hom := false) only
end CompleteDiagonalArithmetic


section ReductionPassArithmetic
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private theorem cancellation_writes (m : Sqr8xWords) (n0 sp : BitVec 64)
    (initial : Sqr8xReduceState) (k : Nat) (hk : k ≤ 8) :
    WorkspaceWrites (sp+56) 8 initial.memory (sqr8xReduceFold m n0 sp initial k).memory := by
  induction k with
  | zero => exact WorkspaceWrites.refl _
  | succ k ih =>
    dsimp only [sqr8xReduceFold]
    apply (ih (by omega)).store_at (7-k) (by omega) _ _
    have hn : 112-8*k = 56+8*(7-k) := by omega
    rw [hn,BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
    rfl

private theorem cancellation_snapshot (m : Sqr8xWords) (n0 sp : BitVec 64)
    (mem : DataMem) (input : Sqr8xWords) (carry : BitVec 64) (blocks off len : Nat)
    (ho : 8 ≤ off) (hl : off+len ≤ 16*blocks) (hb : 128*blocks+8 ≤ 2^64) :
    let initial : Sqr8xReduceState := ⟨input,input.w0*n0,
      mem.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 carry.toIntOpaque⟩
    snapshotLimbs (sqr8xReduceFold m n0 sp initial 8).memory (sp+56+BitVec.ofNat 64 (8*off)) len =
      snapshotLimbs mem (sp+56+BitVec.ofNat 64 (8*off)) len := by
  dsimp only
  have hw := cancellation_writes m n0 sp
    ⟨input,input.w0*n0,mem.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 carry.toIntOpaque⟩ 8 (by decide)
  have hw' : WorkspaceWrites ((sp+56)+BitVec.ofNat 64 (8*0)) 8
      (mem.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 carry.toIntOpaque)
      (sqr8xReduceFold m n0 sp ⟨input,input.w0*n0,mem.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 carry.toIntOpaque⟩ 8).memory := by
    simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw
  rw [workspace_snapshot_outside hw' (off := off) (n := len) (by omega) (by decide) (by omega)]
  rw [show 128*blocks = 8*(16*blocks) by omega]
  exact snapshot_store_outside mem (sp+56) off len (16*blocks) carry.toIntOpaque (by omega) (by omega) (by omega)

private theorem bool_word_sum (a b : Bool) :
    (BitVec.ofNat 64 a.toNat + BitVec.ofNat 64 b.toNat).toNat = a.toNat+b.toNat := by
  cases a <;> cases b <;> rfl

private theorem words_single_value (w : BitVec 64) : wordsValue ⟨w,0,0,0,0,0,0,0⟩ = w.toNat := by
  simp (implicitDefEqProofs := false) only [wordsValue,limbsToNat,show (0 : BitVec 64).toNat=0 from rfl,
    Nat.mul_zero,Nat.add_zero]

private def reductionPassCoefficient (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) : Nat :=
  let input := readWords initial.memory (sp+56+BitVec.ofNat 64 (64*pass))
  reduceFoldCoefficient (limbBlock modulus 0) n0 sp
    ⟨input,input.w0*n0,initial.memory.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 initial.carry.toIntOpaque⟩ 8

private theorem reduction_pass_coefficient_bound (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) :
    reductionPassCoefficient modulus n0 sp blocks pass initial < radix 8 :=
  reduce_fold_coefficient_bound _ _ _ _ 8

attribute [local irreducible] BnSqr8x.limbsToNat sqr8xReduceFold sqr8xTailBlocksFold sqr8xAddResult
private theorem reduction_pass_local_arithmetic (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState)
    (hpos : 0 < blocks) (hpass : pass < blocks) (hlen : modulus.length = 8*blocks)
    (hb : 128*blocks+8 ≤ 2^64) (hi : modulus.getD 0 0*n0+1=0)
    (hcarry : blocks=1 → initial.carry=0) :
    let next := sqr8xReductionPass modulus n0 sp blocks pass initial
    radix 8 * (limbsToNat (snapshotLimbs next.memory (sp+56+BitVec.ofNat 64 (64*(pass+1))) (8*blocks)) +
      radix (8*blocks)*next.carry.toNat) =
    limbsToNat (snapshotLimbs initial.memory (sp+56+BitVec.ofNat 64 (64*pass)) (8*blocks+8)) +
      radix (8*blocks)*initial.carry.toNat + limbsToNat modulus*reductionPassCoefficient modulus n0 sp blocks pass initial := by
  let base := sp+56
  let input := readWords initial.memory (base+BitVec.ofNat 64 (64*pass))
  let saved := initial.memory.storeInt (base+BitVec.ofNat 64 (128*blocks)) 8 initial.carry.toIntOpaque
  let cinit : Sqr8xReduceState := ⟨input,input.w0*n0,saved⟩
  let cancelled := sqr8xReduceFold (limbBlock modulus 0) n0 sp cinit 8
  let coefficients := savedCoefficients cancelled.memory sp
  let tail := sqr8xTailBlocksFold modulus coefficients sp pass ⟨cancelled.words,0,cancelled.memory⟩ (blocks-1)
  let carrySum := if blocks=1 then (tail.words,false) else
    sqr8xAddResult tail.words ⟨initial.carry,0,0,0,0,0,0,0⟩ false
  let out := base+BitVec.ofNat 64 (64*(pass+blocks))
  let sum := sqr8xAddResult carrySum.1 (readWords tail.memory out) (tail.carry != 0)
  let Q := reductionPassCoefficient modulus n0 sp blocks pass initial
  have hcoeff : limbsToNat (coefficients.take 8) = Q := reduce_saved_limbsToNat _ _ _ cinit 8 (by decide)
  have hc := reduce_fold_arithmetic (limbBlock modulus 0) n0 sp cinit rfl hi 8
  change radix 8*wordsValue cancelled.words = wordsValue input+wordsValue (limbBlock modulus 0)*Q at hc
  have hq : 8 ≤ coefficients.length := by simp only [coefficients,savedCoefficients,List.length_map,List.length_range]; decide
  have ht := tail_blocks_arithmetic modulus coefficients sp pass ⟨cancelled.words,0,cancelled.memory⟩ (blocks-1) hq (by omega) (by omega)
  dsimp only at ht
  change limbsToNat (snapshotLimbs tail.memory (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1))) +
    radix (8*(blocks-1))*(wordsValue tail.words+(tail.carry != 0).toNat) = _ at ht
  rw [hcoeff] at ht
  have hcs : wordsValue carrySum.1+radix 8*carrySum.2.toNat = wordsValue tail.words+initial.carry.toNat := by
    dsimp only [carrySum]
    split
    next he => rw [hcarry he]; simp only [show (0 : BitVec 64).toNat=0 from rfl,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    next he =>
      have ha := add_result_arithmetic tail.words ⟨initial.carry,0,0,0,0,0,0,0⟩ false
      simpa only [words_single_value,Bool.toNat_false,Nat.add_zero,show radix 8=2^512 from by decide] using ha
  have hs := add_result_arithmetic carrySum.1 (readWords tail.memory out) (tail.carry != 0)
  have hout : out = (base+BitVec.ofNat 64 (64*(pass+1)))+BitVec.ofNat 64 (8*(8*(blocks-1))) := by
    dsimp only [out]
    rw [show 64*(pass+blocks)=64*(pass+1)+8*(8*(blocks-1)) by omega,BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
  have htailhigh : snapshotLimbs tail.memory out 8 = snapshotLimbs cancelled.memory out 8 := by
    have hw := tail_blocks_writes modulus coefficients sp pass ⟨cancelled.words,0,cancelled.memory⟩ (blocks-1)
    change WorkspaceWrites (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1)) cancelled.memory tail.memory at hw
    have hw' : WorkspaceWrites ((base+BitVec.ofNat 64 (64*(pass+1)))+BitVec.ofNat 64 (8*0)) (8*(blocks-1)) cancelled.memory tail.memory := by
      simpa only [Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw
    rw [hout]
    exact workspace_snapshot_outside hw' (by omega) (by omega) (by omega)
  have hmid : snapshotLimbs cancelled.memory (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1)) =
      snapshotLimbs initial.memory (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1)) := by
    simpa only [← Nat.mul_assoc,show 8*8=64 from rfl] using cancellation_snapshot _ n0 sp initial.memory input initial.carry blocks (8*(pass+1)) (8*(blocks-1)) (by omega) (by omega) hb
  have hhigh : snapshotLimbs tail.memory out 8 = snapshotLimbs initial.memory out 8 := by
    rw [htailhigh]
    simpa only [← Nat.mul_assoc,show 8*8=64 from rfl] using cancellation_snapshot _ n0 sp initial.memory input initial.carry blocks (8*(pass+blocks)) 8 (by omega) (by omega) hb
  rw [hmid] at ht
  have hm : limbsToNat modulus = wordsValue (limbBlock modulus 0) + radix 8*limbsToNat ((modulus.drop 8).take (8*(blocks-1))) := by
    conv => lhs; rw [← List.take_append_drop 8 modulus]
    rw [limbsToNat_append,List.length_take,Nat.min_eq_left (by omega)]
    rw [show modulus.take 8 = (modulus.drop 0).take 8 by rfl,limb_block_limbsToNat _ 0 (by omega)]
    rw [List.take_of_length_le (by rw [List.length_drop,hlen]; omega)]
  have hmem := store_words_append_limbsToNat tail.memory (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1)) sum.1 (by omega)
  rw [← hout] at hmem
  change limbsToNat (snapshotLimbs (storeSqr8xWords tail.memory out sum.1) _ (8*(blocks-1)+8)) = _ at hmem
  have hin : limbsToNat (snapshotLimbs initial.memory (base+BitVec.ofNat 64 (64*pass)) (8*blocks+8)) =
      wordsValue input+radix 8*(limbsToNat (snapshotLimbs initial.memory (base+BitVec.ofNat 64 (64*(pass+1))) (8*(blocks-1))))+
        radix (8*blocks)*limbsToNat (snapshotLimbs initial.memory out 8) := by
    rw [show 8*blocks+8=8+(8*(blocks-1)+8) by omega,snapshot_limbsToNat_append,snapshot_limbsToNat_append,snapshot_read_words]
    have ha : base+BitVec.ofNat 64 (64*pass)+BitVec.ofNat 64 (8*8) = base+BitVec.ofNat 64 (64*(pass+1)) := by
      simp only [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rw [ha,← hout]
    change wordsValue input + _ = _
    rw [show 8*blocks=8+8*(blocks-1) by omega]
    simp only [radix_eq_pow,Nat.pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
  change radix 8*(limbsToNat (snapshotLimbs (storeSqr8xWords tail.memory out sum.1) _ (8*blocks)) +
    radix (8*blocks)*(BitVec.ofNat 64 carrySum.2.toNat+BitVec.ofNat 64 sum.2.toNat).toNat) = _
  rw [bool_word_sum,show 8*blocks=8*(blocks-1)+8 by omega,hmem]
  rw [show 8*blocks=8*(blocks-1)+8 by omega] at hin
  rw [hin,hm]
  rw [← snapshot_read_words tail.memory out,hhigh] at hs
  change wordsValue sum.1+2^512*sum.2.toNat = _ at hs
  have ht' := congrArg (fun z => radix 8*z) ht
  have hs' := congrArg (fun z => radix (8*blocks)*z) hs
  have hcs' := congrArg (fun z => radix (8*blocks)*z) hcs
  simp (implicitDefEqProofs := false) only [show ((0 : BitVec 64)!=0).toNat=0 from rfl,Nat.add_zero] at ht'
  simp only [show 8*blocks=8*(blocks-1)+8 by omega,radix_eq_pow,Nat.pow_add] at hc ht' hs' hcs' ⊢
  grind (splits := 0) only
end ReductionPassArithmetic


section ReductionFoldArithmetic
set_option exponentiation.threshold 1024
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

private theorem WorkspaceWrites.weaken {base : BitVec 64} {len total : Nat} {a b : DataMem}
    (h : WorkspaceWrites base len a b) (hb : len ≤ total) : WorkspaceWrites base total a b := by
  induction h with
  | refl => exact WorkspaceWrites.refl _
  | store _ i hi v ih => exact ih.store i (by omega) v

private theorem reduction_output_writes (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) (hp : 0 < blocks) :
    let input := readWords initial.memory (sp+56+BitVec.ofNat 64 (64*pass))
    let saved := initial.memory.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 initial.carry.toIntOpaque
    let cancelled := sqr8xReduceFold (limbBlock modulus 0) n0 sp ⟨input,input.w0*n0,saved⟩ 8
    WorkspaceWrites (sp+56+BitVec.ofNat 64 (64*(pass+1))) (8*blocks) cancelled.memory
      (sqr8xReductionPass modulus n0 sp blocks pass initial).memory := by
  dsimp only
  let input := readWords initial.memory (sp+56+BitVec.ofNat 64 (64*pass))
  let saved := initial.memory.storeInt (sp+56+BitVec.ofNat 64 (128*blocks)) 8 initial.carry.toIntOpaque
  let cancelled := sqr8xReduceFold (limbBlock modulus 0) n0 sp ⟨input,input.w0*n0,saved⟩ 8
  have ht := tail_blocks_writes modulus (savedCoefficients cancelled.memory sp) sp pass ⟨cancelled.words,0,cancelled.memory⟩ (blocks-1)
  apply (ht.weaken (show 8*(blocks-1) ≤ 8*blocks by omega)).trans
  dsimp only [sqr8xReductionPass]
  have ha : sp+56+BitVec.ofNat 64 (64*(pass+blocks)) =
      sp+56+BitVec.ofNat 64 (64*(pass+1))+BitVec.ofNat 64 (8*(8*(blocks-1))) := by
    rw [show 64*(pass+blocks)=64*(pass+1)+8*(8*(blocks-1)) by omega,BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
  rw [ha]
  exact store_words_writes _ _ (8*(blocks-1)) (by omega) _ _

private theorem reduction_pass_high_snapshot (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState) (hp : 0 < blocks)
    (off len : Nat) (ho : 8*(pass+blocks+1) ≤ off) (hl : off+len ≤ 16*blocks)
    (hb : 128*blocks+8 ≤ 2^64) :
    snapshotLimbs (sqr8xReductionPass modulus n0 sp blocks pass initial).memory (sp+56+BitVec.ofNat 64 (8*off)) len =
      snapshotLimbs initial.memory (sp+56+BitVec.ofNat 64 (8*off)) len := by
  have hw := reduction_output_writes modulus n0 sp blocks pass initial hp
  dsimp only at hw
  have ha : 64*(pass+1)=8*(8*(pass+1)) := by omega
  rw [ha] at hw
  rw [workspace_snapshot_outside hw (off := off) (n := len) (by omega) (by omega) (by omega)]
  exact cancellation_snapshot _ n0 sp initial.memory _ initial.carry blocks off len (by omega) hl hb

private def reductionActiveValue (sp : BitVec 64) (blocks pass : Nat) (s : Sqr8xReductionState) : Nat :=
  limbsToNat (snapshotLimbs s.memory (sp+56+BitVec.ofNat 64 (64*pass)) (8*(2*blocks-pass))) +
    radix (8*blocks)*s.carry.toNat

attribute [local irreducible] BnSqr8x.limbsToNat sqr8xReductionPass
private theorem reduction_pass_arithmetic (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks pass : Nat) (initial : Sqr8xReductionState)
    (hpos : 0 < blocks) (hpass : pass < blocks) (hlen : modulus.length=8*blocks)
    (hb : 128*blocks+8 ≤ 2^64) (hi : modulus.getD 0 0*n0+1=0)
    (hcarry : blocks=1 → initial.carry=0) :
    radix 8*reductionActiveValue sp blocks (pass+1) (sqr8xReductionPass modulus n0 sp blocks pass initial) =
      reductionActiveValue sp blocks pass initial+limbsToNat modulus*reductionPassCoefficient modulus n0 sp blocks pass initial := by
  have hl := reduction_pass_local_arithmetic modulus n0 sp blocks pass initial hpos hpass hlen hb hi hcarry
  let next := sqr8xReductionPass modulus n0 sp blocks pass initial
  let extra := 8*(blocks-pass-1)
  have hh := reduction_pass_high_snapshot modulus n0 sp blocks pass initial hpos (8*(pass+blocks+1)) extra (by omega) (by dsimp [extra]; omega) hb
  dsimp only [reductionActiveValue]
  rw [show 8*(2*blocks-pass)=8*blocks+8+extra by dsimp [extra]; omega,
    show 8*(2*blocks-(pass+1))=8*blocks+extra by dsimp [extra]; omega]
  rw [snapshot_limbsToNat_append,snapshot_limbsToNat_append]
  have ha : sp+56+BitVec.ofNat 64 (64*(pass+1))+BitVec.ofNat 64 (8*(8*blocks)) =
      sp+56+BitVec.ofNat 64 (8*(8*(pass+blocks+1))) := by
    rw [BitVec.add_assoc (sp+56),← BitVec.ofNat_add]
    congr 2; omega
  have hb' : sp+56+BitVec.ofNat 64 (64*pass)+BitVec.ofNat 64 (8*(8*blocks+8)) =
      sp+56+BitVec.ofNat 64 (8*(8*(pass+blocks+1))) := by
    rw [BitVec.add_assoc (sp+56),← BitVec.ofNat_add]
    congr 2; omega
  rw [ha,hb',hh]
  dsimp only at hl
  simp only [radix_eq_pow,Nat.pow_add] at hl ⊢
  grind (splits := 0) only

private def reductionCoefficient (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks : Nat) (initial : Sqr8xReductionState) : Nat → Nat
  | 0 => 0
  | k+1 => reductionCoefficient modulus n0 sp blocks initial k + radix (8*k)*
    reductionPassCoefficient modulus n0 sp blocks k (sqr8xReductionFold modulus n0 sp blocks initial k)

private theorem reduction_coefficient_bound (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks : Nat) (initial : Sqr8xReductionState) (k : Nat) :
    reductionCoefficient modulus n0 sp blocks initial k < radix (8*k) := by
  induction k with
  | zero => simp only [reductionCoefficient,Nat.mul_zero,radix_eq_pow,Nat.pow_zero]; decide
  | succ k ih =>
    have hb := reduction_pass_coefficient_bound modulus n0 sp blocks k (sqr8xReductionFold modulus n0 sp blocks initial k)
    have hp : 0 < radix (8*k) := Nat.pow_pos (by decide)
    have hmul := Nat.mul_le_mul_left (radix (8*k)) (Nat.le_sub_one_of_lt hb)
    rw [reductionCoefficient]
    rw [show 8*(k+1)=8*k+8 by omega]
    simp only [radix_eq_pow,Nat.pow_add] at ih hmul ⊢
    omega

private theorem reduction_fold_arithmetic (modulus : List (BitVec 64)) (n0 sp : BitVec 64)
    (blocks : Nat) (initial : Sqr8xReductionState) (k : Nat)
    (hpos : 0 < blocks) (hk : k ≤ blocks) (hlen : modulus.length=8*blocks)
    (hb : 128*blocks+8 ≤ 2^64) (hi : modulus.getD 0 0*n0+1=0) (hcarry : initial.carry=0) :
    radix (8*k)*reductionActiveValue sp blocks k (sqr8xReductionFold modulus n0 sp blocks initial k) =
      reductionActiveValue sp blocks 0 initial + limbsToNat modulus*reductionCoefficient modulus n0 sp blocks initial k := by
  induction k with
  | zero => simp only [sqr8xReductionFold,reductionCoefficient,Nat.mul_zero,radix_eq_pow,Nat.pow_zero,Nat.one_mul,Nat.add_zero]
  | succ k ih =>
    have ih := ih (by omega)
    have hc : blocks=1 → (sqr8xReductionFold modulus n0 sp blocks initial k).carry=0 := by
      intro he
      have hk0 : k=0 := by omega
      rw [hk0,sqr8xReductionFold]
      exact hcarry
    have hp := reduction_pass_arithmetic modulus n0 sp blocks k
      (sqr8xReductionFold modulus n0 sp blocks initial k) hpos (by omega) hlen hb hi hc
    have he := congrArg (fun z => radix (8*k)*z) hp
    rw [sqr8xReductionFold,reductionCoefficient,show 8*(k+1)=8*k+8 by omega]
    simp only [radix_eq_pow,Nat.pow_add] at he ih ⊢
    grind (splits := 0) only
end ReductionFoldArithmetic

section SquareRefinement
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private def squareCrossLimbs (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) : List (BitVec 64) :=
  ((snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp+56) (16*blocks+1)).set 0 0).take (16*blocks)

private theorem square_cross_length (d : MachineData) (x : List (BitVec 64)) (blocks : Nat) :
    (squareCrossLimbs d x blocks).length=16*blocks := by
  simp only [squareCrossLimbs,List.length_take,List.length_set,snapshot_length]; omega

private theorem square_cross_zero {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    (squareCrossLimbs d x blocks).getD 0 0=0 := by
  simp only [squareCrossLimbs,List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_set]
  simp [show 0<16*blocks by have := h.positive; omega,snapshot_length]

private theorem square_cross_get {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (i : Nat) (hi : 0<i) (hib : i<16*blocks) :
    (squareCrossLimbs d x blocks).getD i 0 =
      (snapshotLimbs (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp+56) (16*blocks+1)).getD i 0 := by
  simp only [squareCrossLimbs,List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_set]
  simp [hib,show 0 ≠ i by omega]

private theorem square_cross_limbsToNat {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    limbsToNat (squareCrossLimbs d x blocks)=cross x := by
  have hp := h.positive
  have hh : 16*blocks+1=(16*blocks)+1 := rfl
  rw [squareCrossLimbs,List.take_set,snapshot_take _ _ _ _ (by omega)]
  rw [show 16*blocks=(16*blocks-1)+1 by omega,snapshot_cons]
  simp only [List.set_cons_zero,limbsToNat_cons,show (0 : BitVec 64).toNat=0 from rfl,Nat.zero_add]
  have ha : d.regs.get64 .rsp+56+8=d.regs.get64 .rsp+64 := by grind
  rw [ha]
  exact final_cross_arithmetic h

private theorem pair_stores_writes (mem : DataMem) (base : BitVec 64)
    (p : Sqr4xDiagonalResult × Sqr4xDiagonalResult) :
    WorkspaceWrites base 4 mem (storeDiagonalPair mem base p) := by
  unfold storeDiagonalPair
  apply WorkspaceWrites.store_at (i := 3) (hi := by decide) (ha := by grind)
  apply WorkspaceWrites.store_at (i := 2) (hi := by decide) (ha := by grind)
  apply WorkspaceWrites.store_at (i := 1) (hi := by decide) (ha := by grind)
  exact WorkspaceWrites.store_at (WorkspaceWrites.refl _) 0 (by decide) (by grind) _

private theorem shift_seed_pair {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    let t := squareCrossLimbs d x blocks
    let p := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0
    (shiftSeed d x blocks).dmem = storeDiagonalPair (diagonalSeed d x blocks).dmem (d.regs.get64 .rsp+56) p ∧
    (shiftSeed d x blocks).regs.get64 .r14=p.2.shiftCarry ∧
    (shiftSeed d x blocks).regs.get64 .r15=p.2.addCarry ∧
    (shiftSeed d x blocks).regs.get64 .rdi=d.regs.get64 .rsp+120 := by
  dsimp only
  rw [square_cross_get h 1 (by decide) (by have := h.positive; omega),
    square_cross_get h 2 (by decide) (by have := h.positive; omega),
    square_cross_get h 3 (by decide) (by have := h.positive; omega)]
  have hr := (square_seed_registers d x blocks).2.2.2.2.1.1
  simp (implicitDefEqProofs := false) only [shiftSeed,storeDiagonalPair,MachineData.dmem_mk,MachineData.regs_mk,Reg64s.get64_set64,
    ite_true,ite_false,reduceCtorEq,hr,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd,eq_self, true_and]

private theorem shift_accumulator_cross {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    shiftAccumulator d x blocks=(squareCrossLimbs d x blocks).drop 4 := by
  have hp := h.positive
  let base := d.regs.get64 .rsp+56
  have hs := (shift_seed_pair h).1
  let p := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0
    ((squareCrossLimbs d x blocks).getD 1 0) ((squareCrossLimbs d x blocks).getD 2 0)
    ((squareCrossLimbs d x blocks).getD 3 0) 0 0
  have hw := pair_stores_writes (diagonalSeed d x blocks).dmem base p
  have hw' : WorkspaceWrites (base+BitVec.ofNat 64 (8*0)) 4 (diagonalSeed d x blocks).dmem (shiftSeed d x blocks).dmem := by
    rw [hs]
    simpa only [p,base,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw
  have he := workspace_snapshot_outside hw' (off := 4) (n := 16*blocks-4) (by omega) (by decide)
    (by have := h.sizeBound; omega)
  dsimp only [shiftAccumulator,squareCrossLimbs]
  rw [snapshot_slice _ _ _ _ _ (by omega),List.drop_take,List.drop_set_of_lt (by decide)]
  rw [snapshot_slice _ _ _ _ _ (by omega)]
  exact he

attribute [local irreducible] BnSqr8x.limbsToNat sqr4xShiftFold sqr4xDiagonalPair
private theorem reduction_seed_square {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    limbsToNat (snapshotLimbs (reductionSeed d x blocks).dmem (d.regs.get64 .rsp+56) (16*blocks)) =
      limbsToNat x * limbsToNat x := by
  let base := d.regs.get64 .rsp+56
  let n := 2*blocks-1
  let t := squareCrossLimbs d x blocks
  let p := sqr4xDiagonalPair (x.getD 0 0) (x.getD 1 0) 0 (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) 0 0
  let boot := storeDiagonalPair (diagonalSeed d x blocks).dmem base p
  let st := sqr4xShiftFold (x.drop 2) (t.drop 4) (base+32) ⟨p.2.shiftCarry,p.2.addCarry,boot⟩ n
  let q := sqr4xDiagonalPair (x.getD (4*n+2) 0) (x.getD (4*n+3) 0)
    (t.getD (8*n+4) 0) (t.getD (8*n+5) 0) (t.getD (8*n+6) 0) (t.getD (8*n+7) 0)
    st.shiftCarry st.addCarry
  have hp := h.positive
  have hn : 4*n+4=8*blocks := by dsimp [n]; omega
  have hn' : 8*n+8=16*blocks := by dsimp [n]; omega
  have ht : t.length=8*n+8 := by rw [square_cross_length,hn']
  have hs := shift_seed_pair h
  change (shiftSeed d x blocks).dmem=boot ∧ (shiftSeed d x blocks).regs.get64 .r14=p.2.shiftCarry ∧
    (shiftSeed d x blocks).regs.get64 .r15=p.2.addCarry ∧ (shiftSeed d x blocks).regs.get64 .rdi=d.regs.get64 .rsp+120 at hs
  have hacc : shiftAccumulator d x blocks=t.drop 4 := shift_accumulator_cross h
  have hmid : sqr4xShiftPrefix (shiftSeed d x blocks) (x.drop 2) (shiftAccumulator d x blocks) n = st := by
    rw [sqr4xShiftPrefix,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hacc]
    have ha : d.regs.get64 .rsp+120+(-32#64)=base+32 := by dsimp [base]; grind
    rw [ha]
  have hdmem : (shiftDoneSeed d x blocks).dmem=st.memory := by
    change (sqr4xShiftPrefix _ _ _ n).memory=st.memory
    rw [hmid]
  have hdregs : (shiftDoneSeed d x blocks).regs.get64 .rax=x.getD (4*n+2) 0 ∧
      (shiftDoneSeed d x blocks).regs.get64 .r10=t.getD (8*n+4) 0 ∧
      (shiftDoneSeed d x blocks).regs.get64 .r11=t.getD (8*n+5) 0 ∧
      (shiftDoneSeed d x blocks).regs.get64 .r14=st.shiftCarry ∧
      (shiftDoneSeed d x blocks).regs.get64 .r15=st.addCarry := by
    simp only [shiftDoneSeed,MachineData.regs_mk,Reg64s.get64_set64,ite_true,ite_false,reduceCtorEq]
    change (x.drop 2).getD (4*n) 0=_ ∧ (shiftAccumulator d x blocks).getD (8*n) 0=_ ∧
      (shiftAccumulator d x blocks).getD (8*n+1) 0=_ ∧
      (sqr4xShiftPrefix _ _ _ n).shiftCarry=_ ∧ (sqr4xShiftPrefix _ _ _ n).addCarry=_
    rw [hmid,hacc]
    simp only [limb_drop_getD]
    have ha : 2+4*n=4*n+2 := by omega
    have hb : 4+8*n=8*n+4 := by omega
    have hc : 4+(8*n+1)=8*n+5 := by omega
    simp only [ha,hb,hc,and_self]
  have hm : (reductionSeed d x blocks).dmem = storeDiagonalPair st.memory (base+BitVec.ofNat 64 (8*(8*n+4))) q := by
    dsimp only [reductionSeed]
    rw [hdmem,hdregs.1,hdregs.2.1,hdregs.2.2.1,hdregs.2.2.2.1,hdregs.2.2.2.2,
      shift_done_pointer h,hacc]
    change _ = storeDiagonalPair st.memory _ q
    rw [show 8*blocks-1=4*n+3 by dsimp [n]; omega]
    change (((st.memory.storeInt (d.regs.get64 .rsp+56+BitVec.ofNat 64 (128*blocks)+(-32#64)) 8
      (sqr4xDiagonalPair _ _ _ _ ((t.drop 4).getD (8*n+2) 0) ((t.drop 4).getD (8*n+3) 0) _ _).1.lo.toIntOpaque).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _ = _
    simp only [limb_drop_getD,show 4+(8*n+2)=8*n+6 by omega,show 4+(8*n+3)=8*n+7 by omega,
      show 4+(8*(2*blocks-1)+2)=8*n+6 by dsimp [n]; omega,
      show 4+(8*(2*blocks-1)+3)=8*n+7 by dsimp [n]; omega]
    have ha (j : BitVec 64) : d.regs.get64 .rsp+56+BitVec.ofNat 64 (128*blocks)+(-32#64+j) =
        base+BitVec.ofNat 64 (8*(8*n+4))+j := by
      have he : 8*(8*n+4)+32=128*blocks := by dsimp [n]; omega
      rw [← he,BitVec.ofNat_add]
      dsimp [base]
      grind
    change (((st.memory.storeInt _ _ q.1.lo.toIntOpaque).storeInt _ _ q.1.hi.toIntOpaque).storeInt _ _ q.2.lo.toIntOpaque).storeInt _ _ q.2.hi.toIntOpaque = _
    have ha0 := ha 0
    have ha1 := ha 8
    have ha2 := ha 16
    have ha3 := ha 24
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.reduceAdd] at ha0 ha1 ha2 ha3
    simp only [BitVec.ofNat_eq_ofNat]
    simp only [show (-32#64)+8#64=(-24#64) from by decide,
      show (-32#64)+16#64=(-16#64) from by decide,
      show (-32#64)+24#64=(-8#64) from by decide] at ha1 ha2 ha3
    rw [ha0,ha1,ha2,ha3]
    rfl
  have he := diagonal_complete_arithmetic x t base (diagonalSeed d x blocks).dmem n
    (by rw [hn]; exact h.inputLength) ht (square_cross_zero h) (by dsimp [n]; have := h.sizeBound; omega)
  change limbsToNat (snapshotLimbs (storeDiagonalPair st.memory (base+BitVec.ofNat 64 (8*(8*n+4))) q) base (8*n+8)) +
    radix (8*n+8)*(q.2.shiftCarry.toNat+(q.2.addCarry != 0).toNat)=2*limbsToNat t+diagonal x at he
  rw [← hm,hn',square_cross_limbsToNat h,← square_decomposition] at he
  have hv := limbsToNat_lt_radix x
  have hmul : limbsToNat x*limbsToNat x < radix (16*blocks) := by
    have hr : 0<radix x.length := Nat.pow_pos (by decide)
    have hh := Nat.mul_lt_mul_of_pos_right hv hr
    have hl := Nat.mul_le_mul_left (limbsToNat x) (Nat.le_of_lt hv)
    rw [h.inputLength] at hh hl
    have he : radix (16*blocks)=radix (8*blocks)*radix (8*blocks) := by
      rw [show 16*blocks=8*blocks+8*blocks by omega]
      simp only [radix_eq_pow, Nat.pow_add]
    rw [he]; omega
  have hv' := limbsToNat_lt_radix (snapshotLimbs (reductionSeed d x blocks).dmem base (16*blocks))
  rw [snapshot_length] at hv'
  have hmod := congrArg (fun z => z % radix (16*blocks)) he
  rw [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hv',Nat.mod_eq_of_lt hmul] at hmod
  exact hmod
end SquareRefinement


section ReductionRefinement
set_option exponentiation.threshold 1024

private theorem initial_snapshot (d : MachineData) (blocks : Nat)
    (hb : 128*blocks+56 ≤ 2^64) :
    snapshotLimbs (reductionInitialMemory d blocks) (d.regs.get64 .rsp+56) (16*blocks) =
      snapshotLimbs d.dmem (d.regs.get64 .rsp+56) (16*blocks) := by
  dsimp only [reductionInitialMemory]
  have h2 := snapshot_store_outside (d.dmem.storeInt (d.regs.get64 .rsp+8) 8
    (d.regs.get64 .rbp+BitVec.ofNat 64 (64*blocks)).toIntOpaque)
    (d.regs.get64 .rsp) 7 (16*blocks) 2
    (d.regs.get64 .rsp+56+BitVec.ofNat 64 (128*blocks)).toIntOpaque (by omega) (by omega) (by decide)
  have h1 := snapshot_store_outside d.dmem (d.regs.get64 .rsp) 7 (16*blocks) 1
    (d.regs.get64 .rbp+BitVec.ofNat 64 (64*blocks)).toIntOpaque (by omega) (by omega) (by decide)
  exact h2.trans h1

private theorem reduction_prefix_arithmetic (d : MachineData) (modulus : List (BitVec 64))
    (n0 : BitVec 64) (blocks : Nat) (hp : 0<blocks) (hl : modulus.length=8*blocks)
    (hb : 128*blocks+56 ≤ 2^64) (hi : modulus.getD 0 0*n0+1=0) :
    ∃Q < radix (8*blocks),
      radix (8*blocks)*(limbsToNat (snapshotLimbs (sqr8xReductionPrefix d modulus n0 blocks blocks).memory
        (d.regs.get64 .rsp+56+BitVec.ofNat 64 (64*blocks)) (8*blocks)) +
        radix (8*blocks)*(sqr8xReductionPrefix d modulus n0 blocks blocks).carry.toNat) =
      limbsToNat (snapshotLimbs d.dmem (d.regs.get64 .rsp+56) (16*blocks)) + limbsToNat modulus*Q := by
  let initial : Sqr8xReductionState := ⟨0,reductionInitialMemory d blocks⟩
  refine ⟨reductionCoefficient modulus n0 (d.regs.get64 .rsp) blocks initial blocks,
    reduction_coefficient_bound _ _ _ _ _ _, ?_⟩
  have he := reduction_fold_arithmetic modulus n0 (d.regs.get64 .rsp) blocks initial blocks hp (by omega) hl (by omega) hi rfl
  dsimp only [reductionActiveValue] at he
  simp (implicitDefEqProofs := false) only [Nat.sub_zero,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero,
    show 2*blocks-blocks=blocks by omega,show 8*(2*blocks)=16*blocks by omega,
    show initial.carry.toNat=0 from rfl,Nat.mul_zero,Nat.add_zero] at he
  rw [show initial.memory=reductionInitialMemory d blocks from rfl] at he
  have hm := initial_snapshot d blocks hb
  simp only [BitVec.ofNat_eq_ofNat] at hm
  rw [hm] at he
  simp only [BitVec.ofNat_eq_ofNat]
  exact he
end ReductionRefinement


section MathematicalCorrectness
set_option exponentiation.threshold 1024
set_option maxRecDepth 2048

/-- The arithmetic reference computes an unreduced Montgomery square. For
`N = 8 * blocks`, `A = limbsToNat x`, `M = limbsToNat modulus`, and `R = 2^(64*N)`,
its complete output `Y` satisfies `R * Y = A * A + M * Q` for some `Q < R`.
No arithmetic-correctness assumption about the reference is required. -/
theorem bnSqr8xResult_montgomery_square {d : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks) :
    BnSqr8x.MontgomerySquare x modulus (bnSqr8xResultValue d x modulus n0 blocks) := by
  have hr := (square_seed_registers d x blocks).2.2.2.2.2.2.2.1
  obtain ⟨q, hq, he⟩ := reduction_prefix_arithmetic (reductionSeed d x blocks) modulus n0 blocks
    h.positive h.modulusLength (by have := h.sizeBound; omega) h.inverse
  rw [hr, reduction_seed_square h] at he
  refine ⟨q, by rw [h.inputLength]; exact hq, ?_⟩
  rw [h.inputLength]
  dsimp only [bnSqr8xResultValue, bnSqr8xResultLimbs, bnSqr8xResult, BnSqr8x.outputAddress]
  simpa only [show 8 * (8 * blocks) = 64 * blocks by omega] using he

private theorem bnSqr8xPost.mathematical {d s : MachineData} {x modulus : List (BitVec 64)}
    {n0 : BitVec 64} {blocks : Nat} (h : BnSqr8xBlockContext d x modulus n0 blocks)
    (hp : bnSqr8xPost d x modulus n0 blocks s) :
    BnSqr8x.MathematicalPost (d.regs.get64 .rsp) x modulus s :=
  ⟨bnSqr8xResultValue d x modulus n0 blocks, bnSqr8xPost.outputValue h hp,
    bnSqr8xResult_montgomery_square h⟩

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout bn_sqr8x_internal_prog)]
local instance : CodeEnv := ⟨layout bn_sqr8x_internal_prog⟩

/-- Mathematical correctness of `__bn_sqr8x_internal`, including termination
and return to `ra`. Let `N = x.length = modulus.length`, `A = limbsToNat x`,
`M = limbsToNat modulus`, and `R = 2^(64*N)`. On return, the `N` limbs starting at
entry `rsp + 56 + 8*N`, together with `rax` as an extra high limb, represent
`Y` with `R * Y = A * A + M * Q` and `Q < R`.

The block count is derived from `x.length / 8`; the context requires `x.length`
to be a positive multiple of eight.

The `False` before `;` rules out falling off the end of the instruction list.
The postcondition after `;` describes the actual exit through `ret`.
The caller's final conditional subtraction is a separate routine. -/
theorem bn_sqr8x_internal_montgomery_square (d : MachineData) (x modulus : List (BitVec 64))
    (n0 : BitVec 64) (ra : Int64) (h : BnSqr8xContext d x modulus n0)
    (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ bn_sqr8x_internal_prog ⦃ fun _ _ => False;
      fun pc s => pc = ra ∧ BnSqr8x.MathematicalPost (d.regs.get64 .rsp) x modulus s ⦄ := by
  let blocks := x.length / 8
  have hblocks : BnSqr8xBlockContext d x modulus n0 blocks := h.toBlockContext
  vcgen [bn_sqr8x_internal_correct d x modulus n0 blocks ra hblocks hret] with
    finish [→ bnSqr8xPost.mathematical hblocks]
end
end MathematicalCorrectness

end Sqr8xArithmetic
