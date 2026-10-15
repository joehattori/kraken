import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.StateSimp

/-!
# `bn_sqr8x_internal`: BoringSSL multi-precision squaring

In BoringSSL's `x86_64-mont5` (`crypto/fipsmodule/bn/asm/x86_64-mont5.pl`),
`bn_sqr8x_internal` squares an `N`-limb bignum `a` modulo `n` in Montgomery
form. It has a squaring part and a reduction part:

1. Cross-products: `t = Σ_{i<j} a[i]*a[j]`, accumulated into a temporary buffer
   `t` on the stack. `.Lsqr4x_1st` computes the products with `a[0]`, then
   each iteration of `.Lsqr4x_outer` takes the next pair of limbs and runs the
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
  the input and accumulator limb arrays.
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
