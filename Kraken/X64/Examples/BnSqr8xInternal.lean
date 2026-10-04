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

* `.Lsqr4x_inner` (section `Sqr4xInner`): termination, no faults, memory safety.
* One two-limb iteration (section `Sqr4xInnerFunctional`): exact functional
  correctness of both stored limbs and both outgoing carries. The arithmetic
  specification uses natural-number multiplication, quotient, and remainder.
  Functional correctness across all iterations remains to be proved.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

attribute [local grind norm]
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

/-- The inner loop, with index initialization and its comparison and back edge. -/
def sqr4x_inner_prog : Program :=
  parse("
start:
    lea (%rbp),%rcx
.Lsqr4x_inner:
") ++ sqr4x_inner_iteration ++ parse("
    cmpq $0,%rcx
    jne .Lsqr4x_inner
")

/-! ### The proof -/

/-- The spec table: at `.Lsqr4x_inner`, `%rdi` and `%rsi` remain at the end of
the `L`-byte slices, `%rcx` is a negative 16-byte-aligned offset in
`[2 ^ 64 - L, 2 ^ 64)`, the output block `[%rdi - L, %rdi)` is preserved, and
every initially mapped address remains mapped (`Mem.SubDom d.dmem s.dmem`). -/
private abbrev sqr4x_inner_table (d : MachineData) (L : Nat) (R : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | ".Lsqr4x_inner", s =>
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      2 ^ 64 - L ≤ rcx ∧ rcx < 2 ^ 64 ∧ rcx % 16 = 0 ∧
      (s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R) ∧
      Mem.SubDom d.dmem s.dmem
  | _, _ => False

/-- The loop variant: the distance `2 ^ 64 - %rcx` remaining until `%rcx` wraps
to `0` at the end of the `L`-byte slice. -/
private abbrev sqr4x_inner_var : Label → MachineData → Nat
  | "start", _ => 2 ^ 64
  | ".Lsqr4x_inner", s => 2 ^ 64 - (s.regs.get64 .rcx).toNat
  | _, _ => 0

variable [layout : _root_.Layout] [Executable.ValidLayout (layout sqr4x_inner_prog)]

/-- The ambient code of the example: `sqr4x_inner_prog`, laid out. -/
local instance sqr4x_inner.env : CodeEnv := ⟨layout sqr4x_inner_prog⟩

theorem sqr4x_inner_correct (d : MachineData) (L : Nat)
    (h_rbp : d.regs.get64 .rbp = 0#64 - BitVec.ofNat 64 L)
    (h_L_mod : L % 16 = 0) (h_L_pos : 0 < L) (h_L_bound : L < 2 ^ 63)
    (R R₀ : DataMem → Prop)
    (h_t : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R)
    (h_a : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi - BitVec.ofNat 64 L, L)] ⋆ R₀) :
    ⦃ fun s => s = d ⦄
      sqr4x_inner_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi - BitVec.ofNat 64 L, L)] ⋆ R ⦄ := by
  apply MachineWP.cfg (sqr4x_inner_table d L R) sqr4x_inner_var
  cfg_cases [sqr4x_inner_prog, sqr4x_inner_iteration]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

/-- `sqr4x_inner_correct`, read at the machine as the baseline judgment. -/
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
  Program.run_of_triple (sqr4x_inner_correct s₀ L h_rbp h_L_mod h_L_pos h_L_bound R R₀ h_t h_a) rfl

end Sqr4xInner

/-! ## Functional correctness of one iteration

The control-flow proof above deliberately forgets memory contents. To test the
value-level obligations separately, verify one complete body against a pure
arithmetic specification. A small multiply-add lemma accounts for the two carries
of each chain. The machine proof then uses the same instruction specifications as
the safety proof, with a final symbolic simplification before `finish`.
-/

section Sqr4xInnerFunctional

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
  split <;> have ha := a.isLt <;> have hb := b.isLt <;> omega

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
  have hca := (addCarry (a * b) c).isLt
  have hcb := (addCarry t (a * b + c)).isLt
  omega

private theorem mac_lo (a b c t : BitVec 64) :
    macLo a b c t = BitVec.ofNat 64 ((a.toNat * b.toNat + c.toNat + t.toNat) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have h := mul_add_words_eq a b c t
  have hl := (macLo a b c t).isLt
  simp only [BitVec.toNat_ofNat]
  change (macLo a b c t).toNat = _
  omega

private theorem mac_hi (a b c t : BitVec 64) :
    macHi a b c t = BitVec.ofNat 64 ((a.toNat * b.toNat + c.toNat + t.toNat) / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have h := mul_add_words_eq a b c t
  have hl := (macLo a b c t).isLt
  have hh := (macHi a b c t).isLt
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
  intro i hi j hj heq
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

end Sqr4xInnerFunctional
