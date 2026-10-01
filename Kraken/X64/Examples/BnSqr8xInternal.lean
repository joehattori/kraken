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

/-- The `.Lsqr4x_inner` loop of `bn_sqr8x_internal` (`x86_64-mont5-linux.S`),
preceded by its index initialization `lea (%rbp),%rcx` (`lea ($i),$j`).

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
def sqr4x_inner_prog : Program := parse("
start:
    lea (%rbp),%rcx
.Lsqr4x_inner:
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
  cfg_cases [sqr4x_inner_prog]
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
