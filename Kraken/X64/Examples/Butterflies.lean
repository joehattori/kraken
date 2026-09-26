import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem

/-!
# Butterflies: an SSE loop over two arrays

The loop walks two 16-byte-aligned float arrays `v1`, `v2` of `len` floats
(`4 * len` bytes) in 16-byte chunks, replacing `(a, b)` by `(a + b, a - b)`.
Both pointers are first advanced to one past the end of their array, and a
single negative index `rdx` counts up towards zero, so the loop needs only one
`add` and a `jl`.

We prove that the loop terminates without faulting, and that on exit the two
arrays (with some new contents) are still where they were, separated from each
other and from the frame `R`.

`butterflies_correct` is one `Triple` of the machine-founded wp, proved through
the control-flow rule: `bf_table` gives the assertion at each label (at `loop`,
the loop invariant), `bf_var` is the variant (the bytes still to process), and
`MachineWP.cfg` with `cfg_cases` produces one `vcgen` obligation per block,
each closed by `finish`. The arrays are two `Mem.Blocks`, owned regions whose
contents are not tracked. The library's `grind` rules for accesses inside
blocks, and for the address, alignment and flag arithmetic, are all the proof
needs. `Program.run_of_triple` reads the triple back as the baseline judgment
(`butterflies_float_terminates_and_safe`).
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

/-- The program: the prologue moves both pointers to the end of their array
and negates the byte count into `rdx`; each iteration of the loop does one
16-byte chunk of both arrays. -/
def butterflies_float_prog : Program := parse("
start:
    shl $2, %edx
    add %rdx, %rdi
    add %rdx, %rsi
    neg %rdx
loop:
    movaps (%rdi,%rdx,1), %xmm0
    movaps (%rsi,%rdx,1), %xmm1
    movaps %xmm0, %xmm2
    subps %xmm1, %xmm2
    addps %xmm1, %xmm0
    movaps %xmm2, (%rsi,%rdx,1)
    movaps %xmm0, (%rdi,%rdx,1)
    add $16, %rdx
    jl loop
")

/-! ## The proof -/

/- The `jl` exit reads the overflow flag, which compares signed values. -/
attribute [local grind =] BitVec.signed_eq

/-- The jump target of the loop is mapped. -/
@[grind .] private theorem bf_loop_isSome :
    (Program.blockAt butterflies_float_prog "loop").isSome := by decide

/-- The spec table: the machine at each label, for a run that started on `d`
over arrays of `L` bytes. At `loop` it is the loop invariant: both pointers sit
one past the end of their array, `rdx` is minus the bytes still to process (a
positive multiple of 16, at most `L`), and the arrays are in place. -/
private abbrev bf_table (d : MachineData) (L : Nat) (R : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | "loop", s =>
      let j := (-s.regs.get64 .rdx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi + BitVec.ofNat 64 L ∧
      s.regs.get64 .rsi = d.regs.get64 .rsi + BitVec.ofNat 64 L ∧
      0 < j ∧ j ≤ L ∧ j % 16 = 0 ∧
      s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L), (d.regs.get64 .rsi, L)] ⋆ R
  | _, _ => False

/-- The variant: the bytes still to process at `loop`; the prologue runs once. -/
private abbrev bf_var : Label → MachineData → Nat
  | "loop", s => (-s.regs.get64 .rdx).toNat
  | _, _ => 2 ^ 64

variable [layout : _root_.Layout] [Executable.ValidLayout (layout butterflies_float_prog)]

/-- The ambient code of the example: `butterflies_float_prog`, laid out. -/
local instance butterflies.env : CodeEnv := ⟨layout butterflies_float_prog⟩

theorem butterflies_correct (d : MachineData) (len : Nat)
    (h_len_reg : d.regs.get (Reg.low .rdx .W32) = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_bound : len * 4 < 2 ^ 31) (h_len_gt : len > 0)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_v2_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆
      Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      butterflies_float_prog
    ⦃ fun _ s => s.dmem =⋆
        Mem.Blocks [(d.regs.get64 .rdi, len * 4), (d.regs.get64 .rsi, len * 4)] ⋆ R ⦄ := by
  apply MachineWP.cfg (bf_table d (len * 4) R) bf_var
  cfg_cases [butterflies_float_prog]
  · vcgen with finish
  · vcgen with finish

/-- `butterflies_correct`, read at the machine as the baseline judgment. The
two arrays, with their contents, are the two blocks, and the blocks on exit
are two arrays with some contents. -/
theorem butterflies_float_terminates_and_safe
    (s₀ : MachineData)
    (v1 v2 : List UInt8)
    (len : Nat)
    (h_len_reg   : s₀.regs.get (Reg.low .rdx .W32) = BitVec.ofNat 32 len)
    (h_len_mod   : len % 4 = 0)
    (h_len_bound : len * 4 < 2^31)
    (h_len_gt    : len > 0)
    (h_v1_len : v1.length = len * 4)
    (h_v2_len : v2.length = len * 4)
    (h_v1_aligned : isAligned 16 s₀.regs.rdi.toBitVec)
    (h_v2_aligned : isAligned 16 s₀.regs.rsi.toBitVec)
    (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At s₀.regs.rsi.toBitVec) ⋆ R) :
    Eventually (straightlineStep (layout butterflies_float_prog))
      (fun s' =>
        ∃ (v1' v2' : List UInt8),
          v1'.length = len * 4 ∧
          v2'.length = len * 4 ∧
          s'.1.dmem =⋆ Eq (v1'.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2'.At s₀.regs.rsi.toBitVec) ⋆ R)
      (s₀, Kraken.Layout.start Directive) := by
  have hw : len * 4 ≤ 2 ^ 64 := by omega
  obtain ⟨m12, mR, hu, hi, ⟨m1, m2, hu', hi', rfl, rfl⟩, hR⟩ := h_mem
  refine eventually_weaken _ _ _ _ ?_ (Program.run_of_triple
    (butterflies_correct s₀ len h_len_reg h_len_mod h_len_bound h_len_gt h_v1_aligned
      h_v2_aligned R
      ⟨_, mR, hu, hi, ⟨_, _, hu', hi', ⟨hw, v1, h_v1_len, rfl⟩, ⟨hw, v2, h_v2_len, rfl⟩⟩, hR⟩)
    rfl)
  rintro s' ⟨m12, mR, hu, hi, ⟨m1, m2, hu', hi', ⟨-, v1', h1, rfl⟩, ⟨-, v2', h2, rfl⟩⟩, hR⟩
  exact ⟨v1', v2', h1, h2, _, mR, hu, hi, ⟨_, _, hu', hi', rfl, rfl⟩, hR⟩
