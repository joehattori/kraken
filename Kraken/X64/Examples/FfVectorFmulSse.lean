import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem

/-!
# `ff_vector_fmul_sse`: an SSE loop that writes an array its inputs may overlap

FFmpeg's `vector_fmul` multiplies two vectors `src0`, `src1` of `len` floats
elementwise into a third, `dst` (`vector_fmul_c` in `libavutil/float_dsp.c`).
Its SSE version (`libavutil/x86/float_dsp.asm`, the `VECTOR_FMUL` macro under
`INIT_XMM sse`) walks the arrays from the end down, 64 bytes per iteration:
`lea` turns the float count in `ecx` into the offset of the last 64-byte chunk,
and each iteration loads the four 16-byte pieces of the chunk of `src0`,
multiplies them by those of `src1` (`mulps`), stores the products into `dst`,
and lowers the offset by 64, until it goes negative.

The program below is the routine's machine code, disassembled from the object
file, in the parser's AT&T syntax. The seven `nop`s are the `ALIGN 16` padding
before `.loop`. The final `ret` is left off, so a run ends by falling off the
end of the program after the `jge`, as in `SbrNegOdd64.lean`. Where an operand
has a displacement, NASM put the offset register in the base slot and the array
pointer in the index slot, as in `0x10(%rcx,%rsi,1)`.

We prove that the routine terminates without faulting, and that it writes no
memory outside `dst`: on exit, `dst` is still an owned block of `4 * len` bytes
(with new contents), and the rest of memory still satisfies the frame `R`. The
floats themselves are not tracked. Compared with the API in
`libavutil/float_dsp.h` (all three pointers 32-byte aligned, `len` a multiple
of 16), the proof finds:

* `len = 0` is not safe, although the API allows it. The 32-bit `lea` computes
  `4 * 0 - 64`, which wraps to `2^32 - 64`, and the loop, which tests at the
  bottom, then runs over the 4 GiB above each pointer. The precondition asks
  for `0 < len`.
* The byte count is computed in 32 bits. The precondition `len * 4 < 2^32`
  keeps it from wrapping. For `2^30 < len < 2^31` the wrap makes the loop
  multiply only the first `len - 2^30` floats: in bounds, but not what the
  caller asked for.
* The pointers need only 16-byte alignment, which the legacy SSE memory
  operands of `movaps` and `mulps` require; the API promises 32.
* The upper half of `rcx` is ignored: the ABI leaves it unspecified for an
  `int` argument, and the 32-bit `lea` reads only `ecx`.
* The prototype marks none of the pointers `restrict`, so the arrays may
  overlap in any way. The precondition owns each array in its own fact about
  the initial memory, and none of these facts says where one array is relative
  to another. The proof covers every overlap, but for safety only: with
  partially overlapping arrays, the routine can compute a different result than
  the C code, which runs from the first element up. Exact aliasing
  (`dst == src0` or `dst == src1`) gives the C code's result.

The proof has the shape of `ButterfliesBlocks.lean`: `vfm_table` gives the
assertion at each label (at `.loop`, the loop invariant), `vfm_var` is the
variant, and `MachineWP.cfg` with `cfg_cases` leaves one `vcgen` obligation per
block, each closed by `finish`. The invariant keeps `dst`'s block, which
`Mem.Blocks.storeInt` carries across each store, and `Mem.SubDom d.dmem s.dmem`:
a store never unmaps an address, so the loads from `src0` and `src1`, which
their facts show readable in the initial memory, stay readable whatever the
stores into `dst` change.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

/-- The program: `ff_vector_fmul_sse` from the object file, without its `ret`. -/
def vector_fmul_sse_prog : Program := parse("
start:
    lea -0x40(,%ecx,4),%rcx
    nop
    nop
    nop
    nop
    nop
    nop
    nop
.loop:
    movaps (%rsi,%rcx,1),%xmm0
    movaps 0x10(%rcx,%rsi,1),%xmm1
    mulps (%rdx,%rcx,1),%xmm0
    mulps 0x10(%rcx,%rdx,1),%xmm1
    movaps %xmm0,(%rdi,%rcx,1)
    movaps %xmm1,0x10(%rcx,%rdi,1)
    movaps 0x20(%rcx,%rsi,1),%xmm0
    movaps 0x30(%rcx,%rsi,1),%xmm1
    mulps 0x20(%rcx,%rdx,1),%xmm0
    mulps 0x30(%rcx,%rdx,1),%xmm1
    movaps %xmm0,0x20(%rcx,%rdi,1)
    movaps %xmm1,0x30(%rcx,%rdi,1)
    sub $0x40,%rcx
    jge .loop
")

/-! ## The proof -/

/-- The spec table: the machine at each label, for a run that started on `d`
over arrays of `L` bytes. At `.loop` it is the loop invariant: the pointers
are as they were, `rcx` is the offset of the current 64-byte chunk, which lies
inside the arrays, `dst` is still a block of `L` bytes separated from the frame
`R`, and every address mapped at the start is still mapped. -/
private abbrev vfm_table (d : MachineData) (L : Nat) (R : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | ".loop", s =>
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      s.regs.get64 .rdx = d.regs.get64 .rdx ∧ rcx + 64 ≤ L ∧ rcx % 64 = 0 ∧
      (s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, L)] ⋆ R) ∧ Mem.SubDom d.dmem s.dmem
  | _, _ => False

/-- The variant: the offset of the current chunk at `.loop`, which each
iteration lowers by 64; the entry runs once. -/
private abbrev vfm_var : Label → MachineData → Nat
  | "start", _ => 2 ^ 64
  | ".loop", s => (s.regs.get64 .rcx).toNat
  | _, _ => 0

variable [layout : _root_.Layout] [Executable.ValidLayout (layout vector_fmul_sse_prog)]

/-- The ambient code of the example: `vector_fmul_sse_prog`, laid out. -/
local instance vector_fmul.env : CodeEnv := ⟨layout vector_fmul_sse_prog⟩

theorem vector_fmul_sse_correct (d : MachineData) (len : Nat)
    (h_len_reg : d.regs.get (Reg.low .rcx .W32) = BitVec.ofNat 32 len)
    (h_len_mod : len % 16 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_dst_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_src0_aligned : isAligned 16 (d.regs.get64 .rsi) = true)
    (h_src1_aligned : isAligned 16 (d.regs.get64 .rdx) = true)
    (R R₀ R₁ : DataMem → Prop)
    (h_dst : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R)
    (h_src0 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, len * 4)] ⋆ R₀)
    (h_src1 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdx, len * 4)] ⋆ R₁) :
    ⦃ fun s => s = d ⦄
      vector_fmul_sse_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R ⦄ := by
  apply MachineWP.cfg (vfm_table d (len * 4) R) vfm_var
  cfg_cases [vector_fmul_sse_prog]
  · vcgen with finish
  · vcgen with finish

/-- `vector_fmul_sse_correct`, read at the machine as the baseline judgment. -/
theorem vector_fmul_sse_terminates_and_safe
    (s₀ : MachineData)
    (len : Nat)
    (h_len_reg   : s₀.regs.get (Reg.low .rcx .W32) = BitVec.ofNat 32 len)
    (h_len_mod   : len % 16 = 0)
    (h_len_pos   : 0 < len)
    (h_len_bound : len * 4 < 2 ^ 32)
    (h_dst_aligned  : isAligned 16 s₀.regs.rdi.toBitVec)
    (h_src0_aligned : isAligned 16 s₀.regs.rsi.toBitVec)
    (h_src1_aligned : isAligned 16 s₀.regs.rdx.toBitVec)
    (R R₀ R₁ : DataMem → Prop)
    (h_dst  : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec, len * 4)] ⋆ R)
    (h_src0 : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rsi.toBitVec, len * 4)] ⋆ R₀)
    (h_src1 : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rdx.toBitVec, len * 4)] ⋆ R₁) :
    Eventually (straightlineStep (layout vector_fmul_sse_prog))
      (fun s' => s'.1.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec, len * 4)] ⋆ R)
      (s₀, Kraken.Layout.start Directive) :=
  Program.run_of_triple
    (vector_fmul_sse_correct s₀ len h_len_reg h_len_mod h_len_pos h_len_bound
      h_dst_aligned h_src0_aligned h_src1_aligned R R₀ R₁ h_dst h_src0 h_src1) rfl
