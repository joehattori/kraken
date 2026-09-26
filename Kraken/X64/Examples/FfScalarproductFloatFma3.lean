import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem

/-!
# `ff_scalarproduct_float_fma3`: an AVX/FMA3 loop over two arrays that may alias

FFmpeg's `scalarproduct_float` returns the dot product of two vectors `v1`, `v2`
of `len` floats (`avpriv_scalarproduct_float_c` in `libavutil/float_dsp.c`).
Its FMA3 version (`libavutil/x86/float_dsp.asm`) consumes the `4 * len` bytes
of each vector in chunks. While at least 128 bytes remain, `.loop128` does 128
bytes per iteration into four ymm accumulators. Then the code does at most one
chunk each of 64, 32 and 16 bytes, adding the accumulators together as it
narrows, and finally sums the four lanes of `xmm0` into its low lane, the
return value.

The program below is the routine's machine code, disassembled from the object
file, in the parser's AT&T syntax. The routine returns from four places. The
last `ret` is left off, the other three become `jmp done`, and `done` labels a
`nop` at the end of the program, as in `CallSwap.lean` (reading the triple at
the machine needs the program to end in an instruction). Each exit keeps the
`vzeroupper` before its `ret`, so `done` sees the machine the `ret` would have.

We prove that the routine terminates without faulting, and that it leaves data
memory as it was. The C prototype does not mark `v1` and `v2` `restrict`, so
the two arrays may overlap: the precondition owns each array in its own fact
about the same memory, and neither fact says where one array is relative to
the other. Only `v1` must be 16-byte aligned (the API promises it for both),
for the `vmovaps` in `.loop16`; the other memory operands are VEX-encoded and
have no alignment requirement. `len` must be positive (with `len = 0` the code
still reads 16 bytes of each array), a multiple of 4, and small enough that
the byte count, which the code computes in 32 bits, does not wrap. The floats
themselves are not tracked.

The proof has the shape of `ButterfliesBlocks.lean`: `sp_table` gives the
assertion at each label, `sp_var` is the variant, and `MachineWP.cfg` with
`cfg_cases` leaves one `vcgen` obligation per block, each closed by `finish`.
Only `.loop128` iterates. The code enters `.loop64`, `.loop32` and `.loop16`
with less than two chunks left, so each of them runs once, and its back edge is
never taken.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

/-- The program: `ff_scalarproduct_float_fma3` from the object file, with its
exits leading to `done` instead of returning. -/
def scalarproduct_fma3_prog : Program := parse("
start:
    xor %r8,%r8
    vxorps %ymm0,%ymm0,%ymm0
    shl $0x2,%edx
    mov %rdx,%rcx
    cmp $0x20,%rcx
    jl .l16
    cmp $0x40,%rcx
    jl .l32
    vxorps %ymm1,%ymm1,%ymm1
    cmp $0x80,%rcx
    jl .l64
    and $0xffffffffffffff80,%rcx
    vxorps %ymm2,%ymm2,%ymm2
    vxorps %ymm3,%ymm3,%ymm3
.loop128:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vmovups 0x40(%rdi,%r8,1),%ymm6
    vmovups 0x60(%rdi,%r8,1),%ymm7
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    vfmadd231ps 0x40(%rsi,%r8,1),%ymm6,%ymm2
    vfmadd231ps 0x60(%rsi,%r8,1),%ymm7,%ymm3
    sub $0xffffffffffffff80,%r8
    cmp %rcx,%r8
    jl .loop128
    vaddps %ymm2,%ymm0,%ymm0
    vaddps %ymm3,%ymm1,%ymm1
    mov %rdx,%rcx
    and $0x7f,%rcx
    cmp $0x40,%rcx
    jge .l64
    vaddps %ymm1,%ymm0,%ymm0
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l64:
    and $0xffffffffffffffc0,%rcx
    add %r8,%rcx
.loop64:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    add $0x40,%r8
    cmp %rcx,%r8
    jl .loop64
    vaddps %ymm1,%ymm0,%ymm0
    mov %rdx,%rcx
    and $0x3f,%rcx
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l32:
    and $0xffffffffffffffe0,%rcx
    add %r8,%rcx
.loop32:
    vmovups (%rdi,%r8,1),%ymm4
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    add $0x20,%r8
    cmp %rcx,%r8
    jl .loop32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    mov %rdx,%rcx
    and $0x1f,%rcx
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    jmp done
.l16:
    and $0xfffffffffffffff0,%rcx
    add %r8,%rcx
.loop16:
    vmovaps (%rdi,%r8,1),%xmm1
    vmulps (%rsi,%r8,1),%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    add $0x10,%r8
    cmp %rcx,%r8
    jl .loop16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
done:
    nop
")

/-! ## The proof -/

/-- The spec table: the machine at each label, for a run that started on `d`
over arrays of `L` bytes. `r8` is the offset of the next chunk. At `.loop128`,
`rcx` is `L` rounded down to a multiple of 128; at `.l64`, `.l32` and `.l16` it
is the number of bytes left; at `.loop64`, `.loop32` and `.loop16` it is the
offset where the loop's one chunk ends. The entries in between also say that
`rdi`, `rsi`, the byte count in `rdx` and data memory are as they were. -/
private abbrev sp_table (d : MachineData) (L : Nat) : Label → MachineData → Prop
  | "start", s => s = d
  | ".loop128", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx = L / 128 * 128 ∧ r8 % 128 = 0 ∧ r8 < rcx
  | ".l64", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx + r8 = L ∧ 64 ≤ rcx ∧ rcx < 128 ∧ r8 % 128 = 0
  | ".loop64", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx = r8 + 64 ∧ r8 + 64 ≤ L ∧ L < r8 + 128 ∧ r8 % 64 = 0
  | ".l32", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx + r8 = L ∧ 32 ≤ rcx ∧ rcx < 64 ∧ r8 % 64 = 0
  | ".loop32", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx = r8 + 32 ∧ r8 + 32 ≤ L ∧ L < r8 + 64 ∧ r8 % 32 = 0
  | ".l16", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx + r8 = L ∧ 16 ≤ rcx ∧ rcx < 32 ∧ r8 % 32 = 0
  | ".loop16", s =>
      let r8 := (s.regs.get64 .r8).toNat
      let rcx := (s.regs.get64 .rcx).toNat
      s.regs.get64 .rdi = d.regs.get64 .rdi ∧ s.regs.get64 .rsi = d.regs.get64 .rsi ∧
      (s.regs.get64 .rdx).toNat = L ∧ s.dmem = d.dmem ∧
      rcx = r8 + 16 ∧ r8 + 16 ≤ L ∧ L < r8 + 32 ∧ r8 % 16 = 0
  | "done", s => s.dmem = d.dmem
  | _, _ => False

/-- The variant: the bytes `.loop128` has left to do. Its back edge is the only
backward jump the code takes; the entry runs once. -/
private abbrev sp_var : Label → MachineData → Nat
  | "start", _ => 2 ^ 64
  | ".loop128", s => (s.regs.get64 .rcx).toNat - (s.regs.get64 .r8).toNat
  | _, _ => 0

variable [layout : _root_.Layout] [Executable.ValidLayout (layout scalarproduct_fma3_prog)]

/-- The ambient code of the example: `scalarproduct_fma3_prog`, laid out. -/
local instance scalarproduct.env : CodeEnv := ⟨layout scalarproduct_fma3_prog⟩

/- The program is long: deciding the side conditions of `MachineWP.cfg` and
splitting the program with `cfg_cases` recurse deeper than the default
`maxRecDepth`, and the nine obligations take more than the default heartbeats. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 400000 in
theorem scalarproduct_fma3_correct (d : MachineData) (len : Nat)
    (h_len_reg : d.regs.get (Reg.low .rdx .W32) = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_v1_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (R₁ R₂ : DataMem → Prop)
    (h_v1 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, len * 4)] ⋆ R₁)
    (h_v2 : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rsi, len * 4)] ⋆ R₂) :
    ⦃ fun s => s = d ⦄ scalarproduct_fma3_prog ⦃ fun _ s => s.dmem = d.dmem ⦄ := by
  apply MachineWP.cfg (sp_table d (len * 4)) sp_var
  cfg_cases [scalarproduct_fma3_prog]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish

/-- `scalarproduct_fma3_correct`, read at the machine as the baseline judgment. -/
theorem scalarproduct_fma3_terminates_and_safe
    (s₀ : MachineData)
    (len : Nat)
    (h_len_reg   : s₀.regs.get (Reg.low .rdx .W32) = BitVec.ofNat 32 len)
    (h_len_mod   : len % 4 = 0)
    (h_len_pos   : 0 < len)
    (h_len_bound : len * 4 < 2 ^ 32)
    (h_v1_aligned : isAligned 16 s₀.regs.rdi.toBitVec)
    (R₁ R₂ : DataMem → Prop)
    (h_v1 : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec, len * 4)] ⋆ R₁)
    (h_v2 : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rsi.toBitVec, len * 4)] ⋆ R₂) :
    Eventually (straightlineStep (layout scalarproduct_fma3_prog))
      (fun s' => s'.1.dmem = s₀.dmem)
      (s₀, Kraken.Layout.start Directive) :=
  Program.run_of_triple
    (scalarproduct_fma3_correct s₀ len h_len_reg h_len_mod h_len_pos h_len_bound
      h_v1_aligned R₁ R₂ h_v1 h_v2) rfl
