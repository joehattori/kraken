import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.StateSimp

open Kraken.X64.Parser Kraken Std.WP MachineWP Lean.Order

set_option experimental.vcgen true

attribute [local grind norm]
  MachineData.regs_mk MachineData.zmms_mk MachineData.status_mk MachineData.dmem_mk
  Reg64s.get64_set64 Reg64s.set64_set64
attribute [local sym_simp] Option.map_some Option.map_none BitVec.zero_add

-- The source's high half is discarded, and MOVQ preserves flags, memory,
-- and every vector register, even when the integer destination was nonzero.
example [CodeEnv] (d : MachineData) :
    ⦃ fun s => s = d ⦄ parse("movq %xmm2, %rbp") ⦃ fun _ s =>
      s.regs = d.regs.set64 .rbp ((d.zmms.get (.xmm .mm2)).extractLsb' 0 64) ∧
      s.status = d.status ∧ s.zmms = d.zmms ∧ s.dmem = d.dmem ⦄ := by
  vcgen simplifying_assumptions with finish

private def returnProgram : Program := parse("
entry:
  movq $1, %rax
  jmp done
done:
  addq $1, %rax
  ret
")

private abbrev returnTable (d : MachineData) : Label → MachineData → Prop
  | "entry", s => s = d
  | "done", s => s.regs.get64 .rax = 1 ∧
      s.regs.get64 .rsp = d.regs.get64 .rsp ∧ s.dmem = d.dmem
  | _, _ => False

section
variable [layout : _root_.Layout] [Executable.ValidLayout (layout returnProgram)]
local instance : CodeEnv := ⟨layout returnProgram⟩

-- The CFG has both an internal edge and an external return. The exit
-- postcondition checks the return address and the stack-pointer adjustment.
example (d : MachineData) (ra : Int64) (hret : d.retAddr = some ra) :
    ⦃ fun s => s = d ⦄ returnProgram ⦃ fun _ _ => False;
      fun pc s => pc = ra ∧ s.regs.get64 .rax = 2 ∧
        s.regs.get64 .rsp = d.regs.get64 .rsp + 8 ∧ s.dmem = d.dmem ⦄ := by
  apply MachineWP.cfg_exit (returnTable d)
  cfg_cases [returnProgram]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
end

private def appendPrefix : Program := parse("movq $3,%rax")
private def appendSuffix : Program := parse("addq $4,%rax")

private theorem append_prefix_correct [CodeEnv] (d : MachineData) :
    ⦃ fun s => s = d ⦄ appendPrefix ⦃ fun _ s =>
      s.regs.get64 .rax = 3 ∧ s.regs.get64 .rbx = d.regs.get64 .rbx ⦄ := by
  vcgen [appendPrefix] simplifying_assumptions with finish

-- A fragment specification composes with following instructions through ++.
example [CodeEnv] (d : MachineData) :
    ⦃ fun s => s = d ⦄ appendPrefix ++ appendSuffix ⦃ fun _ s =>
      s.regs.get64 .rax = 7 ∧ s.regs.get64 .rbx = d.regs.get64 .rbx ⦄ := by
  vcgen [append_prefix_correct, appendSuffix] simplifying_assumptions with finish
