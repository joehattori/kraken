/-
The original `swap` (three `xor`s exchanging `rax` and `rbx`), wrapped as a
procedure and called twice: the involution restores both registers, and the
stack pointer comes back to its entry value. `MachineWP.call_spec` links each
call to its return: the machine pushes the address behind the call cell, and
the callee's `ret` at that address continues the caller's run.
-/
import Kraken.X64.Parser
import Kraken.MachineWP

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false

/-- The program: the caller, the procedure it calls twice, the tail. -/
def pswap : Program := parse("
start:
  call swap
  call swap
  jmp done
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
done:
  nop
")

/-- The procedure's body: the three `xor`s and the return. -/
abbrev pswap.body : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
")

/-- The spec table: the caller starts on `d`, the tail holds the answer, and
the procedure is entered by a call rather than by an edge of the table. -/
private abbrev pswap_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.get64 .rax = d.regs.get64 .rax ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
      ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
  | _, _ => False

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pswap)]

/-- The ambient code of the example: `pswap`, laid out. -/
local instance pswap.env : CodeEnv := ⟨layout pswap⟩

/-- Where `pswap` sits: the placement the control-flow rule and the call rule
both read. -/
private theorem pswap_placed : @Program.Placed ⟨layout pswap⟩ pswap "start" :=
  Program.placed_of_layout (by decide) rfl (by decide)

/-- The procedure sits at its label. -/
private theorem pswap_body_placed : cenv.sits ((_root_.Executable.labels cenv).label "swap") pswap.body :=
  pswap_placed.block "swap" ⟨"swap", pswap.body, some "done"⟩ rfl

/-- What the procedure needs of its caller: the slot the call writes is
mapped, so the return address has somewhere to go. -/
private abbrev SwapPre (s : MachineData) : Prop :=
  (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
    Width.W64.bytes).isSome = true

/-- What the procedure leaves the caller: the two registers exchanged, the
stack pointer restored, and the slot it used still mapped. -/
private abbrev SwapPost (s s' : MachineData) : Prop :=
  s'.regs.get64 .rax = s.regs.get64 .rbx ∧ s'.regs.get64 .rbx = s.regs.get64 .rax
    ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp ∧ SwapPre s'

omit [Executable.ValidLayout (layout pswap)] in
/-- The procedure, from the state its caller pushed: it exchanges the two
registers and returns to the address on the stack. -/
private theorem pswap_body_spec (ra : Int64) (s : MachineData) :
    ⦃ fun t => t = s.pushRa ra ∧ SwapPre s ⦄
      pswap.body
    ⦃ (fun _ _ => False); fun a s' => a = ra ∧ SwapPost s s' ⦄ := by
  vcgen with finish

theorem pswap_correct (d : MachineData) (hslot : SwapPre d) :
    ⦃ fun s => s = d ⦄
      pswap
    ⦃ fun _ s => s.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.regs.get64 .rsp = d.regs.get64 .rsp ⦄ := by
  have hcall := MachineWP.fun_spec_from_label pswap_body_placed pswap_body_spec
  have hpl := pswap_placed
  apply MachineWP.cfg (pswap_table d)
  cfg_cases [pswap]
  · vcgen [hcall] simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

/-- `pswap_correct`, read at the machine as the baseline judgment. -/
theorem pswap_correct_run (d : MachineData) (hslot : SwapPre d) :
    Eventually (straightlineStep (layout pswap))
      (fun s => s.1.regs.get64 .rax = d.regs.get64 .rax
        ∧ s.1.regs.get64 .rbx = d.regs.get64 .rbx
        ∧ s.1.regs.get64 .rsp = d.regs.get64 .rsp)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (pswap_correct d hslot) rfl
