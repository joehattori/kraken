/-
Alias labels: `alias` and `fin` name the same address, because the label cell
`alias` occupies no bytes. `palias_correct` runs the control-flow rule over
the three blocks, and `palias_correct_run` reads the triple back at the
machine through `Program.run_of_triple`, whose placement handles the shared
address.
-/
import Kraken.X64.Parser
import Kraken.MachineWP

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false

/-- The program: the prologue sets `rdx` and jumps to `fin`, and the tail
carries an alias label directly in front of the jump target. -/
def palias : Program := parse("
init:
  mov $2, %rdx
  jmp fin
alias:
fin:
  nop
")

/-- The spec table: nothing on entry, nothing reaches `alias`, and at `fin`
the register holds the answer. -/
private abbrev palias_table : Label → MachineData → Prop
  | "init", _ => True
  | "fin", s => s.regs.rdx.toNat = 2
  | _, _ => False

variable [layout : _root_.Layout] [Executable.ValidLayout (layout palias)]

/-- The ambient code of the example: `palias`, laid out. -/
local instance palias.env : CodeEnv := ⟨layout palias⟩

theorem palias_correct :
    ⦃ fun _ => True ⦄ palias ⦃ fun _ s => s.regs.rdx.toNat = 2 ⦄ := by
  apply MachineWP.cfg palias_table
  cfg_cases [palias]
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish
  · vcgen simplifying_assumptions with finish

/-- `palias_correct`, read at the machine as the baseline judgment. -/
theorem palias_correct_run (d : MachineData) :
    Eventually (straightlineStep (layout palias))
      (fun s => s.1.regs.rdx.toNat = 2) (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple palias_correct trivial
