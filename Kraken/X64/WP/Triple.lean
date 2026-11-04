module

public import Kraken.X64.WP.Basic
public import Std.WP

/-!
# Hoare triples for `Program.wp`

A `Std.WP.WP` instance for program fragments of the ambient `Host` program, so that
`⦃ P ⦄ prog ⦃ Q; E ⦄` (with `open Std.WP`) means `∀ s, P s → prog.wp (Q ()) E s`.
-/

open Std.WP

public instance Program.instWP [Host] :
    WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans p := ⟨fun Q E s => p.wp (Q ()) E s⟩
  trans_monotone _ _ _ _ _ hE hQ := fun _ h => Program.wp_mono (fun s' => hQ () s') hE h

public theorem Program.triple_iff [Host] {p : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    Triple p P Q E ↔ ∀ s, P s → p.wp (Q ()) E s :=
  ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩
