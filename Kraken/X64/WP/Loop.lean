module

public import Kraken.Until
public import Kraken.X64.WP.Host
public import Kraken.X64.WP.Basic

open Classical

public def Program.IsLabelAddr [Host] (p : Program) (a : Int64) : Prop :=
  ∃ l ∈ p.labels, label l = a

/--
Run `p` inside embedding `H` until `pc = H.endAddr` (satisfying `Q`) or control leaves `p` (satisfying `E`).
-/
public abbrev Program.Loop [Host] (p : Program) (H : Embedding p)
    (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) : MachineState → Prop :=
  Until (·.pc ≠ H.endAddr)
    (fun cont st => step1 Host.exe st fun u =>
      if u.pc = H.endAddr ∨ p.IsLabelAddr u.pc ∨ (∃ i < p.length, u.pc = Host.addrOf (H.start + i))
      then cont u else E u.pc u.data)
    (fun st => Q st.data)

public theorem Program.wp_of_loop [Host] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : ∀ H : Embedding p, Program.Loop p H Q E ⟨s, H.startAddr⟩) :
    p.wp Q E s := by
  intro k hk
  let H : Embedding p := ⟨k, hk⟩
  have hloop := Until.iff_eventually.mp (h H)
  change Eventually (step1 Host.exe)
    (fun st => (st.pc = Host.addrOf (k + p.length) ∧ Q st.data) ∨ E st.pc st.data) ⟨s, H.startAddr⟩
  generalize ({ data := s, pc := H.startAddr } : MachineState) = x at hloop ⊢
  induction hloop with
  | done y hy =>
    have hpc : y.pc = Host.addrOf (k + p.length) := not_not.mp hy.1
    apply Eventually.done
    exact Or.inl ⟨hpc, hy.2⟩
  | step y next ht _ ih =>
    refine Eventually.step _ _ ht.2 fun u hu => ?_
    split at hu
    · exact ih u hu
    · exact Eventually.done _ (Or.inr hu)

section
variable [Host]

public theorem prog_at {p : Program} {H : Embedding p} {i : Nat} {d : Directive} (hi : p[i]? = some d) :
    Host.prog[H.start + i]? = some d := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.isInfixAt_iff_getElem?.mp H.isInfixAt i hlt, hpi]

public theorem addrOf_label (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    {p : Program} {H : Embedding p} {i : Nat} {l : Label} (hi : p[i]? = some (.label l)) :
    label l = Host.addrOf (H.start + i) :=
  hlab _ _ (prog_at hi)

end
