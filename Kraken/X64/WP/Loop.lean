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

/-- The continuation of `Program.Loop` after one step: keep running while control stays in `p`. -/
public abbrev Program.LoopCont (p : Program) (H : Embedding p)
    (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (u : MachineState) : Prop :=
  if u.pc = H.endAddr ∨ p.IsLabelAddr u.pc ∨ (∃ i < p.length, u.pc = Host.addrOf (H.start + i))
  then Program.Loop p H Q E u else E u.pc u.data

/-- At the end address, `Program.Loop` holds if `Q` does. -/
public theorem Program.loop_done {p : Program} {H : Embedding p} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} (hq : Q s) :
    Program.Loop p H Q E ⟨s, H.endAddr⟩ :=
  Until.stop (fun h => h rfl) hq

/-- Every address of a directive of `p`, and its end address, continues the loop. -/
public theorem Program.loopCont_of_le {p : Program} {H : Embedding p} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {j : Nat} (hj : j ≤ p.length) {s : MachineData}
    (h : Program.Loop p H Q E ⟨s, Host.addrOf (H.start + j)⟩) :
    Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + j)⟩ := by
  unfold Program.LoopCont
  refine (ite_eq_left ?_).symm ▸ h
  rcases Nat.lt_or_ge j p.length with hlt | hge
  · exact Or.inr (Or.inr ⟨j, hlt, rfl⟩)
  · exact Or.inl (by rw [Embedding.endAddr_def, Nat.le_antisymm hj hge])

/--
One step of `Program.Loop` from the `i`-th directive of `p`: it suffices that interpreting the
directive leads to states that continue the loop.
-/
public theorem Program.loop_of_interp {p : Program} {H : Embedding p} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {i : Nat} {d : Directive} (hi : p[i]? = some d)
    {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf (H.start + i), Host.addrOf (H.start + i + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (H.start + i + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All
      (Program.LoopCont p H Q E)) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ := by
  have hlt : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
  have hk := prog_at (H := H) hi
  have hd : Host.exe.program[H.start + i]? =
      some {directive := d, size := Kraken.Layout.size Instr (H.start + i) : Kraken.Sized Directive} := by
    rw [Host.exe_getElem?, hk]; rfl
  have hsucc := Host.addrOf_succ hk
  rcases Nat.eq_zero_or_pos (Kraken.Layout.size Instr (H.start + i)) with h0 | hz
  · -- A zero-size directive is inert and does not move the program counter.
    rw [h0] at hd hsucc
    have hinert := Host.inert_of_size_zero (List.mem_of_getElem? hd)
    rw [hinert] at h
    simp only [Effects.All] at h
    have hpc : Host.addrOf (H.start + (i + 1)) = Host.addrOf (H.start + i) := by
      rw [← Nat.add_assoc, hsucc]; simp
    have hc : Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + (i + 1))⟩ := by
      rw [← Nat.add_assoc]; exact h
    have hcond : Host.addrOf (H.start + (i + 1)) = H.endAddr ∨
        p.IsLabelAddr (Host.addrOf (H.start + (i + 1))) ∨
        (∃ j < p.length, Host.addrOf (H.start + (i + 1)) = Host.addrOf (H.start + j)) := by
      rcases Nat.lt_or_ge (i + 1) p.length with hlt' | hge
      · exact Or.inr (Or.inr ⟨i + 1, hlt', rfl⟩)
      · exact Or.inl (by rw [Embedding.endAddr_def, show i + 1 = p.length by omega])
    unfold Program.LoopCont at hc
    rw [ite_eq_left hcond, hpc] at hc
    exact hc
  · refine Until.step (fun heq => ?_) ?_ (fun _ hy => hy)
    · -- The address of a non-empty directive is not the end address.
      have hs := Host.sizeBefore_eq_of_addrOf_eq heq
      have h1 := Host.sizeBefore_succ hk
      have h2 := Host.sizeBefore_mono (show H.start + i + 1 ≤ H.start + p.length by omega)
      omega
    · obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
      have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
        ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
          Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
      unfold step1 Executable.step
      change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf (H.start + i))) s
        (Host.addrOf (H.start + i)) _).All _
      rw [hat]
      refine (Directives.interp_inert_append hinert _ _ _ _).mpr ?_
      rw [hsucc] at h
      exact h

end
