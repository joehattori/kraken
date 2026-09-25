/-
The separation-logic weakest precondition. `MProp w` is the assertion type of
the separation algebra: predicates over a `w`-bit byte memory, with `∗` the
disjoint-split conjunction of Kraken/Separation.lean. An assertion of the
program logic keeps registers and flags state-passing and sends only the
memory through the algebra: `Reg64s → RegZmms → StatusFlags → MProp 64`, and
`Int64 →` that for the exit channel.

`SepWP.instWP` interprets a `Program` at this assertion language with the
frame rule internalized on both channels: a triple `⦃P⦄ p ⦃Q; E⦄` holds when
the machine-founded wp validates it under every memory frame, held across the
fall-through and across every exit. `SepWP.sep_intro` is the one door in, and
`SepWP.frames` says every program frames every memory assertion, which is
what the frame inference of `vcgen` consumes.
-/
import Kraken.MachineWP
import Kraken.SeparationMem
import Kraken.SeparationTactics

open Std.WP
open Lean.Order

/-! ## The assertion type -/

/-- Assertions over a `w`-bit byte memory: the carrier of the separation
algebra. -/
def MProp (w : Nat) : Type := Mem w → Prop

namespace MProp

variable {w : Nat}

instance : CompleteLattice (MProp w) :=
  inferInstanceAs (CompleteLattice (Mem w → Prop))

instance : Std.WP.Assertion (MProp w) :=
  inferInstanceAs (Std.WP.Assertion (Mem w → Prop))

/-- Separating conjunction: the memory splits into disjoint halves. -/
def sep (P Q : MProp w) : MProp w := Std.ExtHashMap.sep P Q

@[inherit_doc sep] infixr:65 " ∗ " => MProp.sep

/-- The empty assertion: no memory is owned. -/
def emp : MProp w := Std.ExtHashMap.emp

theorem sep_assoc (P Q R : MProp w) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) :=
  Std.ExtHashMap.sep_assoc P Q R

theorem sep_comm (P Q : MProp w) : P ∗ Q = Q ∗ P :=
  Std.ExtHashMap.sep_comm P Q

theorem emp_sep (P : MProp w) : emp ∗ P = P := Std.ExtHashMap.emp_sep P

theorem sep_emp (P : MProp w) : P ∗ emp = P := Std.ExtHashMap.sep_emp P

instance : Std.Associative (MProp.sep (w := w)) := ⟨sep_assoc⟩
instance : Std.Commutative (MProp.sep (w := w)) := ⟨sep_comm⟩
instance : Std.LawfulIdentity (MProp.sep (w := w)) emp where
  left_id := emp_sep
  right_id := sep_emp

/-- The generic sup on `MProp`, pointwise; from the lattice axioms alone. -/
theorem sup_apply (s : MProp w → Prop) (m : Mem w) :
    (CompleteLattice.sup s : MProp w) m ↔ ∃ P, s P ∧ P m := by
  constructor
  · exact fun hm => sup_le s (x := (fun m => ∃ P, s P ∧ P m : MProp w))
      (fun P hP m' hPm' => ⟨P, hP, hPm'⟩) m hm
  · rintro ⟨P, hP, hPm⟩
    exact le_sup (c := s) hP m hPm

/-- The meet on `MProp`, pointwise; from the lattice axioms alone. A memory
spec's precondition is a meet of its pure conjunct and its footprint, and this
reads both off the owned memory. -/
theorem meet_apply (P Q : MProp w) (m : Mem w) : (P ⊓ Q) m ↔ P m ∧ Q m := by
  constructor
  · exact fun h => ⟨meet_le_left P Q m h, meet_le_right P Q m h⟩
  · rintro ⟨hp, hq⟩
    have hR : (fun m' => m' = m ∧ P m ∧ Q m : MProp w) ⊑ P ⊓ Q := by
      apply le_meet <;> intro m' h' <;> obtain ⟨rfl, _, _⟩ := h' <;> assumption
    exact hR m ⟨rfl, hp, hq⟩

/-- A pure assertion holds at a memory exactly when its proposition holds. -/
theorem ofProp_apply_iff (p : Prop) (m : Mem w) : (⌜p⌝ : MProp w) m ↔ p := by
  constructor
  · exact fun h => ofProp_le p (fun _ => p : MProp w) (fun hp _ _ => hp) m h
  · exact fun hp => le_ofProp (fun m' => m' = m : MProp w) p hp m rfl

/-- The bottom assertion holds of no memory; from the lattice axioms alone. -/
theorem bot_apply_iff (m : Mem w) : (⊥ : MProp w) m ↔ False :=
  ⟨fun h => bot_le (fun _ => False : MProp w) m h, False.elim⟩

/-- A frame next to a pure assertion yields the proposition. -/
theorem sep_ofProp_elim {F : MProp w} {p : Prop} {m : Mem w} (h : (F ∗ ⌜p⌝) m) : p := by
  obtain ⟨_, m₂, _, _, _, hp⟩ := h
  exact (ofProp_apply_iff p m₂).mp hp

/-- `(F ∗ ·)` preserves suprema: the split existential commutes with the
join. Its upper adjoint is the magic wand, which the frame closure takes. -/
instance (F : MProp w) : PreservesSup (MProp.sep F) where
  map_sup s := by
    funext m
    apply propext
    show (∃ m₁ m₂, m₁.union m₂ = m ∧ m₁.inter m₂ = ∅ ∧ F m₁
        ∧ (CompleteLattice.sup s : MProp w) m₂)
      ↔ (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = MProp.sep F x) : MProp w) m
    rw [sup_apply (fun y => ∃ x, s x ∧ y = MProp.sep F x) m]
    constructor
    · rintro ⟨m₁, m₂, hu, hd, hF, hsup⟩
      obtain ⟨P, hP, hPm⟩ := (sup_apply s m₂).mp hsup
      exact ⟨F ∗ P, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
    · rintro ⟨g, ⟨P, hP, rfl⟩, m₁, m₂, hu, hd, hF, hPm⟩
      exact ⟨m₁, m₂, hu, hd, hF, (sup_apply s m₂).mpr ⟨P, hP, hPm⟩⟩

theorem sep_mono_right (P : MProp w) {Q Q' : MProp w} (h : Q ⊑ Q') : P ∗ Q ⊑ P ∗ Q' :=
  PreservesSup.map_mono (MProp.sep P) h

/-- The magic wand: the upper adjoint of `(P ∗ ·)`. `P -∗ Q` owns what,
joined with a disjoint `P`, yields `Q`. -/
noncomputable def wand (P Q : MProp w) : MProp w :=
  Lean.Order.PreservesSup.upperAdjoint (MProp.sep P) Q

@[inherit_doc wand] infixr:60 " -∗ " => MProp.wand

theorem wand_intro {P Q R : MProp w} (h : P ∗ Q ⊑ R) : Q ⊑ P -∗ R :=
  Lean.Order.PreservesSup.le_upperAdjoint (MProp.sep P) h

theorem sep_wand_elim (P Q : MProp w) : P ∗ (P -∗ Q) ⊑ Q :=
  Lean.Order.PreservesSup.upperAdjoint_le (MProp.sep P) Q

end MProp

/-! ## The atoms

`bs.AtM a` owns exactly the bytes `bs` at `a`, the assertion counterpart of
the memory `bs.At a`; `v.AtM a` owns a word, in the width of `v`. -/

/-- The bytes `bs` sit at `a`, and nothing else is owned. -/
def List.AtM {w : Nat} (bs : List UInt8) (a : BitVec w) : MProp w := Eq (bs.At a)

/-- The eight bytes of `v` sit at `a`. -/
abbrev UInt64.AtM {w : Nat} (v : UInt64) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The four bytes of `v` sit at `a`. -/
abbrev UInt32.AtM {w : Nat} (v : UInt32) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The two bytes of `v` sit at `a`. -/
abbrev UInt16.AtM {w : Nat} (v : UInt16) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The byte `v` sits at `a`. -/
abbrev UInt8.AtM {w : Nat} (v : UInt8) (a : BitVec w) : MProp w := v.toBytes.AtM a

/-- The offset of `addr` in the region of `L` bytes at `a₀` leaves room for
eight bytes, and the region fits the address space. -/
def MProp.SliceBound (L : List UInt8) (a₀ addr : BitVec 64) : Prop :=
  (addr - a₀).toNat + 8 ≤ L.length ∧ L.length ≤ 2 ^ 64

theorem MProp.SliceBound.intro {L : List UInt8} {a₀ addr : BitVec 64}
    (h8 : (addr - a₀).toNat + 8 ≤ L.length) (hL : L.length ≤ 2 ^ 64) :
    MProp.SliceBound L a₀ addr := ⟨h8, hL⟩

/-- A region holds a slot: the bytes at `a₀` split at the offset of `addr`
into the bytes before, the eight bytes at `addr`, and the bytes after. -/
theorem List.AtM_slice (L : List UInt8) (a₀ addr : BitVec 64)
    (hb : MProp.SliceBound L a₀ addr) :
    L.AtM a₀
      = (L.take (addr - a₀).toNat).AtM a₀
        ∗ (((L.drop (addr - a₀).toNat).take 8).AtM addr
          ∗ (L.drop ((addr - a₀).toNat + 8)).AtM (addr + 8#64)) := by
  obtain ⟨hk, hL⟩ := hb
  have h1 : L = L.take (addr - a₀).toNat ++ L.drop (addr - a₀).toNat :=
    (List.take_append_drop _ L).symm
  have h2 : L.drop (addr - a₀).toNat
      = (L.drop (addr - a₀).toNat).take 8 ++ L.drop ((addr - a₀).toNat + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have hlen1 : (L.take (addr - a₀).toNat).length = (addr - a₀).toNat := by
    rw [List.length_take]; omega
  have hlen2 : ((L.drop (addr - a₀).toNat).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  have e1 := Mem.At_append_sep (L.take (addr - a₀).toNat) (L.drop (addr - a₀).toNat) a₀
    (by rw [← List.length_append, ← h1]; exact hL)
  have e2 := Mem.At_append_sep ((L.drop (addr - a₀).toNat).take 8)
    (L.drop ((addr - a₀).toNat + 8)) addr
    (by rw [← List.length_append, ← h2, List.length_drop]; omega)
  rw [hlen1, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at e1
  rw [hlen2] at e2
  show Eq (L.At a₀) = Eq ((L.take (addr - a₀).toNat).At a₀)
    ⋆ (Eq (((L.drop (addr - a₀).toNat).take 8).At addr)
      ⋆ Eq ((L.drop ((addr - a₀).toNat + 8)).At (addr + 8#64)))
  rw [← e2, ← h2, ← e1, ← h1]

/-! ## The algebra for `ecancel`

`MProp.sepOps` registers the separation algebra of `MProp` with the
cancellation engine. Its normalizer brings register reads to `get64` reads
through the writes and word atoms to byte atoms, so the addresses of a
spec's footprint and of a precondition's atoms agree syntactically; its split
hook pays a footprint at an address inside a region by `List.AtM_slice`. -/

namespace MProp

open Lean Meta in
/-- Normalize the register reads of an address to `get64` reads through the
writes, and word atoms to byte atoms. -/
def normalizeAtoms (e : Expr) : MetaM (Expr × Option Expr) := do
  let mut thms ← ({} : SimpTheorems).addConst ``Reg64s.get64_set64
  thms ← thms.addConst ``eq_self_iff_true
  for n in [``UInt64.AtM, ``UInt32.AtM, ``UInt16.AtM, ``UInt8.AtM] do
    thms ← thms.addDeclToUnfold n
  for n in [``Reg64s.get64_r10, ``Reg64s.get64_r11, ``Reg64s.get64_r12, ``Reg64s.get64_r13, ``Reg64s.get64_r14, ``Reg64s.get64_r15, ``Reg64s.get64_r8, ``Reg64s.get64_r9, ``Reg64s.get64_rax, ``Reg64s.get64_rbp, ``Reg64s.get64_rbx, ``Reg64s.get64_rcx, ``Reg64s.get64_rdi, ``Reg64s.get64_rdx, ``Reg64s.get64_rsi, ``Reg64s.get64_rsp] do
    thms ← thms.addConst n (inv := true)
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
  let (r, _) ← Meta.simp e ctx (simprocs := #[← Simp.getSimprocs])
  return (r.expr, r.proof?)

open Lean Meta in
/-- Pay an address inside a region: split the region atom at the address by
`List.AtM_slice`, with the bound as the side goal. Stored values
(`Int.toBytes …`) are never split. -/
def splitAtom (atom addr : Expr) : MetaM (Option (Expr × Expr × MVarId)) := do
  unless atom.isAppOfArity ``List.AtM 3 do return none
  let L := atom.appFn!.appArg!
  if L.isAppOf ``Int.toBytes then return none
  let a₀ := atom.appArg!
  let hb ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``MProp.SliceBound #[L, a₀, addr])
  let heq ← mkAppM ``List.AtM_slice #[L, a₀, addr, hb]
  let some (_, _, sliced) := (← instantiateMVars (← inferType heq)).eq? | return none
  return some (sliced, heq, hb.mvarId!)

open Lean Meta in
def sepOps : Kraken.Tactic.SepOps where
  sep := ``MProp.sep
  emp := ``MProp.emp
  isCarrier := fun ty => pure (ty.isAppOfArity ``MProp 1)
  mkSep := fun predType p q => mkAppOptM ``MProp.sep #[predType.appArg!, p, q]
  mkEmp := fun predType => mkAppOptM ``MProp.emp #[predType.appArg!]
  normalize := normalizeAtoms
  split? := splitAtom
  addr? := fun e => if e.isAppOfArity ``List.AtM 3 then some e.appArg! else none

initialize Kraken.Tactic.sepOpsRef.modify (sepOps :: ·)

end MProp

/-! ## The frame operators

The frame is a pure memory assertion. It acts on an assertion of the program
logic pointwise through the state-passing layers, and on the exit channel
through one more layer; `FrameOp.pointwise` composes the `PreservesSup`
instances along the way. -/

namespace SepWP

/-- Frame a memory resource onto an assertion: `∗` under the register, vector
and flag layers. -/
def frameOp : MProp 64 → (Reg64s → RegZmms → StatusFlags → MProp 64)
    → Reg64s → RegZmms → StatusFlags → MProp 64 :=
  FrameOp.pointwise (FrameOp.pointwise (FrameOp.pointwise MProp.sep))

instance (F : MProp 64) : PreservesSup (frameOp F) :=
  inferInstanceAs (PreservesSup
    (FrameOp.pointwise (FrameOp.pointwise (FrameOp.pointwise MProp.sep)) F))

@[simp, grind =] theorem frameOp_apply (F : MProp 64)
    (P : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) : frameOp F P r z f = F ∗ P r z f := rfl

/-- The exit-channel companion: the same frame, at every exit address. -/
def frameOpE : MProp 64 → (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64)
    → Int64 → Reg64s → RegZmms → StatusFlags → MProp 64 :=
  FrameOp.pointwise frameOp

instance (F : MProp 64) : PreservesSup (frameOpE F) :=
  inferInstanceAs (PreservesSup (FrameOp.pointwise frameOp F))

@[simp, grind =] theorem frameOpE_apply (F : MProp 64)
    (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) (a : Int64) (r : Reg64s)
    (z : RegZmms) (f : StatusFlags) : frameOpE F E a r z f = F ∗ E a r z f := rfl

/-! ## The instance -/

/-- The machine-founded wp, read at the separation assertion language: the
memory is curried out of `MachineData`. -/
private def base [CodeEnv] :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  wpTrans q := ⟨fun Q E regs zmms flags mem =>
    cenv.wp q (fun s' => Q () s'.regs s'.zmms s'.status s'.dmem)
      (fun a s' => E a s'.regs s'.zmms s'.status s'.dmem)
      ⟨regs, zmms, flags, mem⟩⟩
  wp_trans_monotone q := by
    intro Q Q' E E' hE hQ regs zmms flags mem h
    exact Kraken.Executable.wp_mono (fun s' => hQ () s'.regs s'.zmms s'.status s'.dmem)
      (fun a s' => hE a s'.regs s'.zmms s'.status s'.dmem) h

/-- Triples of the separation examples: the frame rule internalized on both
channels over the machine-founded wp. -/
noncomputable scoped instance instWP [CodeEnv] :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :=
  WP.withFrameClosure frameOp base

/-- Prove a separation triple: the machine-founded wp validates it under an
arbitrary memory frame, held across the fall-through and across every exit. -/
theorem sep_intro [CodeEnv] {q : Program}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}
    (h : ∀ (F : MProp 64) (s : MachineData),
      (F ∗ P s.regs s.zmms s.status) s.dmem →
      cenv.wp q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status) s'.dmem)
        (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status) s'.dmem) s) :
    ⦃ P ⦄ q ⦃ Q; E ⦄ := by
  refine ⟨WP.le_wp_of_withFrameClosure_eq (base := base) rfl ?_⟩
  intro F regs zmms flags mem hpre
  exact h F ⟨regs, zmms, flags, mem⟩ hpre

/-- Consume a separation triple's wp under a frame: the machine-founded wp of
the framed pre- and postconditions follows, which is how a spec's proof enters
the wp of the tail. The dual of `sep_intro`. -/
theorem sep_elim [CodeEnv] {q : Program} {F : MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} {s : MachineData}
    (h : (F ∗ WP.wp (self := instWP) q Q E s.regs s.zmms s.status) s.dmem) :
    cenv.wp q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status) s'.dmem)
      (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status) s'.dmem) s := by
  have hle : frameOp F (WP.wp (self := instWP) q Q E)
      ⊑ base.wp q (fun a => frameOp F (Q a)) (frameOpE F E) := by
    refine PartialOrder.rel_trans
      (Lean.Order.PreservesSup.map_mono (frameOp F) (iInf_le _ F)) ?_
    exact Lean.Order.PreservesSup.upperAdjoint_le (frameOp F) _
  have := hle s.regs s.zmms s.status s.dmem h
  exact this

/-- Every program frames every memory assertion, on both channels: the
interpretation is a frame closure, and `∗` composes resources by `sep_assoc`.
This is the fact the frame inference of `vcgen` discharges per spec
application. -/
theorem frames [CodeEnv] (q : Program) (F : MProp 64) :
    @WP.Frames Program Unit _ _ _ _ instWP _ frameOp _ _ q F := by
  refine WP.frames_of_frameClosure frameOp MProp.sep ?_ ?_ ⟨fun q => (base.wpTrans q), fun _ => rfl⟩
  · intro r r' a
    funext regs zmms flags
    show (r ∗ r') ∗ a regs zmms flags = r ∗ (r' ∗ a regs zmms flags)
    exact MProp.sep_assoc r r' (a regs zmms flags)
  · intro r r' E
    funext a regs zmms flags
    show (r ∗ r') ∗ E a regs zmms flags = r ∗ (r' ∗ E a regs zmms flags)
    exact MProp.sep_assoc r r' (E a regs zmms flags)

/-- Triples of one directive: the interpretation of the singleton program. -/
noncomputable scoped instance [CodeEnv] :
    WP Directive Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  wpTrans d := WP.wpTrans (self := instWP) [d]
  wp_trans_monotone d := WP.wp_trans_monotone (self := instWP) [d]

theorem triple_directive [CodeEnv] {d : Directive}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    (⦃ P ⦄ d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- Chaining: a program runs its first directive with the wp of the rest as
the post. Every instruction spec is a triple of one directive; this rule is
where `vcgen` sequences them. -/
@[spec] theorem cons_spec [CodeEnv] (d : Directive) (p : Program)
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ := by
  refine sep_intro fun F s hpre => ?_
  have h1 := sep_elim (q := [d]) (Q := fun _ => WP.wp p Q E) hpre
  exact Kraken.Executable.wp_cons
    (Kraken.Executable.wp_mono (fun s' hs' => sep_elim (q := p) hs') (fun _ _ h => h) h1)

/-- The frame fact of one directive, spelled with the exception companion
`vcgen` derives for the exit channel. -/
@[grind .] theorem frames_directive [CodeEnv] (d : Directive) (F : MProp 64) :
    WP.Frames (Prog := Directive) frameOp d F :=
  ⟨(frames [d] F).op_wp_le_wp_op⟩

end SepWP

/-! ## Reading a triple back as the baseline judgment

A separation triple with no exits, whose precondition is a pure fact about
the registers next to a memory assertion and whose postcondition entails a
pure fact about the registers, is a run of the laid-out program: from any
state whose registers satisfy the fact and whose memory splits into the
assertion and a frame `R`, the run ends in a state whose registers satisfy
the post's fact. -/
open MachineWP in
theorem run_of_sep_triple [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)]
    {φ ψ : Reg64s → Prop} {P : Reg64s → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    (ht : (fun r _ _ => ⌜φ r⌝ ⊓ P r) ⊑ WP.wp (self := SepWP.instWP) p Q ⊥)
    (hψ : ∀ r z f, Q () r z f ⊑ ⌜ψ r⌝)
    {R : MProp 64} {s : MachineData} (hφ : φ s.regs) (hmem : s.dmem =⋆ P s.regs ⋆ R)
    {dlast : Directive}
    (henv : cenv = layout p := by rfl)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    Eventually (straightlineStep (layout p)) (fun st => ψ st.1.regs)
      (s, Kraken.Layout.start Directive) := by
  have hpre : (R ∗ (⌜φ s.regs⌝ ⊓ P s.regs)) s.dmem := by
    obtain ⟨m₁, m₂, hu, hd, hP, hR⟩ := hmem
    refine ⟨m₂, m₁, ?_, Std.ExtHashMap.disjoint_symm hd, hR,
      (MProp.meet_apply _ _ m₁).mpr ⟨(MProp.ofProp_apply_iff _ m₁).mpr hφ, hP⟩⟩
    rw [← hu]; exact (Std.ExtHashMap.union_comm_of_disjoint m₁ m₂ hd).symm
  refine Program.run_of_triple (P := fun s => (R ∗ (⌜φ s.regs⌝ ⊓ P s.regs)) s.dmem)
    (Q := fun _ s' => ψ s'.regs) ⟨fun s hs => ?_⟩ hpre henv hlast hd
  rw [MachineWP.wp_eq]
  have h := SepWP.sep_elim (q := p) (F := R) (Q := Q) (E := ⊥)
    (MProp.sep_mono_right R (ht s.regs s.zmms s.status) s.dmem hs)
  refine Kraken.Executable.wp_mono (fun s' hq => ?_) (fun a s' hE => ?_) h
  · exact MProp.sep_ofProp_elim (MProp.sep_mono_right R (hψ s'.regs s'.zmms s'.status) _ hq)
  · obtain ⟨_, m₂, _, _, _, hb⟩ := hE
    exact False.elim (bot_le (fun _ _ _ _ _ => False : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64)
      a s'.regs s'.zmms s'.status m₂ hb)

open MachineWP in
/-- `run_of_sep_triple` for a precondition with no pure part. -/
theorem run_of_sep_triple' [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)]
    {ψ : Reg64s → Prop} {P : Reg64s → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    (ht : (fun r _ _ => P r) ⊑ WP.wp (self := SepWP.instWP) p Q ⊥)
    (hψ : ∀ r z f, Q () r z f ⊑ ⌜ψ r⌝)
    {R : MProp 64} {s : MachineData} (hmem : s.dmem =⋆ P s.regs ⋆ R)
    {dlast : Directive}
    (henv : cenv = layout p := by rfl)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    Eventually (straightlineStep (layout p)) (fun st => ψ st.1.regs)
      (s, Kraken.Layout.start Directive) :=
  run_of_sep_triple (φ := fun _ => True)
    (fun r z f => PartialOrder.rel_trans (meet_le_right _ _) (ht r z f)) hψ trivial hmem henv hlast hd

section Smoke

open scoped SepWP

/-- The empty program preserves any memory assertion. -/
example [CodeEnv] {M : MProp 64} :
    ⦃ fun _ _ _ => M ⦄ ([] : Program)
    ⦃ fun _ _ _ _ => M; fun _ _ _ _ => (⊥ : MProp 64) ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc _
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-- A jump carries the memory assertion into the exit channel: the framed
exit is what the generalized closure buys. -/
example [CodeEnv] {M : MProp 64} :
    ⦃ fun _ _ _ => M ⦄
      ([Directive.instr (.regular .W64 .W64
          (.jmp (.rel (.sub (.label "out") .after_current_instruction))))] : Program)
    ⦃ fun _ _ _ _ => (⊥ : MProp 64);
      fun a _ _ _ => fun m => M m ∧ a = (_root_.Executable.labels cenv).label "out" ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, -⟩ := hpl
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  have hcancel : pc + Int64.ofNat z
      + ((_root_.Executable.labels cenv).label "out" - (pc + Int64.ofNat z))
      = (_root_.Executable.labels cenv).label "out" := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [hcancel]
  refine Eventually.done _ (Or.inr ?_)
  obtain ⟨m₁, m₂, hu, hd, hF, hM⟩ := hpre
  exact ⟨m₁, m₂, hu, hd, hF, hM, rfl⟩

end Smoke
