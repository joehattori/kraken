/-
Partial evaluation of the layout. `Executable.addrOf` names the address of
the directive at an index; `Executable.label_addrOf` computes a label's
address and `Executable.directivesFromAddress_addrOf` cuts the directive list
at an index whose address is fresh, so one `simp` with these two equations
rewrites a straightline judgment's segment into a literal directive list.
`Executable.ValidLayout` packages the facts that make the addresses
well-behaved: labels occupy no bytes, every other directive occupies at least
one, and the program fits in the address space; `addrOf_ne_of_valid`
discharges the freshness hypothesis at any index that follows a non-label
directive.
-/
import Kraken.Blocks

namespace Kraken.Executable

/-- Bytes occupied by the first `n` directives. -/
def sizeBefore (e : Kraken.Executable Directive) (n : Nat) : Nat := ((e.2.take n).map (·.2)).sum

/-- The address of the directive at index `n`. -/
def addrOf (e : Kraken.Executable Directive) (n : Nat) : Int64 := e.1 + .ofNat (e.sizeBefore n)

@[simp] theorem addrOf_zero (e : Kraken.Executable Directive) : e.addrOf 0 = e.1 := by
  simp [addrOf, sizeBefore]

private theorem int64_ofNat_add (a b : Nat) :
    Int64.ofNat (a + b) = Int64.ofNat a + Int64.ofNat b := by
  apply Int64.toBitVec_inj.mp
  simp

/-- The entry of `withAddresses` at an index: the directive there, at the sum
of the sizes before it. -/
private theorem getElem?_withAddresses_pair :
    ∀ (ds : List (Directive × Nat)) (a : Int64) (k : Nat),
      (Kraken.Executable.withAddresses (a, ds))[k]?
        = ds[k]?.map (fun dz => (a + .ofNat ((ds.take k).map (·.2)).sum, dz.1, dz.2))
  | [], a, k => by rw [Kraken.Executable.withAddresses]; simp
  | (d, z) :: ds, a, 0 => by
    rw [Kraken.Executable.withAddresses]
    simp
  | (d, z) :: ds, a, k + 1 => by
    rw [Kraken.Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_pair ds _ k,
      List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [int64_ofNat_add, ← Int64.add_assoc]

private theorem getElem?_withAddresses (e : Kraken.Executable Directive) (k : Nat) (hk : k < e.2.length) :
    e.withAddresses[k]?.map (·.1) = some (e.addrOf k) := by
  show (Kraken.Executable.withAddresses (e.1, e.2))[k]?.map (·.1) = some (e.addrOf k)
  rw [getElem?_withAddresses_pair]
  obtain ⟨dz, hdz⟩ : ∃ dz, e.2[k]? = some dz :=
    ⟨_, List.getElem?_eq_getElem hk⟩
  rw [hdz]
  simp [addrOf, sizeBefore]

private theorem idxOf_eq_of {α} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    ∀ {n : Nat}, l[n]? = some a → (∀ k, k < n → l[k]? ≠ some a) → l.idxOf a = n := by
  induction l with
  | nil => intro n hn _; simp at hn
  | cons x xs ih =>
    intro n hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn; simp
    | succ m =>
      have hx : (x == a) = false := by
        have h0 := hlt 0 (Nat.succ_pos m)
        simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq] at h0
        simpa using h0
      simp only [List.idxOf_cons, hx]
      rw [ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]
      simp

/-- `dropWhile` drops a prefix: some position `j` has the tail from `j` on,
every element before `j` satisfying the predicate and, when an element sits at
`j`, that element failing it. -/
private theorem dropWhile_stops {α} {p : α → Bool} {l : List α} :
    ∃ j, l.dropWhile p = l.drop j
      ∧ (∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
        ∧ (∀ c, l[j]? = some c → p c = false) := by
  induction l with
  | nil => exact ⟨0, by simp, fun k hk c hc => by simp at hc, fun c hc => by simp at hc⟩
  | cons x xs ih =>
    by_cases hx : p x
    · obtain ⟨j, hdrop, hprior, hhead⟩ := ih
      refine ⟨j + 1, ?_, ?_, ?_⟩
      · rw [List.dropWhile_cons, if_pos hx, List.drop_succ_cons]
        exact hdrop
      · intro k hk c hc
        cases k with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hc; exact hc ▸ hx
        | succ m => exact hprior m (by omega) c (by simpa using hc)
      · intro c hc
        exact hhead c (by simpa using hc)
    · exact ⟨0, by rw [List.dropWhile_cons, if_neg hx, List.drop_zero],
        fun k hk c hc => by omega,
        fun c hc => by
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc; simpa using hx⟩

/-- `dropWhile` cuts at position `j` when every earlier element satisfies the
predicate and the element there fails it. -/
private theorem dropWhile_eq_drop_of {α} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  induction l generalizing j with
  | nil => simp
  | cons x xs ih =>
    cases j with
    | zero =>
      have hx := hhead x rfl
      rw [List.dropWhile_cons, if_neg (by simp [hx]), List.drop_zero]
    | succ m =>
      have hx := hprior 0 (Nat.succ_pos m) x rfl
      rw [List.dropWhile_cons, if_pos (by simp [hx]), List.drop_succ_cons]
      exact ih (fun k hk c hc => hprior (k+1) (by omega) c (by simpa using hc))
        (fun c hc => hhead c (by simpa using hc))

/-- `withAddresses` of a suffix, spelled from position `j`. -/
private theorem withAddresses_drop :
    ∀ (ds : List (Directive × Nat)) (a : Int64) (j : Nat), j ≤ ds.length →
      (Kraken.Executable.withAddresses (a, ds)).drop j
        = Kraken.Executable.withAddresses
            (a + .ofNat (((ds.take j).map (·.2)).sum), ds.drop j)
  | ds, a, 0, _ => by simp
  | ds, a, j + 1, h => by
    match ds, h with
    | (d, z) :: ds, h =>
      rw [Kraken.Executable.withAddresses]
      simp only [List.drop_succ_cons,
        withAddresses_drop ds (a + .ofNat z) j (by simpa using h),
        List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [int64_ofNat_add, ← Int64.add_assoc]

/-- The snd projection of `withAddresses` is the directive list. -/
private theorem withAddresses_map_snd' :
    ∀ (ds : List (Directive × Nat)) (a : Int64),
      (Kraken.Executable.withAddresses (a, ds)).map (·.2) = ds
  | [], a => by rw [Kraken.Executable.withAddresses]; rfl
  | (d, z) :: ds, a => by
    rw [Kraken.Executable.withAddresses]
    simp [withAddresses_map_snd' ds]

/-- Cutting the directive list at an address: the segment at the address of
directive `n` is the directive list from the first index `j` that sits at
this address. -/
theorem directivesFromAddress_addrOf_first (e : Kraken.Executable Directive) (j n : Nat)
    (hjn : j ≤ n) (hn : n ≤ e.2.length) (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop j := by
  show ((Kraken.Executable.withAddresses (e.1, e.2)).dropWhile
      (·.1 ≠ e.addrOf n)).map (·.2) = e.2.drop j
  have hlen : (Kraken.Executable.withAddresses (e.1, e.2)).length = e.2.length := by
    conv => lhs; rw [show (Kraken.Executable.withAddresses (e.1, e.2)).length
      = ((Kraken.Executable.withAddresses (e.1, e.2)).map (·.2)).length by simp]
    rw [withAddresses_map_snd' e.2 e.1]
  have hdw : (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ e.addrOf n)
      = (Kraken.Executable.withAddresses (e.1, e.2)).drop j := by
    apply dropWhile_eq_drop_of
    · intro k hk c hc
      have hklt : k < e.2.length := by
        have hbound : k < (Kraken.Executable.withAddresses (e.1, e.2)).length := by
          by_cases h : k < (Kraken.Executable.withAddresses (e.1, e.2)).length
          · exact h
          · rw [List.getElem?_eq_none (by omega)] at hc; cases hc
        omega
      have := getElem?_withAddresses e k hklt
      rw [hc] at this
      simp only [Option.map_some, Option.some.injEq] at this
      have hne : c.1 ≠ e.addrOf n := this ▸ hfresh k hk
      simpa using hne
    · intro c hc
      have hjlt : j < e.2.length := by
        have hbound : j < (Kraken.Executable.withAddresses (e.1, e.2)).length := by
          by_cases h : j < (Kraken.Executable.withAddresses (e.1, e.2)).length
          · exact h
          · rw [List.getElem?_eq_none (by omega)] at hc; cases hc
        omega
      have := getElem?_withAddresses e j hjlt
      rw [hc] at this
      simp only [Option.map_some, Option.some.injEq] at this
      have heq : c.1 = e.addrOf n := this ▸ hj
      simpa using heq
  rw [hdw, List.map_drop, withAddresses_map_snd' e.2 e.1]

/-- Cutting the directive list at an index whose address is fresh: the
segment at the address of directive `n` is the directive list from `n` on. -/
theorem directivesFromAddress_addrOf (e : Kraken.Executable Directive) (n : Nat) (hn : n ≤ e.2.length)
    (hfresh : ∀ k, k < n → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.2.drop n :=
  directivesFromAddress_addrOf_first e n n (Nat.le_refl n) hn rfl hfresh

private theorem findSome?_eq_of {α β} {f : α → Option β} {l : List α} :
    ∀ {n : Nat} {b : β}, l[n]?.bind f = some b →
      (∀ k, k < n → l[k]?.bind f = none) → l.findSome? f = some b := by
  induction l with
  | nil => intro n b hn _; simp at hn
  | cons x xs ih =>
    intro n b hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.bind_some] at hn
      simp [hn]
    | succ m =>
      have h0 : f x = none := by simpa using hlt 0 (Nat.succ_pos m)
      rw [List.findSome?_cons, h0,
        ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]

/-- The address of a label: the address of the index holding its first
occurrence, provided the label occupies no bytes there. -/
theorem label_addrOf (e : Kraken.Executable Directive) (l : Label) (n : Nat)
    (hn : e.2[n]? = some (.label l, 0))
    (hfirst : ∀ dz ∈ e.2.take n, dz.1 ≠ Directive.label l) :
    (_root_.Executable.labels e).label l = e.addrOf n := by
  replace hfirst : ∀ k, k < n → e.2[k]?.map (·.1) ≠ some (Directive.label l) := by
    intro k hk hcontra
    obtain ⟨dz, hdz⟩ : ∃ dz, e.2[k]? = some dz := by
      rcases h : e.2[k]? with _ | dz
      · rw [h] at hcontra; simp at hcontra
      · exact ⟨dz, rfl⟩
    rw [hdz] at hcontra
    refine hfirst dz (List.mem_iff_getElem?.mpr ⟨k, ?_⟩) (by simpa using hcontra)
    rw [List.getElem?_take_of_lt hk, hdz]
  have hstep : e.1 + .ofNat ((e.2.take (n + 1)).map (·.2)).sum = e.addrOf n := by
    unfold addrOf sizeBefore
    rw [List.take_add_one, hn]
    simp
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n) ?hit ?miss]
  · exact rfl
  case hit =>
    show ((Kraken.Executable.withAddresses (e.1, e.2))[n]?.bind _) = some (e.addrOf n)
    rw [getElem?_withAddresses_pair, hn]
    show some (e.addrOf n, Directive.label l, 0) >>= _ = some (e.addrOf n)
    simp
  case miss =>
    intro k hk
    show ((Kraken.Executable.withAddresses (e.1, e.2))[k]?.bind _) = none
    rw [getElem?_withAddresses_pair]
    rcases hm : e.2[k]? with _ | ⟨d, z⟩
    · simp
    · have hd : d ≠ .label l := by
        have := hfirst k hk
        rw [hm] at this
        simpa using this
      simp [hd]

/-! ## Valid layouts -/

/-- The facts about a laid-out executable that keep its addresses
well-behaved: labels occupy no bytes, every other directive occupies at least
one, and the program fits in the address space. Distinct cut points that
follow a non-label directive then sit at distinct addresses
(`addrOf_ne_of_valid`). -/
class ValidLayout (e : Kraken.Executable Directive) : Prop where
  label_size : ∀ (i : Nat) l z, e.2[i]? = some (Directive.label l, z) → z = 0
  instr_size : ∀ (i : Nat) d z, e.2[i]? = some (d, z) → (∀ l, d ≠ Directive.label l) → 0 < z
  no_wrap : (e.2.map (·.2)).sum < 2 ^ 64

private theorem sum_map_take_le {α} (f : α → Nat) (l : List α) (k : Nat) :
    ((l.take k).map f).sum ≤ (l.map f).sum := by
  conv => rhs; rw [← List.take_append_drop k l]
  simp only [List.map_append, List.sum_append]
  omega

private theorem sizeBefore_le_sum (e : Kraken.Executable Directive) (n : Nat) :
    e.sizeBefore n ≤ (e.2.map (·.2)).sum :=
  sum_map_take_le _ e.2 n

private theorem sizeBefore_mono (e : Kraken.Executable Directive) {k n : Nat} (h : k ≤ n) :
    e.sizeBefore k ≤ e.sizeBefore n := by
  unfold sizeBefore
  rw [show e.2.take k = (e.2.take n).take k by rw [List.take_take, Nat.min_eq_left h]]
  exact sum_map_take_le _ _ k

private theorem sizeBefore_succ (e : Kraken.Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) :
    e.sizeBefore (n + 1) = e.sizeBefore n + z := by
  unfold sizeBefore
  rw [List.take_add_one, hd]
  simp

/-- Stepping one directive advances the address by that directive's size. -/
theorem addrOf_succ (e : Kraken.Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) : e.addrOf (n + 1) = e.addrOf n + .ofNat z := by
  unfold addrOf
  rw [sizeBefore_succ e hd, int64_ofNat_add, Int64.add_assoc]

/-- A nonempty segment starts at a position, and the segment is the text from
that position on. -/
theorem exists_pos_of_directivesFromAddress (e : Kraken.Executable Directive) {a : Int64}
    (h : e.directivesFromAddress a ≠ []) :
    ∃ k, k < e.2.length ∧ e.addrOf k = a ∧ e.directivesFromAddress a = e.2.drop k := by
  -- the dropWhile stops somewhere inside the list; that position is the start
  obtain ⟨j, hjdrop, hjprior⟩ := dropWhile_stops
      (p := fun c : Int64 × Directive × Nat => c.1 ≠ a)
      (l := Kraken.Executable.withAddresses (e.1, e.2))
  have hlen : (Kraken.Executable.withAddresses (e.1, e.2)).length = e.2.length := by
    conv => lhs; rw [show (Kraken.Executable.withAddresses (e.1, e.2)).length
      = ((Kraken.Executable.withAddresses (e.1, e.2)).map (·.2)).length by simp]
    rw [withAddresses_map_snd' e.2 e.1]
  have hseg : e.directivesFromAddress a = e.2.drop j := by
    show ((Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ a)).map (·.2)
      = e.2.drop j
    rw [hjdrop, List.map_drop, withAddresses_map_snd' e.2 e.1]
  have hjlt : j < e.2.length := by
    by_cases hlt : j < e.2.length
    · exact hlt
    · rw [hseg, List.drop_eq_nil_of_le (by omega)] at h
      exact absurd rfl h
  refine ⟨j, hjlt, ?_, hseg⟩
  -- the entry at the stop satisfies the stop condition: its address is `a`
  obtain ⟨c, hc⟩ : ∃ c, (Kraken.Executable.withAddresses (e.1, e.2))[j]? = some c :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hstop := hjprior.2 c hc
  have := getElem?_withAddresses e j hjlt
  rw [hc] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [← this]
  simpa using hstop

/-- Coincident addresses have equal byte counts: the total byte count fits
the address space, so `Int64.ofNat` acts injectively on the counts. -/
theorem sizeBefore_eq_of_addrOf_eq (e : Kraken.Executable Directive) [hv : ValidLayout e] {k n : Nat}
    (heq : e.addrOf k = e.addrOf n) : e.sizeBefore k = e.sizeBefore n := by
  have hbk : e.sizeBefore k < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (sizeBefore_le_sum e k) hv.no_wrap
  have hbn : e.sizeBefore n < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (sizeBefore_le_sum e n) hv.no_wrap
  have hbv : BitVec.ofNat 64 (e.sizeBefore k) = BitVec.ofNat 64 (e.sizeBefore n) := by
    have h4 := congrArg Int64.toBitVec heq
    simp only [addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
    exact (BitVec.add_right_inj _).mp h4
  have hnat := congrArg BitVec.toNat hbv
  simp only [BitVec.toNat_ofNat] at hnat
  omega

/-- Distinct addresses at a cut point that follows a non-label directive. -/
theorem addrOf_ne_of_valid (e : Kraken.Executable Directive) [hv : ValidLayout e] {k n : Nat}
    (hk : k < n) (hsome : (e.2[n - 1]?).isSome)
    (hd : ∀ l z, e.2[n - 1]? ≠ some (Directive.label l, z)) :
    e.addrOf k ≠ e.addrOf n := by
  obtain ⟨⟨d, z⟩, hdz⟩ := Option.isSome_iff_exists.mp hsome
  have hz : 0 < z := hv.instr_size _ _ _ hdz (fun l hl => hd l z (by rw [hdz, hl]))
  have h1 : e.sizeBefore k ≤ e.sizeBefore (n - 1) := sizeBefore_mono e (by omega)
  have h2 : e.sizeBefore n = e.sizeBefore (n - 1) + z := by
    have hs := sizeBefore_succ e hdz
    rw [show n - 1 + 1 = n by omega] at hs
    exact hs
  intro heq
  have h3 := sizeBefore_eq_of_addrOf_eq e heq
  omega

/-- The least index that satisfies a predicate, at or below a witness. -/
theorem _root_.Nat.exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hPm⟩ := hb
      obtain ⟨j, hj, hPj, hmin⟩ := ih m hm hPm
      exact ⟨j, by omega, hPj, hmin⟩
    · exact ⟨n, Nat.le_refl n, h, fun k hk hPk => hb ⟨k, hk, hPk⟩⟩

/-- Between two cut points with one address every directive is a label: a
non-label directive occupies at least one byte and separates the addresses. -/
theorem label_between_of_addrOf_eq (e : Kraken.Executable Directive) [hv : ValidLayout e] {j k n : Nat}
    (hjk : j ≤ k) (hkn : k < n) (hn : n ≤ e.2.length)
    (heq : e.addrOf j = e.addrOf n) :
    ∃ l z, e.2[k]? = some (Directive.label l, z) := by
  obtain ⟨⟨d, z⟩, hdz⟩ : ∃ dz, e.2[k]? = some dz :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  cases d with
  | label l => exact ⟨l, z, hdz⟩
  | instr i | byteArray a =>
    exfalso
    have hz : 0 < z := hv.instr_size _ _ _ hdz (fun l h => Directive.noConfusion h)
    have h1 : e.sizeBefore j ≤ e.sizeBefore k := sizeBefore_mono e hjk
    have h2 : e.sizeBefore (k + 1) = e.sizeBefore k + z := sizeBefore_succ e hdz
    have h3 : e.sizeBefore (k + 1) ≤ e.sizeBefore n := sizeBefore_mono e hkn
    have h4 := sizeBefore_eq_of_addrOf_eq e heq
    omega

/-- The cut point of the address of index `n`: the segment there starts at
the least index `j` with that address, and every directive from `j` up to `n` is a
label. -/
theorem exists_cut (e : Kraken.Executable Directive) [ValidLayout e] {n : Nat} (hn : n ≤ e.2.length) :
    ∃ j, j ≤ n ∧ e.directivesFromAddress (e.addrOf n) = e.2.drop j
      ∧ ∀ m, j ≤ m → m < n → ∃ l z, e.2[m]? = some (Directive.label l, z) := by
  obtain ⟨j, hjn, hj, hmin⟩ :=
    Nat.exists_least_le (P := fun k => e.addrOf k = e.addrOf n) rfl
  exact ⟨j, hjn, directivesFromAddress_addrOf_first e j n hjn hn hj hmin,
    fun m hjm hmn => label_between_of_addrOf_eq e hjm hmn hn hj⟩

end Kraken.Executable

/-- The start address a layout gives a program. -/
theorem _root_.Layout.apply_fst [layout : Layout] (p : Program) :
    (layout p).1 = layout.start := rfl

/-- The directive list a layout gives a program is that program laid out from
position zero. -/
theorem _root_.Layout.apply_snd [layout : Layout] (p : Program) :
    (layout p).2 = Layout.frag 0 p := by simp [Layout.frag, Kraken.Layout.apply]
