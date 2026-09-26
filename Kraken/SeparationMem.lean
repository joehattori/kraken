import Kraken.Mem
import Kraken.Separation

/-!
# Separation-logic interface to Kraken memory-access operations
-/

open Std
open Std.ExtHashMap
open List

private theorem Std.ExtHashMap.get_union_l_disjoint {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 : ExtHashMap key value) (k : key) (v : value) (h_disj : m1.inter m2 = ∅) (h : m1.get? k = some v) :
    (m1.union m2).get? k = some v := by
  rw [get?_eq_getElem?] at h
  rw [get?_eq_getElem?, union_comm_of_disjoint m1 m2 h_disj]
  simp only [union_eq, getElem?_union, h, Option.some_or]

private theorem Std.ExtHashMap.union_union_override {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 m3 : ExtHashMap key value) (h_sub : ∀ k, k ∈ m1 → k ∈ m3) :
    (m1.union m2).union m3 = m2.union m3 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union]
  cases h3 : m3[k]?
  · have h_not_mem3 : ¬ k ∈ m3 := by
      intro h_mem
      have h_some := getElem?_eq_some_getElem h_mem
      rw [h3] at h_some
      contradiction
    have h_not_mem1 : ¬ k ∈ m1 := fun h => h_not_mem3 (h_sub k h)
    have h1 := getElem?_eq_none h_not_mem1
    rw [h1]
    cases h2 : m2[k]?
    · rfl
    · rfl
  · rfl

private theorem List.range_get_eq_map_some {α : Type} (l : List α) :
    (List.range l.length).map (fun i => if h : i < l.length then some (l.get ⟨i, h⟩) else none) = l.map some := by
  apply List.ext_get <;> simp

private theorem mem_At_samerange {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (h_len : _bs.length = bs.length) (k : BitVec w) :
    (k ∈ bs.At a) = (k ∈ _bs.At a) := by
  exact propext (by simp [mem_At_iff, h_len])

private theorem disjoint_Atsame_l_same_r {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (m2 : Mem w)
    (h_disj : (_bs.At a).inter m2 = ∅) (h_len : _bs.length = bs.length) :
    (bs.At a).inter m2 = ∅ := by
  simpa [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff,
    mem_At_samerange _bs bs a h_len] using h_disj

namespace Mem

theorem loadBytes_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadBytes a n = some bs := by
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  rw [← h_union]
  have h_get : ∀ i (h : i < n), ((bs.At a).union m2).get? (a + BitVec.ofNat w i) = some (bs.get ⟨i, Hl ▸ h⟩) := by
    intro i hi
    apply get_union_l_disjoint
    · exact h_inter
    · rw [get?_At_idx _ _ _ (by omega) (Hl.symm ▸ Hlw)]
      exact getElem?_eq_getElem (Hl ▸ hi)
  rw [Mem.loadBytes]
  rw [show (List.range n).map (fun i => ((bs.At a).union m2).get? (a + BitVec.ofNat w i)) =
           (List.range n).map (fun i => if h : i < n then some (bs.get ⟨i, Hl ▸ h⟩) else none) by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; rw [dif_pos hi]; exact h_get i hi]
  cases Hl
  rw [List.range_get_eq_map_some]
  rw [List.allSome_map_some]

theorem storeBytes_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n ∧ bs.length = n) :
    (m.storeBytes a bs) =⋆ Eq (bs.At a) ⋆ R := by
  have ⟨Hsep, h_len1, h_len2⟩ := H
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  dsimp [storeBytes]
  rw [← h_union]
  rw [union_union_override (_bs.At a) m2 (bs.At a) (by
    intro k hk; rw [mem_At_samerange _bs bs a (by omega)]; exact hk)]
  rw [sep_comm]
  exact ⟨m2, bs.At a, rfl, disjoint_symm (disjoint_Atsame_l_same_r _bs bs a m2 h_inter (by omega)), hR, rfl⟩

theorem loadInt_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  simp [loadInt, loadBytes_sep bs a n R m Hsep Hl Hlw]

theorem storeInt_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ Eq ((Int.toBytes n v).At a) ⋆ R := by
  simpa only [storeInt] using
    storeBytes_sep a n _bs (Int.toBytes n v) R m ⟨H.1, H.2, Int.toBytes_length n v⟩

theorem At_append_sep {w : Nat} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    Eq ((bs1 ++ bs2).At a) = Eq (bs1.At a) ⋆ Eq (bs2.At (a + .ofNat _ bs1.length)) := by
  funext m
  apply propext
  constructor
  · rintro rfl
    rw [List.At_append _ _ _ h_len]
    exact ⟨bs1.At a, bs2.At (a + BitVec.ofNat w bs1.length), rfl, List.disjoint_At_append _ _ _ h_len, rfl, rfl⟩
  · rintro ⟨m1, m2, h_union, h_disj, rfl, rfl⟩
    rw [← h_union]
    rw [← List.At_append _ _ _ h_len]

/-! ## Slices of a region

An access of `n` bytes at `addr` inside a region `bs.At a` touches the bytes at
offset `(addr - a).toNat`. The region splits around them, which reduces the
access to `loadInt_sep` or `storeInt_sep` with the rest of the region in the
frame. -/

/-- A region in three parts, split with the middle part first. -/
theorem At_append3_sep {w : Nat} (pre mid post : List UInt8) (a : BitVec w)
    (hlen : pre.length + mid.length + post.length ≤ 2 ^ w) :
    Eq ((pre ++ mid ++ post).At a)
      = Eq (mid.At (a + .ofNat w pre.length))
        ⋆ (Eq (pre.At a) ⋆ Eq (post.At (a + .ofNat w (pre.length + mid.length)))) := by
  rw [At_append_sep (pre ++ mid) post a (by simp; omega),
    At_append_sep pre mid a (by omega), sep_assoc, sep_comm_l]
  simp only [List.length_append]

private theorem add_ofNat_toNat_sub {w : Nat} (a addr : BitVec w) :
    a + BitVec.ofNat w (addr - a).toNat = addr := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- A region split around the `n` bytes at `addr` inside it: those bytes first,
then the bytes before and after them. -/
theorem At_slice_sep {w : Nat} (bs : List UInt8) (a addr : BitVec w) (n : Nat)
    (hin : (addr - a).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    Eq (bs.At a)
      = Eq (((bs.drop (addr - a).toNat).take n).At addr)
        ⋆ (Eq ((bs.take (addr - a).toNat).At a)
          ⋆ Eq ((bs.drop ((addr - a).toNat + n)).At (addr + .ofNat w n))) := by
  have hsplit : bs = bs.take (addr - a).toNat ++ (bs.drop (addr - a).toNat).take n
      ++ bs.drop ((addr - a).toNat + n) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  conv => lhs; rw [hsplit]
  rw [At_append3_sep _ _ _ a (by simp only [List.length_take, List.length_drop]; omega), h1, h2,
    add_ofNat_toNat_sub, BitVec.ofNat_add, ← BitVec.add_assoc, add_ofNat_toNat_sub]

/-- A load inside a region reads the region's bytes there. -/
theorem loadInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) :
    m.loadInt addr n = some (Int.ofBytes ((bs.drop (addr - a).toNat).take n)) := by
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  exact loadInt_sep _ addr n _ m h (by simp only [List.length_take, List.length_drop]; omega)
    (by omega)

/-- A store inside a region writes its bytes into the region, which keeps its
length. -/
theorem storeInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) (v : Int) :
    m.storeInt addr n v =⋆
      Eq ((bs.take (addr - a).toNat ++ Int.toBytes n v ++ bs.drop ((addr - a).toNat + n)).At a)
        ⋆ F := by
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  have hst := storeInt_sep addr n _ _ m ⟨h, h2⟩ v
  rw [At_append3_sep _ _ _ a
      (by simp only [List.length_take, List.length_drop, Int.toBytes_length]; omega),
    sep_assoc, h1, Int.toBytes_length, add_ofNat_toNat_sub, BitVec.ofNat_add,
    ← BitVec.add_assoc, add_ofNat_toNat_sub]
  exact hst

/-! ## Blocks: owned regions with untracked contents

A program that moves data around without inspecting it (a copy, an in-place
update) needs to know which regions it owns, not what they hold. `Block a len`
owns the `len` bytes at `a`, whatever they are, and `Blocks` lists several,
separated from each other. A load or store inside a listed block is safe and
keeps the list, so an invariant says `s.dmem =⋆ Mem.Blocks [...] ⋆ R` and needs
nothing else about memory.

The load and store lemmas fire in `grind` on such a fact and an access.
Their side condition `Blocks.Inside` has one introduction rule per usual
address shape: the block's base, the base plus an offset, and the base plus
two offsets (a pointer into the block plus an index). `grind` applies a rule
only when the address is computed from that block's base, so it never has to
rule out the other blocks. -/

/-- An owned region of `len` bytes at `a`, whose contents are not tracked. -/
def Block {w : Nat} (a : BitVec w) (len : Nat) (h : Mem w) : Prop :=
  len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ bs.At a = h

/-- A block is a region with some contents of its length. -/
theorem Block.sep_elim {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Block a len ⋆ F) :
    len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ m =⋆ Eq (bs.At a) ⋆ F := by
  obtain ⟨m1, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩ := h
  exact ⟨hw, bs, hlen, _, m2, hu, hi, rfl, hF⟩

/-- A region is a block of its length, forgetting the contents. -/
theorem Block.sep_intro {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    {bs : List UInt8} (hlen : bs.length = len) (hw : len ≤ 2 ^ w)
    (h : m =⋆ Eq (bs.At a) ⋆ F) : m =⋆ Block a len ⋆ F := by
  obtain ⟨m1, m2, hu, hi, rfl, hF⟩ := h
  exact ⟨_, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩

/-- A load inside a block succeeds. -/
theorem Block.loadInt_isSome {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) :
    (m.loadInt addr n).isSome = true := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  rw [loadInt_slice h' hin hw]
  rfl

/-- A store inside a block keeps the block. -/
theorem Block.storeInt {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) (v : Int) :
    m.storeInt addr n v =⋆ Block a len ⋆ F := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  exact Block.sep_intro
    (by simp only [List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
        omega)
    hw (storeInt_slice h' hin hw v)

/-- Blocks separated from each other, as `(base, length)` pairs:
`Blocks [(a₁, l₁), (a₂, l₂)]` is `Block a₁ l₁ ⋆ Block a₂ l₂`. -/
def Blocks {w : Nat} : List (BitVec w × Nat) → Mem w → Prop
  | [] => emp
  | [(a, len)] => Block a len
  | (a, len) :: b :: bs => Block a len ⋆ Blocks (b :: bs)

/-- The `n` bytes at `addr` lie inside one of the blocks. -/
def Blocks.Inside {w : Nat} (addr : BitVec w) (n : Nat) : List (BitVec w × Nat) → Prop
  | [] => False
  | (a, len) :: bs => (addr - a).toNat + n ≤ len ∨ Blocks.Inside addr n bs

/-- An access inside a later block is inside the list. -/
theorem Blocks.Inside.tail {w : Nat} {addr : BitVec w} {n : Nat} {p : BitVec w × Nat}
    {bs : List (BitVec w × Nat)} (h : Blocks.Inside addr n bs) :
    Blocks.Inside addr n (p :: bs) := by
  obtain ⟨a, len⟩ := p
  exact Or.inr h

/-- An access at a block's base. -/
theorem Blocks.Inside.base {w : Nat} {a : BitVec w} {n len : Nat} {bs : List (BitVec w × Nat)}
    (h : n ≤ len) : Blocks.Inside a n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- An access at an offset `x` from a block's base. -/
theorem Blocks.Inside.base_add {w : Nat} {a x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : x.toNat + n ≤ len) :
    Blocks.Inside (a + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

/-- An access at two offsets `c` and `x` from a block's base, such as a pointer
into the block plus an index. -/
theorem Blocks.Inside.base_add_add {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x).toNat + n ≤ len) :
    Blocks.Inside (a + c + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

/-- A load inside one of the blocks succeeds. -/
theorem Blocks.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h hin
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h' hin
      · rw [sep_comm_l] at h'
        exact ih h' hin

/-- A store inside one of the blocks keeps all of them. -/
theorem Blocks.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) (v : Int) :
    m.storeInt addr n v =⋆ Blocks bs ⋆ F := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.storeInt h hin v
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      show (Block a len ⋆ Blocks (q :: bs) ⋆ F) (m.storeInt addr n v)
      rw [sep_assoc]
      rcases hin with hin | hin
      · exact Block.storeInt h' hin v
      · rw [sep_comm_l] at h' ⊢
        exact ih h' hin

grind_pattern Blocks.Inside.tail => Blocks.Inside addr n (p :: bs)
grind_pattern Blocks.Inside.base => Blocks.Inside a n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add => Blocks.Inside (a + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_add => Blocks.Inside (a + c + x) n ((a, len) :: bs)
grind_pattern Blocks.loadInt_isSome => sep (Blocks bs) F m, Mem.loadInt m addr n
grind_pattern Blocks.storeInt => sep (Blocks bs) F m, Mem.storeInt m addr n v

end Mem
