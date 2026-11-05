module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
public import Kraken.X64.Art.StringEquals

open Std
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/-- Extract the list of UTF-16 code units from the string payload. -/
@[expose] def strChars (count : BitVec 32) (data : List UInt8) : List (BitVec 16) :=
  (List.range (count >>> 1).toNat).map (fun i =>
    if count.getLsbD 0 then
      (data.getD (2 * i) 0).toBitVec.zeroExtend 16 ||| ((data.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)
    else
      (data.getD i 0).toBitVec.zeroExtend 16)

/-- Java `String.indexOf(ch, fromIndex)` specification for BMP code points (`ch ≤ 0xFFFF`). -/
@[expose] def indexOfSpec (chars : List (BitVec 16)) (ch fromIndex : BitVec 32) : BitVec 32 :=
  let start := if fromIndex.slt 0 then 0 else fromIndex.toNat
  match (chars.drop start).findIdx? (fun c => c.zeroExtend 32 = ch) with
  | some i => BitVec.ofNat 32 (start + i)
  | none   => -1#32

/--
Specification postcondition on final state `t`:
- `out` contains `indexOfSpec chars ch fromIndex`.
- registers not in `out :: temps` are preserved from `s`.
- `dmem` is unchanged.
- `zmms` is either unchanged (`s.zmms`), or zeroUpper after vector writes.
-/
@[expose] def StringIndexOfPost (out : Reg64) (temps : List Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32) (s t : MachineData) : Prop :=
  let res : BitVec 32 := indexOfSpec chars ch fromIndex
  (t.regs.get (.low out .W32) = res) ∧
  (∀ r, r ∉ out :: temps → t.regs.get64 r = s.regs.get64 r) ∧
  t.dmem = s.dmem ∧
  (t.zmms = s.zmms ∨
   ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)

/-- Slow-path postcondition when `ch > 0xFFFF`: jumps to `slow` with unchanged state. -/
@[expose] def StringIndexOfSlow [Host] (slow : Label) (ch : BitVec 32) (s₀ : MachineData)
    (pc : Int64) (s : MachineData) : Prop :=
  pc = label slow ∧ ch.toNat > 0xFFFF ∧ s.regs = s₀.regs ∧ s.dmem = s₀.dmem ∧ s.zmms = s₀.zmms

/-- A label outside the embedding range. -/
@[expose] def IsSlowPathLabel [Host] (p : _root_.Program) (H : Embedding p) (slow : Label) : Prop :=
  ¬(label slow = H.endAddr ∨ p.IsLabelAddr (label slow) ∨
    (∃ i < p.length, label slow = Host.addrOf (H.start + i)))

theorem findIdx?_go_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) (i : Nat) :
    List.findIdx?.go p (x :: xs) i = if p x then some i else List.findIdx?.go p xs (i + 1) := by
  conv => lhs; rw [List.findIdx?.go]

theorem findIdx?_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    List.findIdx? p (x :: xs) = if p x then some 0 else (List.findIdx? p xs).map (· + 1) := by
  unfold List.findIdx?
  rw [findIdx?_go_cons]
  split
  · rfl
  · have hgo : ∀ (ys : List α) (n : Nat), List.findIdx?.go p ys (n + 1) = (List.findIdx?.go p ys n).map (· + 1) := by
      intro ys
      induction ys with
      | nil => intro n; rfl
      | cons y yys ih =>
        intro n
        rw [findIdx?_go_cons, findIdx?_go_cons]
        split
        · rfl
        · rw [ih (n + 1), ih n]
    exact hgo xs 0

theorem findIdx?_eq_some {α : Type} (p : α → Bool) (l : List α) (j : Nat)
    (hj : j < l.length) (h_match : p (l.get ⟨j, hj⟩) = true)
    (h_first : ∀ (i : Nat) (hi : i < j), p (l.get ⟨i, by omega⟩) = false) :
    l.findIdx? p = some j := by
  induction l generalizing j with
  | nil => contradiction
  | cons x xs ih =>
    rw [findIdx?_cons]
    by_cases hj0 : j = 0
    · subst hj0
      simpa using h_match
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hx : p x = false := by
        have := h_first 0 (by omega)
        simpa using this
      simp only [hx]
      have hj' : j' < xs.length := by simpa using hj
      have h_match' : p (xs.get ⟨j', hj'⟩) = true := by
        simpa using h_match
      have h_first' : ∀ (i : Nat) (hi : i < j'), p (xs.get ⟨i, by omega⟩) = false := by
        intro i hi
        have := h_first (i + 1) (by omega)
        simpa using this
      have := ih j' hj' h_match' h_first'
      rw [this]; rfl

theorem findIdx?_eq_none {α : Type} (p : α → Bool) (l : List α)
    (h_none : ∀ (i : Nat) (hi : i < l.length), p (l.get ⟨i, hi⟩) = false) :
    l.findIdx? p = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [findIdx?_cons]
    have hx : p x = false := by
      have := h_none 0 (by simp)
      simpa using this
    simp only [hx]
    have ih' := ih (fun i hi => by
      have := h_none (i + 1) (by simp; omega)
      simpa using this)
    rw [ih']; rfl

theorem indexOfSpec_eq_some {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (j : Nat) (hj : j < (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).length)
    (h_match : ((chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨j, hj⟩).zeroExtend 32 = ch)
    (h_first : ∀ (i : Nat) (hi : i < j),
      ((chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨i, by omega⟩).zeroExtend 32 ≠ ch) :
    indexOfSpec chars ch fromIndex = BitVec.ofNat 32 ((if fromIndex.slt 0 then 0 else fromIndex.toNat) + j) := by
  dsimp only [indexOfSpec]
  have := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
    (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)) j hj
    (by simp only [decide_eq_true_iff, h_match])
    (by intro i hi; simp only [decide_eq_false_iff_not]; exact h_first i hi)
  rw [this]

theorem indexOfSpec_eq_none {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (h_none : ∀ (i : Nat) (hi : i < (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).length),
      ((chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨i, hi⟩).zeroExtend 32 ≠ ch) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  dsimp only [indexOfSpec]
  have := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
    (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat))
    (by intro i hi; simp only [decide_eq_false_iff_not]; exact h_none i hi)
  rw [this]

theorem indexOfSpec_empty (ch fromIndex : BitVec 32) :
    indexOfSpec [] ch fromIndex = -1#32 := by
  dsimp only [indexOfSpec]
  simp

theorem indexOfSpec_ge {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (h_ge : chars.length ≤ (if fromIndex.slt 0 then 0 else fromIndex.toNat)) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  dsimp only [indexOfSpec]
  rw [List.drop_of_length_le h_ge]
  rfl

theorem indexOfSpec_compressed_gt127 {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (h_ascii : ∀ c ∈ chars, c.toNat < 128)
    (h_ch : ch.toNat > 127) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  apply indexOfSpec_eq_none
  intro i hi
  have h_in : (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨i, hi⟩ ∈ chars := by
    have := List.get_mem (chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)) ⟨i, hi⟩
    exact List.mem_of_mem_drop this
  have h_lt := h_ascii _ h_in
  intro heq
  have h_toNat := congrArg BitVec.toNat heq
  change (BitVec.setWidth 32 _).toNat = ch.toNat at h_toNat
  rw [BitVec.toNat_setWidth] at h_toNat
  have h_c_lt : ((chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨i, hi⟩).toNat < 2 ^ 32 := by
    have := ((chars.drop (if fromIndex.slt 0 then 0 else fromIndex.toNat)).get ⟨i, hi⟩).isLt
    omega
  rw [Nat.mod_eq_of_lt h_c_lt] at h_toNat
  omega

theorem byte_eq_iff (b : BitVec 8) (ch : BitVec 32) (h_ch : ch.toNat ≤ 127) :
    ((b.zeroExtend 16).zeroExtend 32 = ch) ↔ (b = ch.setWidth 8) := by
  constructor
  · intro h; subst h; bv_decide
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    change (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.setWidth 8 ch))).toNat = ch.toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have h8 : ch.toNat < 2 ^ 8 := by omega
    have h16 : ch.toNat < 2 ^ 16 := by omega
    have h32 : ch.toNat < 2 ^ 32 := ch.isLt
    rw [Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h32]

theorem word_eq_iff (w : BitVec 16) (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535) :
    (w.zeroExtend 32 = ch) ↔ (w = ch.setWidth 16) := by
  constructor
  · intro h; subst h; bv_decide
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    change (BitVec.setWidth 32 (BitVec.setWidth 16 ch)).toNat = ch.toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have h16 : ch.toNat < 2 ^ 16 := by omega
    have h32 : ch.toNat < 2 ^ 32 := ch.isLt
    rw [Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h32]

theorem pos_of_comp (c : BitVec 32) (h1 : c ≠ 0#32) (h2 : c.getLsbD 0 = false) :
    0 < (c >>> 1).toNat := by
  have : c >>> 1 ≠ 0#32 := by bv_decide
  apply Nat.pos_of_ne_zero
  intro h
  apply this
  apply BitVec.eq_of_toNat_eq
  simp [h]

theorem strChars_length (count : BitVec 32) (data : List UInt8) :
    (strChars count data).length = (count >>> 1).toNat := by
  simp [strChars]

theorem get_map_range {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (hi : i < n) :
    ((List.range n).map f).get ⟨i, by simp; exact hi⟩ = f i := by
  simp

theorem strChars_compressed_get {c : BitVec 32} {d : List UInt8}
    (h_comp : c.getLsbD 0 = false) (i : Nat) (hi : i < (c >>> 1).toNat) :
    (strChars c d).get ⟨i, by rw [strChars_length]; exact hi⟩ = (d.getD i 0).toBitVec.zeroExtend 16 := by
  change ((List.range (c >>> 1).toNat).map _).get ⟨i, by simp; exact hi⟩ = _
  rw [get_map_range (hi := hi)]
  rw [h_comp]
  rfl

theorem strChars_uncompressed_get {c : BitVec 32} {d : List UInt8}
    (h_uncomp : c.getLsbD 0 = true) (i : Nat) (hi : i < (c >>> 1).toNat) :
    (strChars c d).get ⟨i, by rw [strChars_length]; exact hi⟩ =
      (d.getD (2 * i) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
  change ((List.range (c >>> 1).toNat).map _).get ⟨i, by simp; exact hi⟩ = _
  rw [get_map_range (hi := hi)]
  rw [h_uncomp]
  rfl

theorem strChars_compressed_ascii {c : BitVec 32} {d : List UInt8}
    (h_comp : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (h_ascii : ∀ b ∈ d, b < 128) :
    ∀ c_char ∈ strChars c d, c_char.toNat < 128 := by
  intro c_char hc_char
  unfold strChars at hc_char
  simp only [List.mem_map, List.mem_range] at hc_char
  obtain ⟨i, hi, rfl⟩ := hc_char
  rw [h_comp]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hlen : strByteLen c = (c >>> 1).toNat := by
    unfold strByteLen; rw [h_comp]; rfl
  have hi_d : i < d.length := by rw [hl, hlen]; exact hi
  have hd_eq : d.getD i 0 = d[i] := by
    unfold List.getD; rw [List.getElem?_eq_getElem hi_d]; rfl
  have hd_in : d[i] ∈ d := List.getElem_mem hi_d
  have hb_lt := h_ascii d[i] hd_in
  have : (d.getD i 0).toNat < 128 := by rw [hd_eq]; exact hb_lt
  change ((d.getD i 0).toBitVec.zeroExtend 16).toNat < 128
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact this

theorem jg_ch127_true {ch : BitVec 32} (h1 : 127 < ch.toNat) (h2 : ch.toNat ≤ 65535) :
    let v := ch - 127#32
    let of := v.signed != ch.signed - (127#32).signed
    let sf := v.msb
    let zf := v == 0#32
    (!zf && (sf == of)) = true := by
  have h_toNat : (ch - 127#32).toNat = ch.toNat - 127 := by
    rw [BitVec.toNat_sub]
    have : (127#32).toNat = 127 := rfl
    rw [this]
    have h_mod : (2 ^ 32 - 127 + ch.toNat) % 2 ^ 32 = ch.toNat - 127 := by
      have : 2 ^ 32 - 127 + ch.toNat = (ch.toNat - 127) + 2 ^ 32 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt]
      have := ch.isLt; omega
    simp only [h_mod]
  have h_ch_lt : 2 * ch.toNat < 2 ^ 32 := by omega
  have h_v_signed : (ch - 127#32).signed = (ch.toNat - 127 : Int) := by
    unfold BitVec.signed BitVec.toInt
    rw [h_toNat]
    split <;> omega
  have h_ch_signed : ch.signed = (ch.toNat : Int) := by
    unfold BitVec.signed BitVec.toInt
    simp only [h_ch_lt, ↓reduceIte]
  have h_127_signed : (127#32).signed = 127 := rfl
  have h_of : ((ch - 127#32).signed != ch.signed - (127#32).signed) = false := by
    rw [bne_eq_false_iff_eq, h_v_signed, h_ch_signed, h_127_signed]
  have h_sf : (ch - 127#32).msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]
    rw [h_toNat]; omega
  have h_zf : (ch - 127#32 == 0#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    rw [h_toNat] at this
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
    omega
  dsimp only
  rw [h_zf, h_sf, h_of]
  rfl

theorem jg_ch127_false {ch : BitVec 32} (h1 : ch.toNat ≤ 127) :
    let v := ch - 127#32
    let of := v.signed != ch.signed - (127#32).signed
    let sf := v.msb
    let zf := v == 0#32
    (!zf && (sf == of)) = false := by
  by_cases heq : ch.toNat = 127
  · have hch : ch = 127#32 := by
      apply BitVec.eq_of_toNat_eq; simp [heq]
    dsimp only
    rw [hch]
    decide
  · have hlt : ch.toNat < 127 := by omega
    have h_toNat : (ch - 127#32).toNat = 2 ^ 32 - 127 + ch.toNat := by
      rw [BitVec.toNat_sub]
      have : (127#32).toNat = 127 := rfl
      rw [this, Nat.mod_eq_of_lt]
      have := ch.isLt; omega
    have h_v_ge : 2 ^ 31 ≤ (ch - 127#32).toNat := by
      rw [h_toNat]; omega
    have h_sf : (ch - 127#32).msb = true := by
      rw [BitVec.msb_eq_decide, decide_eq_true_iff]
      exact h_v_ge
    have h_v_signed : (ch - 127#32).signed = (ch.toNat : Int) - 127 := by
      unfold BitVec.signed BitVec.toInt
      rw [h_toNat]
      split <;> omega
    have h_ch_lt : 2 * ch.toNat < 2 ^ 32 := by omega
    have h_ch_signed : ch.signed = (ch.toNat : Int) := by
      unfold BitVec.signed BitVec.toInt
      simp only [h_ch_lt, ↓reduceIte]
    have h_127_signed : (127#32).signed = 127 := rfl
    have h_of : ((ch - 127#32).signed != ch.signed - (127#32).signed) = false := by
      rw [bne_eq_false_iff_eq, h_v_signed, h_ch_signed, h_127_signed]
    dsimp only
    rw [h_sf, h_of]
    simp

theorem rax_w8_eq (s : MachineData) (ch : BitVec 32) (hch : s.regs.get (Reg.low .rax .W32) = ch) :
    s.regs.get (Reg.low .rax .W8) = ch.setWidth 8 := by
  have h : ∀ x : BitVec 64,
      BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 64 x) =
        BitVec.setWidth 8 (BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 64 x)) := by
    intro x; bv_decide
  have : Width.W8.bits = 8 := rfl
  have : Width.W32.bits = 32 := rfl
  simp only [Reg64s.get, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop] at hch ⊢
  rw [← hch]
  exact h _

theorem rax_w16_eq (s : MachineData) (ch : BitVec 32) (hch : s.regs.get (Reg.low .rax .W32) = ch) :
    s.regs.get (Reg.low .rax .W16) = ch.setWidth 16 := by
  have h : ∀ x : BitVec 64,
      BitVec.extractLsb' 0 16 (BitVec.extractLsb' 0 64 x) =
        BitVec.setWidth 16 (BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 64 x)) := by
    intro x; bv_decide
  have : Width.W16.bits = 16 := rfl
  have : Width.W32.bits = 32 := rfl
  simp only [Reg64s.get, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop] at hch ⊢
  rw [← hch]
  exact h _

theorem rax_w32_eq (s : MachineData) (ch : BitVec 32) (hch : s.regs.get (Reg.low .rax .W32) = ch) :
    BitVec.setWidth 32 (s.regs.get64 Reg64.rax) = ch := by
  have h : ∀ x : BitVec 64,
      BitVec.setWidth 32 x = BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 64 x) := by
    intro x; bv_decide
  have : Width.W32.bits = 32 := rfl
  simp only [Reg64s.get, Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop] at hch
  rw [← hch]
  have : 64 - 0 = 64 := rfl
  rw [this]
  exact h _

theorem len_eval_eq (c : BitVec 32) :
    ((BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64 c)).ushiftRight 1)).setWidth 32 : BitVec 32) = BitVec.ofNat 32 (c >>> 1).toNat := by
  have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
  rw [BitVec.ofNat_toNat]
  bv_decide

theorem len_eval_simple (c : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (c.ushiftRight 1)) = BitVec.ofNat 32 (c >>> 1).toNat := by
  have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
  rw [BitVec.ofNat_toNat]
  bv_decide

theorem rcx_eval_eq (c : BitVec 32) :
    (BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64 c)).ushiftRight 1)) = BitVec.ofNat 64 (c >>> 1).toNat := by
  have : (c >>> 1).toNat < 2 ^ 64 := by
    have := (c >>> 1).isLt; omega
  rw [BitVec.ofNat_toNat]
  bv_decide

theorem shift_right_lt (c : BitVec 32) : (c >>> 1).toNat < 2 ^ 32 - 1 := by
  rw [BitVec.toNat_ushiftRight]
  have := c.isLt
  omega

theorem toNat_sub_of_ge {w : Nat} (a b : BitVec w) (h : a.toNat ≥ b.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have : 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt]
  have := a.isLt; omega

theorem toNat_sub_of_lt {w : Nat} (a b : BitVec w) (h : a.toNat < b.toNat) :
    (a - b).toNat = 2 ^ w - (b.toNat - a.toNat) := by
  rw [BitVec.toNat_sub]
  have : 2 ^ w - b.toNat + a.toNat = 2 ^ w - (b.toNat - a.toNat) := by omega
  rw [this, Nat.mod_eq_of_lt]
  have := b.isLt; omega

theorem jge_implies_ge (a b : BitVec 32) (hb : b.toNat < 2 ^ 31)
    (h_ge :
      let v := a - b
      let of := v.toInt != a.toInt - b.toInt
      let sf := v.msb
      (sf == of) = true) :
    b.toNat ≤ (if a.slt 0 then 0 else a.toNat) := by
  dsimp only at h_ge
  by_cases ha_lt : a.toNat < 2 ^ 31
  · have ha_int : a.toInt = (a.toNat : Int) := by
      unfold BitVec.toInt
      have : 2 * a.toNat < 2 ^ 32 := by omega
      simp [this]
    have ha_slt : a.slt 0 = false := by
      simp [BitVec.slt, ha_int]
    rw [ha_slt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h_ge_nat : a.toNat ≥ b.toNat
    · omega
    · have h_lt_nat : a.toNat < b.toNat := by omega
      have hb_int : b.toInt = (b.toNat : Int) := by
        unfold BitVec.toInt
        have : 2 * b.toNat < 2 ^ 32 := by omega
        simp [this]
      have hv_toNat : (a - b).toNat = 2 ^ 32 - (b.toNat - a.toNat) := toNat_sub_of_lt a b h_lt_nat
      have hv_int : (a - b).toInt = (a.toNat : Int) - (b.toNat : Int) := by
        unfold BitVec.toInt
        rw [hv_toNat]
        split <;> omega
      have h_of : ((a - b).toInt != a.toInt - b.toInt) = false := by
        rw [bne_eq_false_iff_eq, hv_int, ha_int, hb_int]
      have hv_sf : (a - b).msb = true := by
        rw [BitVec.msb_eq_decide, decide_eq_true_iff, hv_toNat]
        omega
      rw [hv_sf, h_of] at h_ge
      have : (true == false) = false := rfl
      rw [this] at h_ge
      contradiction
  · have ha_ge : a.toNat ≥ 2 ^ 31 := by omega
    have ha_int : a.toInt = (a.toNat : Int) - 2 ^ 32 := by
      unfold BitVec.toInt
      have : ¬ (2 * a.toNat < 2 ^ 32) := by
        have := a.isLt; omega
      simp [this]
    have ha_slt : a.slt 0 = true := by
      simp [BitVec.slt, ha_int]
      have := a.isLt; omega
    rw [ha_slt]
    simp only [↓reduceIte]
    by_cases hb0 : b.toNat = 0
    · omega
    · exfalso
      have hb_int : b.toInt = (b.toNat : Int) := by
        unfold BitVec.toInt
        have : 2 * b.toNat < 2 ^ 32 := by omega
        simp [this]
      have h_ge_nat : a.toNat ≥ b.toNat := by omega
      have hv_toNat : (a - b).toNat = a.toNat - b.toNat := toNat_sub_of_ge a b h_ge_nat
      by_cases hv_lt : (a - b).toNat < 2 ^ 31
      · have hv_int : (a - b).toInt = ((a - b).toNat : Int) := by
          unfold BitVec.toInt
          split <;> omega
        have h_of : ((a - b).toInt != a.toInt - b.toInt) = true := by
          rw [bne_iff_ne]
          intro h
          rw [hv_int, hv_toNat, ha_int, hb_int] at h
          have := a.isLt; omega
        have hv_sf : (a - b).msb = false := by
          rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]
          omega
        rw [hv_sf, h_of] at h_ge
        have : (false == true) = false := rfl
        rw [this] at h_ge
        contradiction
      · have hv_ge' : (a - b).toNat ≥ 2 ^ 31 := by omega
        have hv_int : (a - b).toInt = (a.toNat : Int) - (b.toNat : Int) - 2 ^ 32 := by
          unfold BitVec.toInt
          rw [hv_toNat]
          split <;> omega
        have h_of : ((a - b).toInt != a.toInt - b.toInt) = false := by
          rw [bne_eq_false_iff_eq, hv_int, ha_int, hb_int]
          omega
        have hv_sf : (a - b).msb = true := by
          rw [BitVec.msb_eq_decide, decide_eq_true_iff]
          exact hv_ge'
        rw [hv_sf, h_of] at h_ge
        have : (true == false) = false := rfl
        rw [this] at h_ge
        contradiction

theorem not_jge_implies_lt (a b : BitVec 32) (hb_pos : 0 < b.toNat) (hb : b.toNat < 2 ^ 31)
    (h_not_ge :
      let v := a - b
      let of := v.toInt != a.toInt - b.toInt
      let sf := v.msb
      (sf == of) = false) :
    (if a.slt 0 then 0 else a.toNat) < b.toNat := by
  dsimp only at h_not_ge
  by_cases ha_lt : a.toNat < 2 ^ 31
  · have ha_int : a.toInt = (a.toNat : Int) := by
      unfold BitVec.toInt
      split <;> omega
    have ha_slt : a.slt 0 = false := by
      simp [BitVec.slt, ha_int]
    rw [ha_slt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h_ge_nat : a.toNat ≥ b.toNat
    · exfalso
      have hb_int : b.toInt = (b.toNat : Int) := by
        unfold BitVec.toInt
        split <;> omega
      have hv_toNat : (a - b).toNat = a.toNat - b.toNat := toNat_sub_of_ge a b h_ge_nat
      have hv_int : (a - b).toInt = ((a - b).toNat : Int) := by
        unfold BitVec.toInt
        split <;> omega
      have h_of : ((a - b).toInt != a.toInt - b.toInt) = false := by
        rw [bne_eq_false_iff_eq, hv_int, hv_toNat, ha_int, hb_int]
        omega
      have hv_sf : (a - b).msb = false := by
        rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, hv_toNat]
        omega
      rw [hv_sf, h_of] at h_not_ge
      have : (false == false) = true := rfl
      rw [this] at h_not_ge
      contradiction
    · omega
  · have ha_ge : a.toNat ≥ 2 ^ 31 := by omega
    have ha_int : a.toInt = (a.toNat : Int) - 2 ^ 32 := by
      unfold BitVec.toInt
      split <;> omega
    have ha_slt : a.slt 0 = true := by
      simp [BitVec.slt, ha_int]
      have := a.isLt; omega
    rw [ha_slt]
    simp only [↓reduceIte]
    exact hb_pos

theorem cmovg_zero_eval (start_val : BitVec 32) :
    let v := start_val - 0#32
    let of := v.toInt != start_val.toInt - (0#32).toInt
    let sf := v.msb
    let zf := v == 0#32
    let cond := !zf && (sf == of)
    (if cond then start_val else 0#32) = (if start_val.slt 0 then 0#32 else start_val) := by
  dsimp only
  have hof : ((start_val - 0#32).toInt != start_val.toInt - (0#32).toInt) = false := by
    simp
  rw [hof]
  bv_decide

theorem setWidth64_cmovg (start_val : BitVec 32) :
    (BitVec.setWidth 64 (if start_val.slt 0 then 0#32 else start_val)) =
      BitVec.ofNat 64 (if start_val.slt 0 then 0 else start_val.toNat) := by
  split
  · rfl
  · simp

theorem cmovg_start_idx_eval (start_val : BitVec 32) :
    let v := start_val - 0#32
    let of := v.toInt != start_val.toInt - (0#32).toInt
    let sf := v.msb
    let zf := v == 0#32
    let cond := !zf && (sf == of)
    (BitVec.setWidth 64 (if cond then start_val else 0#32)) =
      BitVec.ofNat 64 (if start_val.slt 0 then 0 else start_val.toNat) := by
  dsimp only
  rw [cmovg_zero_eval, setWidth64_cmovg]

theorem ofNat_sub_eq (A B : Nat) (hBA : B ≤ A) (hA : A < 2 ^ 64) :
    BitVec.ofNat 64 A - BitVec.ofNat 64 B = BitVec.ofNat 64 (A - B) := by
  apply BitVec.eq_of_toNat_eq
  have hA_nat : (BitVec.ofNat 64 A).toNat = A := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
  have hB_nat : (BitVec.ofNat 64 B).toNat = B := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hge : (BitVec.ofNat 64 A).toNat ≥ (BitVec.ofNat 64 B).toNat := by
    rw [hA_nat, hB_nat]; exact hBA
  rw [toNat_sub_of_ge (BitVec.ofNat 64 A) (BitVec.ofNat 64 B) hge]
  rw [hA_nat, hB_nat]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem addr_sib2_disp [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W16⟩, disp := .int64 d } regs p).zeroExtend 64 =
      regs.get64 r + BitVec.ofInt 64 ((regs.get64 i).signed * 2) + d.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Width.bits, Width.bytes]
  rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.extractLsb'_eq_self, BitVec.ofInt_toInt,
    ← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  simp

theorem addr_sib2_disp' [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W16⟩, disp := .int64 d } regs p : BitVec 64) =
      regs.get64 r + BitVec.ofInt 64 ((regs.get64 i).signed * 2) + d.toBitVec := by
  have := addr_sib2_disp regs r i d p
  simpa using this

theorem ofInt_signed_mul2 (x : BitVec 64) :
    BitVec.ofInt 64 (x.signed * 2) = x * 2#64 := by
  change BitVec.ofInt 64 (x.toInt * 2) = x * 2#64
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rfl

theorem ofNat_mul2 (n : Nat) :
    BitVec.ofNat 64 n * 2#64 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem rcx_zero_of_len_zero (fromIndex : BitVec 32)
    (hnot_ge : ((fromIndex - 0#32).msb == ((fromIndex - 0#32).signed != fromIndex.signed - (0#32).signed)) = false) :
    let v := fromIndex - 0#32
    let of := v.toInt != fromIndex.toInt - (0#32).toInt
    let sf := v.msb
    let zf := v == 0#32
    let cond := !zf && (sf == of)
    (if cond then fromIndex else 0#32) = 0#32 := by
  dsimp only
  have hof : ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) = false := by simp
  have h_eq : ((fromIndex - 0#32).signed != fromIndex.signed - (0#32).signed) = false := by
    change ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) = false
    exact hof
  rw [h_eq] at hnot_ge
  rw [hof]
  have hsf : (fromIndex - 0#32).msb = true := by
    revert hnot_ge
    bv_decide
  rw [hsf]
  bv_decide

end

end Kraken.X64.Art
