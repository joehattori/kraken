module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
public import Kraken.X64.Art.StringEquals
public import Kraken.X64.Art.StringIndexOfSpec

@[expose] public def RegZmms.setAll (zmms : RegZmms) :
    List (AvxReg .W256) → List (BitVec 256) → RegZmms
  | r :: rs, v :: vs => (zmms.set r v).setAll rs vs
  | _, _ => zmms

namespace Kraken.X64.Art

public section

/-- Java `String.compareTo` on UTF-16 code units: the difference of the first
    differing chars, else the difference of the lengths. -/
@[expose] def compareToSpec : List (BitVec 16) → List (BitVec 16) → BitVec 32
  | x :: xs, y :: ys =>
    if x = y then compareToSpec xs ys else x.zeroExtend 32 - y.zeroExtend 32
  | xs, ys => BitVec.ofInt 32 ((xs.length : Int) - ys.length)

/--
`out` holds the result on all 64 bits. Registers outside `out :: temps` and memory are
kept; zmms are kept, or the ymm temps are written and then zeroUpper. Flags are free.
-/
@[expose] def StringCompareToPost (out : Reg64) (temps : List Reg64) (ymms : List (AvxReg .W256))
    (a b : List (BitVec 16)) (s t : MachineData) : Prop :=
  t.regs.get64 out = (compareToSpec a b).zeroExtend 64 ∧
  (∀ r, r ∉ out :: temps → t.regs.get64 r = s.regs.get64 r) ∧
  t.dmem = s.dmem ∧
  (t.zmms = s.zmms ∨ ∃ vs, t.zmms = (s.zmms.setAll ymms vs).zeroUpper)

/-- Null `arg`: exit through `slow` with registers, memory and zmms as at entry. -/
@[expose] def StringCompareToSlow [Host] (slow : Label) (arg : Reg64) (s₀ : MachineData)
    (pc : Int64) (t : MachineData) : Prop :=
  pc = label slow ∧ s₀.regs.get64 arg = 0#64 ∧
  t.regs = s₀.regs ∧ t.dmem = s₀.dmem ∧ t.zmms = s₀.zmms

/-! ## `RegZmms.setAll` and `compareToSpec` helper lemmas -/

theorem zmms_post_singleton {zmms : RegZmms} {s : MachineData} {ymm : AvxReg .W256}
    (h : zmms = s.zmms ∨ ∃ v, zmms = (s.zmms.set ymm v).zeroUpper) :
    zmms = s.zmms ∨ ∃ vs, zmms = (s.zmms.setAll [ymm] vs).zeroUpper :=
  match h with
  | .inl heq => .inl heq
  | .inr ⟨v, hv⟩ => .inr ⟨[v], hv⟩

theorem compareToSpec_nil_left (b : List (BitVec 16)) :
    compareToSpec [] b = BitVec.ofInt 32 (-(b.length : Int)) := by
  cases b <;> simp [compareToSpec]

theorem compareToSpec_nil_right (a : List (BitVec 16)) :
    compareToSpec a [] = BitVec.ofInt 32 (a.length : Int) := by
  cases a <;> simp [compareToSpec]

theorem compareToSpec_self (a : List (BitVec 16)) :
    compareToSpec a a = 0#32 := by
  induction a with
  | nil => simp [compareToSpec]
  | cons x xs ih => simp [compareToSpec, ih]

theorem compareToSpec_drop {a b : List (BitVec 16)} :
    ∀ {k : Nat} (hka : k ≤ a.length) (hkb : k ≤ b.length),
      (∀ (i : Nat) (hi : i < k),
        a[i]'(Nat.lt_of_lt_of_le hi hka) = b[i]'(Nat.lt_of_lt_of_le hi hkb)) →
      compareToSpec a b = compareToSpec (a.drop k) (b.drop k) := by
  induction a generalizing b with
  | nil =>
    intro k hka hkb heq
    have hk : k = 0 := by simp at hka; omega
    subst hk; rfl
  | cons x xs ih =>
    intro k hka hkb heq
    cases k with
    | zero => rfl
    | succ k' =>
      cases b with
      | nil => simp at hkb
      | cons y ys =>
        have hxy : x = y := by
          have := heq 0 (Nat.zero_lt_succ k')
          simpa using this
        subst hxy
        simp only [compareToSpec, ↓reduceIte, List.drop_succ_cons]
        apply ih (by simpa using hka) (by simpa using hkb)
        intro i hi
        have := heq (i + 1) (Nat.succ_lt_succ hi)
        simpa using this

theorem compareToSpec_prefix {a b : List (BitVec 16)}
    (heq : ∀ (i : Nat) (h1 : i < a.length) (h2 : i < b.length), a[i] = b[i]) :
    compareToSpec a b = BitVec.ofInt 32 ((a.length : Int) - b.length) := by
  let k := min a.length b.length
  have hka : k ≤ a.length := Nat.min_le_left _ _
  have hkb : k ≤ b.length := Nat.min_le_right _ _
  rw [compareToSpec_drop hka hkb (fun i hi =>
    heq i (Nat.lt_of_lt_of_le hi hka) (Nat.lt_of_lt_of_le hi hkb))]
  by_cases hlen : a.length ≤ b.length
  · have hk : k = a.length := Nat.min_eq_left hlen
    have ha : a.drop k = [] := List.drop_of_length_le (by omega)
    have hbl : (b.drop k).length = b.length - a.length := by rw [List.length_drop, hk]
    rw [ha, compareToSpec_nil_left, hbl]
    congr 1; omega
  · have hlen' : b.length ≤ a.length := by omega
    have hk : k = b.length := Nat.min_eq_right hlen'
    have hb : b.drop k = [] := List.drop_of_length_le (by omega)
    have hal : (a.drop k).length = a.length - b.length := by rw [List.length_drop, hk]
    rw [hb, compareToSpec_nil_right, hal]
    congr 1; omega

theorem compareToSpec_diff {a b : List (BitVec 16)} {k : Nat}
    (hka : k < a.length) (hkb : k < b.length)
    (heq : ∀ (i : Nat) (hi : i < k),
      a[i]'(Nat.lt_trans hi hka) = b[i]'(Nat.lt_trans hi hkb))
    (hne : a[k] ≠ b[k]) :
    compareToSpec a b = a[k].zeroExtend 32 - b[k].zeroExtend 32 := by
  rw [compareToSpec_drop (Nat.le_of_lt hka) (Nat.le_of_lt hkb) heq]
  rw [List.drop_eq_getElem_cons hka, List.drop_eq_getElem_cons hkb]
  simp [compareToSpec, hne]

theorem compareToSpec_diff_neg (x y : BitVec 16) :
    x.zeroExtend 32 - y.zeroExtend 32 = -(y.zeroExtend 32 - x.zeroExtend 32) := by
  rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.add_comm]

/-! ## String length, byte-to-char, and arithmetic helpers -/

theorem strByteLen_compressed {c : BitVec 32} (h : c.getLsbD 0 = false) :
    strByteLen c = (c >>> 1).toNat := by
  unfold strByteLen
  have h0 : c[0] = false := h
  simp [h0]

theorem strByteLen_uncompressed {c : BitVec 32} (h : c.getLsbD 0 = true) :
    strByteLen c = 2 * (c >>> 1).toNat := by
  unfold strByteLen
  have h0 : c[0] = true := h
  simp [h0]

theorem ushiftRight1_lt (c : BitVec 32) : (c >>> 1).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := c.isLt
  omega

theorem sub_ofNat32_eq_ofInt_diff (m n : Nat) :
    BitVec.ofNat 32 m - BitVec.ofNat 32 n = BitVec.ofInt 32 ((m : Int) - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem sub_len_eq_compareToSpec_prefix (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8) :
    (c₁ >>> 1) - (c₂ >>> 1) =
      BitVec.ofInt 32 (((strChars c₁ d₁).length : Int) - (strChars c₂ d₂).length) := by
  have h1lt : (c₁ >>> 1).toNat < 2 ^ 32 := Nat.lt_trans (ushiftRight1_lt c₁) (by decide)
  have h2lt : (c₂ >>> 1).toNat < 2 ^ 32 := Nat.lt_trans (ushiftRight1_lt c₂) (by decide)
  have h₁ : BitVec.ofNat 32 (c₁ >>> 1).toNat = c₁ >>> 1 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt])
  have h₂ : BitVec.ofNat 32 (c₂ >>> 1).toNat = c₂ >>> 1 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2lt])
  rw [strChars_length, strChars_length, ← sub_ofNat32_eq_ofInt_diff, h₁, h₂]

theorem and_neg2_eq_shift (x : BitVec 32) :
    x &&& (-2#32) = (x >>> 1) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  have hneg : (-2#32 : BitVec 32) = ~~~(1#32) := by decide
  rw [hneg, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [hi, BitVec.getLsbD_ushiftRight, Nat.add_comm]

theorem and_neg2_eq (x : BitVec 32) :
    x &&& (-2#32) = BitVec.ofNat 32 (2 * (x >>> 1).toNat) := by
  rw [and_neg2_eq_shift]
  apply BitVec.eq_of_toNat_eq
  have hlt := ushiftRight1_lt x
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

theorem and_neg2_toNat (x : BitVec 32) :
    (x &&& (-2#32)).toNat = 2 * (x >>> 1).toNat := by
  rw [and_neg2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := ushiftRight1_lt x; omega

theorem word_of_bytes_ze32 (b0 b1 : UInt8) :
    BitVec.ofInt 32 (Int.ofBytes [b0, b1]) =
      (b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have h16 := word_of_bytes b0 b1
  have hlt : Int.ofBytes [b0, b1] < 2 ^ 16 := by simp [Int.ofBytes]; omega
  have hge : 0 ≤ Int.ofBytes [b0, b1] := Int.ofBytes_ge_zero _
  rw [← h16, ofInt_eq_ofNat_of_lt hge (by omega), ofInt_eq_ofNat_of_lt hge hlt]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem byte_ofInt_ze32 (b : UInt8) :
    BitVec.ofInt 32 (Int.ofBytes [b]) = (b.toBitVec.zeroExtend 16).zeroExtend 32 := by
  have hb : b.toNat < 256 := b.toBitVec.isLt
  have hsingle : Int.ofBytes [b] = b.toNat := by simp [Int.ofBytes]
  rw [hsingle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

theorem strChars_compressed_getElem {c : BitVec 32} {d : List UInt8}
    (h_comp : c.getLsbD 0 = false) (i : Nat) (hi : i < (strChars c d).length) :
    (strChars c d)[i]'hi = (d.getD i 0).toBitVec.zeroExtend 16 := by
  have hi' : i < (c >>> 1).toNat := by rwa [strChars_length] at hi
  exact strChars_compressed_get h_comp i hi'

theorem strChars_uncompressed_getElem {c : BitVec 32} {d : List UInt8}
    (h_uncomp : c.getLsbD 0 = true) (i : Nat) (hi : i < (strChars c d).length) :
    (strChars c d)[i]'hi =
      (d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
  have hi' : i < (c >>> 1).toNat := by rwa [strChars_length] at hi
  exact strChars_uncompressed_get h_uncomp i hi'

private theorem list_getD_eq_getElem {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i]'h := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem strChars_compressed_eq_of_bytes {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    (hc1 : c₁.getLsbD 0 = false) (hc2 : c₂.getLsbD 0 = false)
    (hl1 : d₁.length = strByteLen c₁) (hl2 : d₂.length = strByteLen c₂)
    {i : Nat} (hi1 : i < (strChars c₁ d₁).length) (hi2 : i < (strChars c₂ d₂).length)
    (hbyte : d₁[i]'(by rw [hl1, strByteLen_compressed hc1, ← strChars_length c₁ d₁]; exact hi1) =
             d₂[i]'(by rw [hl2, strByteLen_compressed hc2, ← strChars_length c₂ d₂]; exact hi2)) :
    (strChars c₁ d₁)[i]'hi1 = (strChars c₂ d₂)[i]'hi2 := by
  have hd1 : i < d₁.length := by rw [hl1, strByteLen_compressed hc1, ← strChars_length c₁ d₁]; exact hi1
  have hd2 : i < d₂.length := by rw [hl2, strByteLen_compressed hc2, ← strChars_length c₂ d₂]; exact hi2
  rw [strChars_compressed_getElem hc1 i hi1, strChars_compressed_getElem hc2 i hi2]
  rw [list_getD_eq_getElem d₁ i 0 hd1, list_getD_eq_getElem d₂ i 0 hd2, hbyte]

theorem strChars_compressed_ne_of_bytes {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    (hc1 : c₁.getLsbD 0 = false) (hc2 : c₂.getLsbD 0 = false)
    (hl1 : d₁.length = strByteLen c₁) (hl2 : d₂.length = strByteLen c₂)
    {i : Nat} (hi1 : i < (strChars c₁ d₁).length) (hi2 : i < (strChars c₂ d₂).length)
    (hbyte : d₁[i]'(by rw [hl1, strByteLen_compressed hc1, ← strChars_length c₁ d₁]; exact hi1) ≠
             d₂[i]'(by rw [hl2, strByteLen_compressed hc2, ← strChars_length c₂ d₂]; exact hi2)) :
    (strChars c₁ d₁)[i]'hi1 ≠ (strChars c₂ d₂)[i]'hi2 := by
  intro heq
  have hd1 : i < d₁.length := by rw [hl1, strByteLen_compressed hc1, ← strChars_length c₁ d₁]; exact hi1
  have hd2 : i < d₂.length := by rw [hl2, strByteLen_compressed hc2, ← strChars_length c₂ d₂]; exact hi2
  rw [strChars_compressed_getElem hc1 i hi1, strChars_compressed_getElem hc2 i hi2] at heq
  rw [list_getD_eq_getElem d₁ i 0 hd1, list_getD_eq_getElem d₂ i 0 hd2] at heq
  apply hbyte
  apply UInt8.toBitVec_inj.mp
  have := congrArg (BitVec.setWidth 8) heq
  simpa [BitVec.zeroExtend] using this

theorem u16_lo_byte (b0 b1 : UInt8) :
    (b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).setWidth 8 = b0.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, show i < 16 by omega, Bool.not_true, Bool.false_and,
    Bool.and_false, Bool.or_false]
  simp [hi]

theorem u16_hi_byte (b0 b1 : UInt8) :
    ((b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)) >>> 8).setWidth 8 = b1.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb0 : b0.toBitVec.getLsbD (8 + i) = false := by
    have hlt : b0.toNat < 2 ^ (8 + i) :=
      Nat.lt_of_lt_of_le b0.toBitVec.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
    show ¬(8 + i < 8) by omega, show 8 + i < 16 by omega,
    show 8 + i - 8 = i by omega, hb0]
  simp only [decide_eq_true hi, decide_eq_true (by omega : i < 16), decide_true, Bool.true_and,
    Bool.and_false, Bool.false_or, decide_false, Bool.not_false]

theorem strChars_uncompressed_eq_of_bytes {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    (hc1 : c₁.getLsbD 0 = true) (hc2 : c₂.getLsbD 0 = true)
    (hl1 : d₁.length = strByteLen c₁) (hl2 : d₂.length = strByteLen c₂)
    {k : Nat} (hk1 : k < (strChars c₁ d₁).length) (hk2 : k < (strChars c₂ d₂).length)
    (hlo : d₁[2 * k]'(by rw [hl1, strByteLen_uncompressed hc1, ← strChars_length c₁ d₁]; omega) =
           d₂[2 * k]'(by rw [hl2, strByteLen_uncompressed hc2, ← strChars_length c₂ d₂]; omega))
    (hhi : d₁[2 * k + 1]'(by rw [hl1, strByteLen_uncompressed hc1, ← strChars_length c₁ d₁]; omega) =
           d₂[2 * k + 1]'(by rw [hl2, strByteLen_uncompressed hc2, ← strChars_length c₂ d₂]; omega)) :
    (strChars c₁ d₁)[k]'hk1 = (strChars c₂ d₂)[k]'hk2 := by
  have hl1_1 : 2 * k + 1 < d₁.length := by rw [hl1, strByteLen_uncompressed hc1, ← strChars_length c₁ d₁]; omega
  have hl1_0 : 2 * k < d₁.length := by omega
  have hl2_1 : 2 * k + 1 < d₂.length := by rw [hl2, strByteLen_uncompressed hc2, ← strChars_length c₂ d₂]; omega
  have hl2_0 : 2 * k < d₂.length := by omega
  rw [strChars_uncompressed_getElem hc1 k hk1, strChars_uncompressed_getElem hc2 k hk2]
  rw [list_getD_eq_getElem d₁ (2 * k) 0 hl1_0, list_getD_eq_getElem d₁ (2 * k + 1) 0 hl1_1,
    list_getD_eq_getElem d₂ (2 * k) 0 hl2_0, list_getD_eq_getElem d₂ (2 * k + 1) 0 hl2_1, hlo, hhi]

theorem strChars_uncompressed_ne_of_byte {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    (hc1 : c₁.getLsbD 0 = true) (hc2 : c₂.getLsbD 0 = true)
    (hl1 : d₁.length = strByteLen c₁) (hl2 : d₂.length = strByteLen c₂)
    {b : Nat} (hb1 : b < d₁.length) (hb2 : b < d₂.length)
    (hne : d₁[b]'hb1 ≠ d₂[b]'hb2) :
    ∀ (hk1 : b / 2 < (strChars c₁ d₁).length) (hk2 : b / 2 < (strChars c₂ d₂).length),
      (strChars c₁ d₁)[b / 2]'hk1 ≠ (strChars c₂ d₂)[b / 2]'hk2 := by
  intro hk1 hk2 heq
  rw [strChars_uncompressed_getElem hc1 (b / 2) hk1,
    strChars_uncompressed_getElem hc2 (b / 2) hk2] at heq
  have hl1' : 2 * (b / 2) + 1 < d₁.length := by
    rw [hl1, strByteLen_uncompressed hc1, ← strChars_length c₁ d₁]; omega
  have hl2' : 2 * (b / 2) + 1 < d₂.length := by
    rw [hl2, strByteLen_uncompressed hc2, ← strChars_length c₂ d₂]; omega
  rw [list_getD_eq_getElem d₁ (2 * (b / 2)) 0 (by omega),
    list_getD_eq_getElem d₁ (2 * (b / 2) + 1) 0 hl1',
    list_getD_eq_getElem d₂ (2 * (b / 2)) 0 (by omega),
    list_getD_eq_getElem d₂ (2 * (b / 2) + 1) 0 hl2'] at heq
  apply hne
  by_cases hmod : b % 2 = 0
  · have hb_eq : 2 * (b / 2) = b := by omega
    apply UInt8.toBitVec_inj.mp
    have := congrArg (BitVec.setWidth 8) heq
    simp only [u16_lo_byte] at this
    simpa [hb_eq] using this
  · have hb_eq : 2 * (b / 2) + 1 = b := by omega
    apply UInt8.toBitVec_inj.mp
    have := congrArg (fun x : BitVec 16 => (x >>> 8).setWidth 8) heq
    simp only [u16_hi_byte] at this
    simpa [hb_eq] using this

/-! ## SIMD (`vpcmpeqb`/`vpmovmskb`/`bsf`) and QWORD (`xor`/`bsf`) byte-diff lemmas -/

private theorem getLsbD_ge_eq_false {w : Nat} (x : BitVec w) {i : Nat} (hi : w ≤ i) :
    x.getLsbD i = false := by
  have hlt : x.toNat < 2 ^ i := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hi)
  simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem foldl_ofLanes_byte_getLsbD (w : Nat) (hw : w % 8 = 0) (f : Nat → BitVec 8) (m : Nat)
    (hm : m ≤ w / 8) (bit : Nat) (hbit : bit < w) :
    ((List.range m).foldl (fun acc i => acc ||| ((f i).setWidth w <<< (8 * i))) 0#w).getLsbD bit =
      (decide (bit / 8 < m) && (f (bit / 8)).getLsbD (bit % 8)) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [BitVec.getLsbD_or, ih (by omega), BitVec.getLsbD_shiftLeft]
    by_cases hle : 8 * m' ≤ bit
    · by_cases hlt : bit - 8 * m' < 8
      · have hdiv : bit / 8 = m' := by omega
        have h1 : decide (bit / 8 < m') = false := decide_eq_false (by omega)
        have h2 : decide (bit / 8 < m' + 1) = true := decide_eq_true (by omega)
        have h3 : decide (bit % 8 < w) = true := decide_eq_true (by omega)
        have h4 : decide (bit < 8 * m') = false := decide_eq_false (by omega)
        rw [h1, h2, h4, Bool.false_and, Bool.false_or, Bool.true_and,
          decide_eq_true hbit, Bool.not_false, Bool.true_and, Bool.true_and,
          BitVec.getLsbD_setWidth, show bit - 8 * m' = bit % 8 by omega,
          hdiv, h3, Bool.true_and]
      · have h1 : decide (bit / 8 < m') = false := decide_eq_false (by omega)
        have h2 : decide (bit / 8 < m' + 1) = false := decide_eq_false (by omega)
        have hge : (f m').getLsbD (bit - 8 * m') = false :=
          getLsbD_ge_eq_false (f m') (by omega)
        rw [h1, h2, Bool.false_and, Bool.false_or, BitVec.getLsbD_setWidth, hge,
          Bool.and_false, Bool.and_false]
    · have h1 : decide (bit / 8 < m') = true := decide_eq_true (by omega)
      have h2 : decide (bit / 8 < m' + 1) = true := decide_eq_true (by omega)
      have h4 : decide (bit < 8 * m') = true := decide_eq_true (by omega)
      simp [h1, h2, h4]

theorem ofLanes_byte_getLsbD (w : Nat) (hw : w % 8 = 0) (f : Nat → BitVec 8)
    (bit : Nat) (hbit : bit < w) :
    (BitVec.ofLanes w 8 f).getLsbD bit = (f (bit / 8)).getLsbD (bit % 8) := by
  rw [BitVec.ofLanes, foldl_ofLanes_byte_getLsbD w hw f (w / 8) (Nat.le_refl _) bit hbit]
  have hdiv : bit / 8 < w / 8 := Nat.div_lt_of_lt_mul (by omega)
  simp [hdiv]

theorem lane_ofLanes_byte (w : Nat) (hw : w % 8 = 0) (f : Nat → BitVec 8)
    (j : Nat) (hj : j < w / 8) :
    (BitVec.ofLanes w 8 f).lane 8 j = f j := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.lane, BitVec.getLsbD_extractLsb', decide_eq_true hb, Bool.true_and]
  have hbit : 8 * j + b < w := by omega
  rw [ofLanes_byte_getLsbD w hw f (8 * j + b) hbit]
  rw [show (8 * j + b) / 8 = j by omega, show (8 * j + b) % 8 = b by omega]

theorem foldl_pmovmskb_getLsbD {w : Nat} (v : BitVec w) (m : Nat) (hm : m ≤ 32)
    (j : Nat) (hj : j < 32) :
    ((List.range m).foldl (fun acc i =>
      if (v.lane 8 i).msb then acc ||| (1#32 <<< i) else acc) 0#32).getLsbD j =
      (decide (j < m) && (v.lane 8 j).msb) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hmsb : (v.lane 8 m').msb = true
    · simp only [hmsb, ↓reduceIte, BitVec.getLsbD_or, ih (by omega), BitVec.getLsbD_shiftLeft, hj]
      by_cases hjm : j = m'
      · subst hjm
        have : ¬(j < j) := Nat.lt_irrefl _
        simp [this, hmsb]
      · by_cases hlt : j < m'
        · simp [hlt, show j < m' + 1 by omega]
        · have hge : ¬(j < m' + 1) := by omega
          have h1 : (1#32 : BitVec 32).getLsbD (j - m') = false := by
            obtain ⟨k, hk⟩ : ∃ k, j - m' = k + 1 := ⟨j - m' - 1, by omega⟩
            rw [hk]; simp
          simp [hlt, hge, h1]
    · have hf : (v.lane 8 m').msb = false := Bool.eq_false_iff.mpr hmsb
      simp only [hf, Bool.false_eq_true, ↓reduceIte, ih (by omega)]
      by_cases hjm : j = m'
      · subst hjm
        simp [hf]
      · congr 1
        simp [decide_eq_decide]
        omega

theorem pmovmskb_pcmpeqb_getLsbD (x y : BitVec 256) (j : Nat) (hj : j < 32) :
    (BitVec.pmovmskb (BitVec.pcmpeqb x y)).getLsbD j = (x.lane 8 j == y.lane 8 j) := by
  rw [BitVec.pmovmskb, foldl_pmovmskb_getLsbD _ (256 / 8) (by decide) j hj]
  have hlt : j < 256 / 8 := by omega
  rw [decide_eq_true hlt, Bool.true_and, BitVec.pcmpeqb, lane_ofLanes_byte 256 (by decide) _ j hlt]
  have ht255 : (0xFF#8 : BitVec 8).msb = true := by decide
  have hf0 : (0#8 : BitVec 8).msb = false := by decide
  by_cases heq : (x.lane 8 j == y.lane 8 j) = true
  · simp [heq, ht255]
  · have hf : (x.lane 8 j == y.lane 8 j) = false := Bool.eq_false_iff.mpr heq
    simp [hf, hf0]

theorem lane_ofInt_ofBytes (n : Nat) (bs : List UInt8) (hlen : bs.length = n)
    (j : Nat) (hj : j < n) :
    (BitVec.ofInt (8 * n) (Int.ofBytes bs)).lane 8 j = bs[j].toBitVec := by
  have hlt : Int.ofBytes bs < 256 ^ n := by
    rw [← hlen]; exact Int.ofBytes_lt bs
  have hge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have h256_nat : ∀ k : Nat, (256 : Int) ^ k = ((2 ^ (8 * k) : Nat) : Int) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Int.pow_succ, ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
      change ((2 ^ (8 * k) : Nat) : Int) * ((2 ^ 8 : Nat) : Int) = ((2 ^ (8 * k) * 2 ^ 8 : Nat) : Int)
      rw [Int.natCast_mul]
  have h256 : (256 : Int) ^ n = ((2 ^ (8 * n) : Nat) : Int) := h256_nat n
  have hwlt : Int.ofBytes bs < ((2 ^ (8 * n) : Nat) : Int) := by rw [← h256]; exact hlt
  have hmod_all : (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toNat = (Int.ofBytes bs).toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hge hwlt]
  have htake : (bs.take j).length = j := List.length_take_of_le (by omega)
  have hsplit : bs = bs.take j ++ bs[j] :: bs.drop (j + 1) := by
    have h := (List.take_append_drop j bs).symm
    rwa [List.drop_eq_getElem_cons (by omega)] at h
  have hbytes : Int.ofBytes bs =
      Int.ofBytes (bs.take j) + 256 ^ j * (bs[j].toNat + 256 * Int.ofBytes (bs.drop (j + 1))) := by
    conv => lhs; rw [hsplit]
    rw [Int.ofBytes_append, htake, Int.ofBytes_cons]
    have hcomm : Int.ofBytes (bs.drop (j + 1)) * 256 + (bs[j].toNat : Int) =
        bs[j].toNat + 256 * Int.ofBytes (bs.drop (j + 1)) := by omega
    rw [hcomm]
  have hp_lt : Int.ofBytes (bs.take j) < 256 ^ j := by
    have := Int.ofBytes_lt (bs.take j)
    rwa [htake] at this
  have hp_ge : 0 ≤ Int.ofBytes (bs.take j) := Int.ofBytes_ge_zero _
  have hr_ge : 0 ≤ Int.ofBytes (bs.drop (j + 1)) := Int.ofBytes_ge_zero _
  have hb_lt : bs[j].toNat < 256 := bs[j].toBitVec.isLt
  let P := (Int.ofBytes (bs.take j)).toNat
  let Q := (Int.ofBytes (bs.drop (j + 1))).toNat
  have h256j : (256 : Int) ^ j = ((2 ^ (8 * j) : Nat) : Int) := h256_nat j
  have hP_eq : Int.ofBytes (bs.take j) = (P : Int) := (Int.toNat_of_nonneg hp_ge).symm
  have hQ_eq : Int.ofBytes (bs.drop (j + 1)) = (Q : Int) := (Int.toNat_of_nonneg hr_ge).symm
  have hP_lt : P < 2 ^ (8 * j) := by
    have hlt' : (P : Int) < ((2 ^ (8 * j) : Nat) : Int) := by rw [← hP_eq, ← h256j]; exact hp_lt
    exact Int.ofNat_lt.mp hlt'
  have hD_pos : 0 < 2 ^ (8 * j) := Nat.pow_pos (by omega)
  have hbytes_nat : Int.ofBytes bs = ((P + 2 ^ (8 * j) * (bs[j].toNat + 256 * Q) : Nat) : Int) := by
    rw [hbytes, hP_eq, hQ_eq, h256j]
    change (P : Int) + ((2 ^ (8 * j) : Nat) : Int) * ((bs[j].toNat : Int) + ((256 : Nat) : Int) * (Q : Int)) = _
    simp only [Int.natCast_add, Int.natCast_mul]
  have hnat_eq : (Int.ofBytes bs).toNat = P + 2 ^ (8 * j) * (bs[j].toNat + 256 * Q) := by
    rw [hbytes_nat, Int.toNat_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.lane, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hmod_all, hnat_eq]
  rw [Nat.add_mul_div_left _ _ hD_pos, Nat.div_eq_of_lt hP_lt, Nat.zero_add]
  change (bs[j].toNat + 256 * Q) % 256 = bs[j].toBitVec.toNat
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb_lt]
  rfl

theorem findSome?_range_spec {α : Type} (f : Nat → Option α) (w : Nat) (v : α)
    (h : (List.range w).findSome? f = some v) :
    ∃ i < w, f i = some v ∧ ∀ j < i, f j = none := by
  induction w with
  | zero => simp at h
  | succ w ih =>
    rw [List.range_succ, List.findSome?_append] at h
    cases h1 : (List.range w).findSome? f with
    | some v' =>
      rw [h1] at h
      simp at h
      subst h
      obtain ⟨i, hi, hfi, hfirst⟩ := ih h1
      exact ⟨i, Nat.lt_succ_of_lt hi, hfi, hfirst⟩
    | none =>
      rw [h1] at h
      simp only [Option.none_or, List.findSome?_cons, List.findSome?_nil] at h
      cases fw : f w with
      | none => rw [fw] at h; simp at h
      | some v' =>
        rw [fw] at h; injection h with heq; subst heq
        refine ⟨w, Nat.lt_succ_self w, fw, fun j hj => ?_⟩
        cases fj : f j with
        | none => rfl
        | some u =>
          exfalso
          have hmem : j ∈ List.range w := List.mem_range.mpr hj
          exact absurd (List.findSome?_eq_none_iff.mp h1 j hmem) (by simp [fj])

theorem bsf_spec' {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    ∃ i < w, BitVec.bsf x = BitVec.ofNat w i ∧
             x.getLsbD i = true ∧
             ∀ j < i, x.getLsbD j = false := by
  unfold BitVec.bsf
  have h_some : ∃ v, (List.range w).findSome? (fun i => if x.getLsbD i then some i else none) = some v := by
    cases h : (List.range w).findSome? (fun i => if x.getLsbD i then some i else none) with
    | some v => exact ⟨v, rfl⟩
    | none =>
      exfalso
      have h_all : ∀ i < w, x.getLsbD i = false := by
        intro i hi
        have hi_in : i ∈ List.range w := List.mem_range.mpr hi
        have := List.findSome?_eq_none_iff.mp h i hi_in
        cases h_lsb : x.getLsbD i
        · rfl
        · simp [h_lsb] at this
      have hx0 : x = 0#w := by
        ext i hi
        change x.getLsbD i = (0#w).getLsbD i
        rw [h_all i hi]; simp
      exact hx hx0
  obtain ⟨v, hv⟩ := h_some
  rw [hv]
  obtain ⟨i, hi, hfi, hfj⟩ := findSome?_range_spec (fun i => if x.getLsbD i then some i else none) w v hv
  cases h_lsb : x.getLsbD i
  · rw [h_lsb] at hfi; simp at hfi
  · rw [h_lsb] at hfi
    injection hfi with hfi
    subst hfi
    refine ⟨i, hi, rfl, h_lsb, ?_⟩
    intro j hj
    have := hfj j hj
    cases h_j : x.getLsbD j
    · rfl
    · rw [h_j] at this; simp at this

theorem bsf_toNat' {w : Nat} (x : BitVec w) (hw2 : w < 2 ^ w) (hx : x ≠ 0#w) :
    ∃ i < w, (BitVec.bsf x).toNat = i ∧
             x.getLsbD i = true ∧
             ∀ j < i, x.getLsbD j = false := by
  obtain ⟨i, hi, h_bsf, h_true, h_false⟩ := bsf_spec' x hx
  rw [h_bsf]
  have : (BitVec.ofNat w i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hi hw2)]
  exact ⟨i, hi, this, h_true, h_false⟩

theorem pmovmskb_pcmpeqb_first_diff (bs₁ bs₂ : List UInt8)
    (hl1 : bs₁.length = 32) (hl2 : bs₂.length = 32)
    (hne : BitVec.pmovmskb (BitVec.pcmpeqb
      (BitVec.ofInt 256 (Int.ofBytes bs₁))
      (BitVec.ofInt 256 (Int.ofBytes bs₂))) ≠ -1#32) :
    ∃ b, ∃ (_ : b < 32),
      (BitVec.bsf (~~~BitVec.pmovmskb (BitVec.pcmpeqb
        (BitVec.ofInt 256 (Int.ofBytes bs₁))
        (BitVec.ofInt 256 (Int.ofBytes bs₂))))).toNat = b ∧
      BitVec.bsf (~~~BitVec.pmovmskb (BitVec.pcmpeqb
        (BitVec.ofInt 256 (Int.ofBytes bs₁))
        (BitVec.ofInt 256 (Int.ofBytes bs₂)))) = BitVec.ofNat 32 b ∧
      (∀ (j : Nat) (hj : j < b), bs₁[j]'(by omega) = bs₂[j]'(by omega)) ∧
      bs₁[b]'(by omega) ≠ bs₂[b]'(by omega) := by
  let v₁ := BitVec.ofInt 256 (Int.ofBytes bs₁)
  let v₂ := BitVec.ofInt 256 (Int.ofBytes bs₂)
  let m := BitVec.pmovmskb (BitVec.pcmpeqb v₁ v₂)
  have hm_ne : ~~~m ≠ 0#32 := by
    intro h0
    apply hne
    have : ~~~(~~~m) = ~~~(0#32) := congrArg (~~~·) h0
    simpa using this
  obtain ⟨b, hb_lt, hb_eq, hb_true, hb_false⟩ := bsf_toNat' (~~~m) (by decide) hm_ne
  refine ⟨b, hb_lt, hb_eq, ?_, ?_, ?_⟩
  · change BitVec.bsf (~~~m) = BitVec.ofNat 32 b
    apply BitVec.eq_of_toNat_eq
    rw [hb_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro j hj
    have hj32 : j < 32 := Nat.lt_trans hj hb_lt
    have hf := hb_false j hj
    rw [BitVec.getLsbD_not, decide_eq_true hj32, Bool.true_and] at hf
    have htm : m.getLsbD j = true := by
      cases hm : m.getLsbD j <;> simp_all
    change (BitVec.pmovmskb (BitVec.pcmpeqb v₁ v₂)).getLsbD j = true at htm
    rw [pmovmskb_pcmpeqb_getLsbD v₁ v₂ j hj32, beq_iff_eq] at htm
    rw [lane_ofInt_ofBytes 32 bs₁ hl1 j hj32, lane_ofInt_ofBytes 32 bs₂ hl2 j hj32] at htm
    exact UInt8.toBitVec_inj.mp htm
  · have ht := hb_true
    rw [BitVec.getLsbD_not, decide_eq_true hb_lt, Bool.true_and] at ht
    have hfm : m.getLsbD b = false := by
      cases hm : m.getLsbD b <;> simp_all
    change (BitVec.pmovmskb (BitVec.pcmpeqb v₁ v₂)).getLsbD b = false at hfm
    rw [pmovmskb_pcmpeqb_getLsbD v₁ v₂ b hb_lt, beq_eq_false_iff_ne] at hfm
    rw [lane_ofInt_ofBytes 32 bs₁ hl1 b hb_lt, lane_ofInt_ofBytes 32 bs₂ hl2 b hb_lt] at hfm
    exact fun h => hfm (congrArg UInt8.toBitVec h)

theorem xor_bsf_first_diff_byte (bs₁ bs₂ : List UInt8)
    (hl1 : bs₁.length = 8) (hl2 : bs₂.length = 8)
    (hne : BitVec.ofInt 64 (Int.ofBytes bs₁) ^^^ BitVec.ofInt 64 (Int.ofBytes bs₂) ≠ 0#64) :
    ∃ r, ∃ (_ : r < 8),
      ((BitVec.bsf (BitVec.ofInt 64 (Int.ofBytes bs₁) ^^^
        BitVec.ofInt 64 (Int.ofBytes bs₂))).setWidth 32 >>> 3).toNat = r ∧
      (∀ (j : Nat) (hj : j < r), bs₁[j]'(by omega) = bs₂[j]'(by omega)) ∧
      bs₁[r]'(by omega) ≠ bs₂[r]'(by omega) := by
  let w₁ := BitVec.ofInt 64 (Int.ofBytes bs₁)
  let w₂ := BitVec.ofInt 64 (Int.ofBytes bs₂)
  obtain ⟨k, hk_lt, hk_toNat, hk_true, hk_false⟩ := bsf_toNat' (w₁ ^^^ w₂) (by decide) hne
  have hr_lt : k / 8 < 8 := by omega
  have hsh : ((BitVec.bsf (w₁ ^^^ w₂)).setWidth 32 >>> 3).toNat = k / 8 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, hk_toNat,
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨k / 8, hr_lt, hsh, ?_, ?_⟩
  · intro j hj
    have hbyte : w₁.lane 8 j = w₂.lane 8 j := by
      apply BitVec.eq_of_getLsbD_eq
      intro bit hbit
      simp only [BitVec.lane, BitVec.getLsbD_extractLsb', decide_eq_true hbit, Bool.true_and]
      have hidx : 8 * j + bit < k := by omega
      have hf := hk_false (8 * j + bit) hidx
      rw [BitVec.getLsbD_xor] at hf
      cases h1 : w₁.getLsbD (8 * j + bit) <;> cases h2 : w₂.getLsbD (8 * j + bit) <;> simp_all
    rw [lane_ofInt_ofBytes 8 bs₁ hl1 j (by omega), lane_ofInt_ofBytes 8 bs₂ hl2 j (by omega)] at hbyte
    exact UInt8.toBitVec_inj.mp hbyte
  · intro hsame
    have hbyte : w₁.lane 8 (k / 8) = w₂.lane 8 (k / 8) := by
      rw [lane_ofInt_ofBytes 8 bs₁ hl1 (k / 8) hr_lt,
        lane_ofInt_ofBytes 8 bs₂ hl2 (k / 8) hr_lt, hsame]
    have hbit := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8)) hbyte
    have hk_mod : k % 8 < 8 := Nat.mod_lt _ (by omega)
    simp only [BitVec.lane, BitVec.getLsbD_extractLsb', decide_eq_true hk_mod, Bool.true_and,
      show 8 * (k / 8) + k % 8 = k by omega] at hbit
    have ht := hk_true
    rw [BitVec.getLsbD_xor, hbit, Bool.xor_self] at ht
    contradiction

/-! ## `StringsInMem` helpers -/

theorem stringsInMem_same {s₁ s₂ : BitVec 64} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : StringsInMem s₁ s₂ c₁ c₂ d₁ d₂ R m)
    (heq : s₁ = s₂) :
    compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) = 0#32 := by
  simp only [StringsInMem, heq, ↓reduceIte] at h
  rcases h with ⟨rfl, rfl, _⟩
  exact compareToSpec_self _

theorem stringsInMem_left {s₁ s₂ : BitVec 64} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : StringsInMem s₁ s₂ c₁ c₂ d₁ d₂ R m) :
    ∃ R', (StringAt s₁ c₁ d₁ ⋆ R') m := by
  by_cases heq : s₁ = s₂
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    exact ⟨R, heq ▸ h.2.2⟩
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    rw [Std.ExtHashMap.sep_assoc] at h
    exact ⟨StringAt s₂ c₂ d₂ ⋆ R, h⟩

theorem stringsInMem_right {s₁ s₂ : BitVec 64} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : StringsInMem s₁ s₂ c₁ c₂ d₁ d₂ R m) :
    ∃ R', (StringAt s₂ c₂ d₂ ⋆ R') m := by
  by_cases heq : s₁ = s₂
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    rcases h with ⟨rfl, rfl, hm⟩
    exact ⟨R, hm⟩
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at h
    exact ⟨StringAt s₁ c₁ d₁ ⋆ R, h⟩

theorem stringsInMem_frame {s₁ s₂ : BitVec 64} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (h : StringsInMem s₁ s₂ c₁ c₂ d₁ d₂ R m) :
    ∃ L, (L ⋆ R) m := by
  by_cases heq : s₁ = s₂
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    exact ⟨StringAt s₂ c₁ d₁, h.2.2⟩
  · simp only [StringsInMem, heq, ↓reduceIte] at h
    exact ⟨StringAt s₁ c₁ d₁ ⋆ StringAt s₂ c₂ d₂, h⟩

end

end Kraken.X64.Art
