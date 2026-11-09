module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
public import Kraken.X64.Art.StringEquals
public import Kraken.X64.Art.StringIndexOfSpec
public import Kraken.X64.Art.StringCompareToSpec

open Std
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/-- An operand that ART `String.getCharsNoCheck` accepts as either a register or a 32-bit
    constant (`Location::RegisterOrConstant`). -/
inductive RegOrImm where
  | reg (r : Reg64)
  | imm (v : BitVec 32)
  deriving DecidableEq, Repr

/-- 32-bit value of a `RegOrImm` in register state `regs`. -/
@[expose] def RegOrImm.eval32 (x : RegOrImm) (regs : Reg64s) : BitVec 32 :=
  match x with
  | .reg r => (regs.get64 r).setWidth 32
  | .imm v => v

/-- Unsigned 32-bit `Nat` value of a `RegOrImm` in register state `regs`. -/
@[expose] def RegOrImm.toNat (x : RegOrImm) (regs : Reg64s) : Nat :=
  (x.eval32 regs).toNat

/-- Zero-extended 64-bit value corresponding to the 32-bit value of `x`. -/
@[expose] def RegOrImm.eval64 (x : RegOrImm) (regs : Reg64s) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat regs)

/-- Upper 32 bits are zero when `x` is passed in a 64-bit register (required for 64-bit `leaq`
    indexing). -/
@[expose] def RegOrImm.hi32Zero (x : RegOrImm) (regs : Reg64s) : Prop :=
  match x with
  | .reg r => (regs.get64 r).toNat < 2 ^ 32
  | .imm _ => True

/-- Register footprint of a `RegOrImm`. -/
@[expose] def RegOrImm.regs (x : RegOrImm) : List Reg64 :=
  match x with
  | .reg r => [r]
  | .imm _ => []

/-- Signed 32-bit displacement fit for ART's `ArrayAddress(obj, srcBegin, ...)` when `srcBegin`
    is a constant. -/
@[expose] def srcBeginDisp32Fit (srcBegin : RegOrImm) (c : BitVec 32) : Prop :=
  match srcBegin with
  | .reg _ => True
  | .imm v => (if c.getLsbD 0 then 2 * v.toNat else v.toNat) + 16 < 2 ^ 31

/-- Signed 32-bit displacement fit for ART's `ArrayAddress(dst, dstBegin, ...)` when `dstBegin`
    is a constant. -/
@[expose] def dstBeginDisp32Fit (dstBegin : RegOrImm) : Prop :=
  match dstBegin with
  | .reg _ => True
  | .imm v => 2 * v.toNat + 12 < 2 ^ 31

/-- Address of `dst[dstBegin]` in an ART `char[]` object (`data` payload at `+12`, 2 bytes per
    UTF-16 code unit). -/
@[expose] def getCharsDstAddr (dst : Reg64) (dstBegin : RegOrImm) (regs : Reg64s) : BitVec 64 :=
  regs.get64 dst + 12#64 + 2#64 * dstBegin.eval64 regs

/-- Encode a list of UTF-16 code units as little-endian bytes. -/
@[expose] def utf16le (cs : List (BitVec 16)) : List UInt8 :=
  cs.flatMap fun ch =>
    [(ch.extractLsb' 0 8).toNat.toUInt8, (ch.extractLsb' 8 8).toNat.toUInt8]

/-- Target bytes written into `dst[dstBegin .. dstBegin + (e - b))` by
    `String.getCharsNoCheck(srcBegin = b, srcEnd = e, dst, dstBegin)`. -/
@[expose] def getCharsBytes (c : BitVec 32) (d : List UInt8) (b e : Nat) : List UInt8 :=
  utf16le (((strChars c d).drop b).take (e - b))

/-- Shared precondition for both baseline and AVX2 lowerings of `String.getCharsNoCheck`. -/
@[expose] def StringGetCharsPre
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst : Reg64) (dstBegin : RegOrImm)
    (c : BitVec 32) (d : List UInt8) (s : MachineData) : Prop :=
  let b := srcBegin.toNat s.regs
  let e := ((s.regs.get64 srcEnd).setWidth 32).toNat
  let dstAddr := getCharsDstAddr dst dstBegin s.regs
  d.length = strByteLen c ∧
  b ≤ e ∧ e ≤ (c >>> 1).toNat ∧
  srcBegin.hi32Zero s.regs ∧
  dstBegin.hi32Zero s.regs ∧
  (s.regs.get64 dst).getLsbD 0 = false ∧
  srcBeginDisp32Fit srcBegin c ∧
  dstBeginDisp32Fit dstBegin ∧
  ∃ (old : List UInt8) (R : Mem 64 → Prop), old.length = 2 * (e - b) ∧
    (StringAt (s.regs.get64 obj) c d ⋆ Eq (old.At dstAddr) ⋆ R) s.dmem

/-- Shared postcondition for both baseline and AVX2 lowerings of `String.getCharsNoCheck`. -/
@[expose] def StringGetCharsPost
    (srcBegin : RegOrImm) (srcEnd dst : Reg64) (dstBegin : RegOrImm)
    (temps : List Reg64) (ymms : List (AvxReg .W256))
    (c : BitVec 32) (d : List UInt8) (s t : MachineData) : Prop :=
  let b := srcBegin.toNat s.regs
  let e := ((s.regs.get64 srcEnd).setWidth 32).toNat
  let dstAddr := getCharsDstAddr dst dstBegin s.regs
  t.dmem = s.dmem.storeBytes dstAddr (getCharsBytes c d b e) ∧
  (∀ r, r ∉ temps → t.regs.get64 r = s.regs.get64 r) ∧
  (t.zmms = s.zmms ∨ ∃ vs, t.zmms = (s.zmms.setAll ymms vs).zeroUpper)

/-- ART `CodeGeneratorX86_64::ArrayAddress(base, idx, scale, offset)` addressing expression. -/
@[expose] def arrayAddr (base : Reg64) (idx : RegOrImm) (scale : Width) (offset : Nat) : AddrExpr :=
  match idx with
  | .reg r =>
    { base := some (.reg base), idx := some ⟨r, scale⟩, disp := .int64 (Int64.ofNat offset) }
  | .imm v =>
    { base := some (.reg base), idx := none,
      disp := .int64 (Int64.ofNat (offset + scale.bytes * v.toNat)) }

namespace GetCharsProof

open Proof (addr_base_disp addr_sib1_disp addr_base_disp' addr_sib1_disp'
  loadInt_eq ofInt_ofBytes_inj i64_add_sub sub_beq_zero
  ofNat32_add_lit ofNat32_sub_lit ofNat32_eq_zero cf_ofNat32
  sw32_64 sw32_ofNat reg64s_ext regZmms_ext lowMm
  get512_zeroUpper_low get512_zeroUpper_high
  zmms_get_set zmms_set_set zeroUpper_set_get
  get64_set64 get512_set512 get_low32 get_low64 set_low32 set_low64
  sep_get_l sep_get_r at_get padded stringAt_cnt stringAt_data load_count strByteLen_lt)

/-! ## `RegOrImm` and `arrayAddr` lemmas -/

theorem RegOrImm.toNat_lt {x : RegOrImm} {regs : Reg64s} : x.toNat regs < 2 ^ 32 :=
  (x.eval32 regs).isLt

theorem RegOrImm.eval64_reg {r : Reg64} {regs : Reg64s}
    (hhi : RegOrImm.hi32Zero (.reg r) regs) :
    RegOrImm.eval64 (.reg r) regs = regs.get64 r := by
  simp only [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have hlt : (regs.get64 r).toNat < 2 ^ 32 := hhi
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]

theorem BitVec.ofInt_signed_mul_ofNat (x : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (x.signed * n) = x * BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_mul]
  congr 1
  apply BitVec.eq_of_toInt_eq; simp [BitVec.signed]

theorem addr_arrayAddr [Labels] (regs : Reg64s) (base : Reg64) (idx : RegOrImm)
    (scale : Width) (offset : Nat) (p : Std.Rco Int64)
    (hhi : idx.hi32Zero regs) :
    (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr base idx scale offset) regs p : BitVec 64) =
      regs.get64 base + BitVec.ofNat 64 offset + BitVec.ofNat 64 scale.bytes * idx.eval64 regs := by
  cases idx with
  | reg r =>
    simp only [arrayAddr, AddrExpr.interp, BitVec.toAddressSize, BitVec.take, Width.bits,
      ConstExpr.interp, BitVec.extractLsb'_eq_self]
    rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_signed_mul_ofNat]
    simp only [BitVec.signed]
    rw [BitVec.ofInt_toInt, ← Int64.toInt_toBitVec, BitVec.ofInt_toInt, Int64.toBitVec_ofNat_grind,
      RegOrImm.eval64_reg hhi, BitVec.mul_comm]
    change regs.get64 base + BitVec.ofNat 64 scale.bytes * regs.get64 r + BitVec.ofNat 64 offset = _
    ac_rfl
  | imm v =>
    simp only [arrayAddr, AddrExpr.interp, BitVec.toAddressSize, BitVec.take, Width.bits,
      ConstExpr.interp, BitVec.extractLsb'_eq_self, RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32]
    rw [Int.add_zero, BitVec.ofInt_add]
    simp only [BitVec.signed]
    rw [BitVec.ofInt_toInt, ← Int64.toInt_toBitVec, BitVec.ofInt_toInt, Int64.toBitVec_ofNat_grind]
    change regs.get64 base + BitVec.ofNat 64 (offset + scale.bytes * v.toNat) = _
    rw [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_assoc]

/-! ## `utf16le`, `getCharsBytes`, `expBytes`, and `pmovzxbw` lemmas -/

/-- Expand each byte `b` into little-endian UTF-16 code unit `[b, 0]`. -/
@[expose] def expBytes (bs : List UInt8) : List UInt8 :=
  bs.flatMap fun b => [b, 0]

theorem expBytes_length (bs : List UInt8) : (expBytes bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [expBytes, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem expBytes_getElem (bs : List UInt8) (j : Nat) (hj : j < 2 * bs.length) :
    (expBytes bs)[j]'(by rw [expBytes_length]; exact hj) =
      if j % 2 = 0 then bs[j / 2]'(by omega) else 0 := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    match j with
    | 0 => simp [expBytes]
    | 1 => simp [expBytes]
    | j' + 2 =>
      have hj' : j' < 2 * bs.length := by simp at hj; omega
      have hsub := ih j' hj'
      simp only [expBytes, List.flatMap_cons, List.cons_append, List.nil_append,
        List.getElem_cons_succ] at hsub ⊢
      rw [hsub]
      have hmod : (j' + 2) % 2 = j' % 2 := by omega
      have hdiv : (j' + 2) / 2 = j' / 2 + 1 := by omega
      simp [hmod, hdiv]

theorem utf16le_length (cs : List (BitVec 16)) : (utf16le cs).length = 2 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [utf16le, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem utf16le_getElem_even (cs : List (BitVec 16)) (j : Nat) (hj : j < cs.length) :
    (utf16le cs)[2 * j]'(by rw [utf16le_length]; omega) =
      (cs[j].extractLsb' 0 8).toNat.toUInt8 := by
  induction cs generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => simp [utf16le]
    | succ j' =>
      have hj' : j' < cs.length := by simp at hj; omega
      simpa [utf16le, Nat.mul_succ, Nat.add_assoc] using ih j' hj'

theorem utf16le_getElem_odd (cs : List (BitVec 16)) (j : Nat) (hj : j < cs.length) :
    (utf16le cs)[2 * j + 1]'(by rw [utf16le_length]; omega) =
      (cs[j].extractLsb' 8 8).toNat.toUInt8 := by
  induction cs generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => simp [utf16le]
    | succ j' =>
      have hj' : j' < cs.length := by simp at hj; omega
      simpa [utf16le, Nat.mul_succ, Nat.add_assoc] using ih j' hj'

theorem getCharsBytes_length (c : BitVec 32) (d : List UInt8) {b e : Nat}
    (hb : b ≤ e) (he : e ≤ (c >>> 1).toNat) :
    (getCharsBytes c d b e).length = 2 * (e - b) := by
  unfold getCharsBytes
  rw [utf16le_length, List.length_take, List.length_drop, strChars_length]
  omega

private theorem bv8_extract0_ze16 (x : BitVec 8) :
    (x.zeroExtend 16).extractLsb' 0 8 = x := by bv_decide

private theorem bv8_extract8_ze16 (x : BitVec 8) :
    (x.zeroExtend 16).extractLsb' 8 8 = 0#8 := by bv_decide

private theorem bv8_extract0_or16 (x0 x1 : BitVec 8) :
    (x0.zeroExtend 16 ||| (x1.zeroExtend 16 <<< 8)).extractLsb' 0 8 = x0 := by bv_decide

private theorem bv8_extract8_or16 (x0 x1 : BitVec 8) :
    (x0.zeroExtend 16 ||| (x1.zeroExtend 16 <<< 8)).extractLsb' 8 8 = x1 := by bv_decide

private theorem bv_extract0_ze16 (b : UInt8) :
    ((b.toBitVec.zeroExtend 16).extractLsb' 0 8).toNat.toUInt8 = b := by
  rw [bv8_extract0_ze16 b.toBitVec]
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp

private theorem bv_extract8_ze16 (b : UInt8) :
    ((b.toBitVec.zeroExtend 16).extractLsb' 8 8).toNat.toUInt8 = 0 := by
  rw [bv8_extract8_ze16 b.toBitVec]; rfl

private theorem bv_extract0_or16 (b0 b1 : UInt8) :
    (((b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).extractLsb' 0 8).toNat.toUInt8) = b0 := by
  rw [bv8_extract0_or16 b0.toBitVec b1.toBitVec]
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp

private theorem bv_extract8_or16 (b0 b1 : UInt8) :
    (((b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).extractLsb' 8 8).toNat.toUInt8) = b1 := by
  rw [bv8_extract8_or16 b0.toBitVec b1.toBitVec]
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp

theorem getCharsBytes_compressed_getElem {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    {b e : Nat} (hb : b ≤ e) (he : e ≤ (c >>> 1).toNat)
    (k : Nat) (hk : k < 2 * (e - b)) :
    (getCharsBytes c d b e)[k]'(by rw [getCharsBytes_length c d hb he]; exact hk) =
      if k % 2 = 0 then d[b + k / 2]'(by rw [hl, strByteLen_compressed hc]; omega) else 0 := by
  have hlen_sub : (((strChars c d).drop b).take (e - b)).length = e - b := by
    rw [List.length_take, List.length_drop, strChars_length]; omega
  have hj : k / 2 < (((strChars c d).drop b).take (e - b)).length := by omega
  have hbj : b + k / 2 < (strChars c d).length := by rw [strChars_length]; omega
  have hchar : (((strChars c d).drop b).take (e - b))[k / 2]'hj =
      (d[b + k / 2]'(by rw [hl, strByteLen_compressed hc]; omega)).toBitVec.zeroExtend 16 := by
    rw [List.getElem_take, List.getElem_drop, strChars_compressed_getElem hc _ hbj]
    have hgetD : d.getD (b + k / 2) 0 = d[b + k / 2]'(by rw [hl, strByteLen_compressed hc]; omega) := by
      change d[b + k / 2]?.getD 0 = _
      rw [List.getElem?_eq_getElem (by rw [hl, strByteLen_compressed hc]; omega)]; rfl
    rw [hgetD]
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · have hk_div : (2 * j) / 2 = j := by omega
    have hmod : (2 * j) % 2 = 0 := by omega
    simp only [hmod, ↓reduceIte]
    have hcharj : (((strChars c d).drop b).take (e - b))[j]'(by omega) =
        (d[b + j]'(by rw [hl, strByteLen_compressed hc]; omega)).toBitVec.zeroExtend 16 := by
      simpa [hk_div] using hchar
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem]
    unfold getCharsBytes
    rw [List.getElem?_eq_getElem (by rw [utf16le_length, hlen_sub]; omega),
      utf16le_getElem_even _ j (by omega)]
    congr 1
    rw [hcharj, bv_extract0_ze16]
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hk_div]
  · have hk_div : (2 * j + 1) / 2 = j := by omega
    have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
    simp only [hmod, ↓reduceIte]
    have hcharj : (((strChars c d).drop b).take (e - b))[j]'(by omega) =
        (d[b + j]'(by rw [hl, strByteLen_compressed hc]; omega)).toBitVec.zeroExtend 16 := by
      simpa [hk_div] using hchar
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem]
    unfold getCharsBytes
    rw [List.getElem?_eq_getElem (by rw [utf16le_length, hlen_sub]; omega),
      utf16le_getElem_odd _ j (by omega)]
    congr 1
    rw [hcharj, bv_extract8_ze16]

theorem getCharsBytes_compressed_eq_expBytes {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    {b e : Nat} (hb : b ≤ e) (he : e ≤ (c >>> 1).toNat) :
    getCharsBytes c d b e = expBytes ((d.drop b).take (e - b)) := by
  have hl_take : ((d.drop b).take (e - b)).length = e - b := by
    rw [List.length_take, List.length_drop, hl, strByteLen_compressed hc]; omega
  apply List.ext_getElem
  · rw [getCharsBytes_length c d hb he, expBytes_length, hl_take]
  · intro k hk1 hk2
    have hk : k < 2 * (e - b) := by rw [getCharsBytes_length c d hb he] at hk1; exact hk1
    rw [getCharsBytes_compressed_getElem hc hl hb he k hk,
      expBytes_getElem _ k (by rw [hl_take]; exact hk)]
    split <;> simp [List.getElem_take, List.getElem_drop]

theorem getCharsBytes_uncompressed_getElem {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    {b e : Nat} (hb : b ≤ e) (he : e ≤ (c >>> 1).toNat)
    (k : Nat) (hk : k < 2 * (e - b)) :
    (getCharsBytes c d b e)[k]'(by rw [getCharsBytes_length c d hb he]; exact hk) =
      d[2 * b + k]'(by rw [hl, strByteLen_uncompressed hc]; omega) := by
  have hlen_sub : (((strChars c d).drop b).take (e - b)).length = e - b := by
    rw [List.length_take, List.length_drop, strChars_length]; omega
  have hj : k / 2 < (((strChars c d).drop b).take (e - b)).length := by omega
  have hbj : b + k / 2 < (strChars c d).length := by rw [strChars_length]; omega
  have h_even_lt : 2 * (b + k / 2) < d.length := by rw [hl, strByteLen_uncompressed hc]; omega
  have h_odd_lt : 2 * (b + k / 2) + 1 < d.length := by rw [hl, strByteLen_uncompressed hc]; omega
  have hgetD0 : d.getD (2 * (b + k / 2)) 0 = d[2 * (b + k / 2)]'h_even_lt := by
    change d[2 * (b + k / 2)]?.getD 0 = _
    rw [List.getElem?_eq_getElem h_even_lt]; rfl
  have hgetD1 : d.getD (2 * (b + k / 2) + 1) 0 = d[2 * (b + k / 2) + 1]'h_odd_lt := by
    change d[2 * (b + k / 2) + 1]?.getD 0 = _
    rw [List.getElem?_eq_getElem h_odd_lt]; rfl
  have hchar : (((strChars c d).drop b).take (e - b))[k / 2]'hj =
      (d[2 * (b + k / 2)]'h_even_lt).toBitVec.zeroExtend 16 |||
        ((d[2 * (b + k / 2) + 1]'h_odd_lt).toBitVec.zeroExtend 16 <<< 8) := by
    rw [List.getElem_take, List.getElem_drop, strChars_uncompressed_getElem hc (b + k / 2) hbj,
      hgetD0, hgetD1]
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · have hk_div : (2 * j) / 2 = j := by omega
    have hcharj : (((strChars c d).drop b).take (e - b))[j]'(by omega) =
        (d[2 * (b + j)]'(by rw [hl, strByteLen_uncompressed hc]; omega)).toBitVec.zeroExtend 16 |||
          ((d[2 * (b + j) + 1]'(by rw [hl, strByteLen_uncompressed hc]; omega)).toBitVec.zeroExtend 16 <<< 8) := by
      simpa [hk_div] using hchar
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem]
    unfold getCharsBytes
    rw [List.getElem?_eq_getElem (by rw [utf16le_length, hlen_sub]; omega),
      utf16le_getElem_even _ j (by omega)]
    congr 1
    rw [hcharj, bv_extract0_or16]
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
    simp only [Nat.mul_add]
  · have hk_div : (2 * j + 1) / 2 = j := by omega
    have hcharj : (((strChars c d).drop b).take (e - b))[j]'(by omega) =
        (d[2 * (b + j)]'(by rw [hl, strByteLen_uncompressed hc]; omega)).toBitVec.zeroExtend 16 |||
          ((d[2 * (b + j) + 1]'(by rw [hl, strByteLen_uncompressed hc]; omega)).toBitVec.zeroExtend 16 <<< 8) := by
      simpa [hk_div] using hchar
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem]
    unfold getCharsBytes
    rw [List.getElem?_eq_getElem (by rw [utf16le_length, hlen_sub]; omega),
      utf16le_getElem_odd _ j (by omega)]
    congr 1
    rw [hcharj, bv_extract8_or16]
    apply Option.some_inj.mp
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
    simp only [Nat.mul_add, Nat.add_assoc]

theorem getCharsBytes_uncompressed_eq_drop_take {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    {b e : Nat} (hb : b ≤ e) (he : e ≤ (c >>> 1).toNat) :
    getCharsBytes c d b e = (d.drop (2 * b)).take (2 * (e - b)) := by
  have hl_take : ((d.drop (2 * b)).take (2 * (e - b))).length = 2 * (e - b) := by
    rw [List.length_take, List.length_drop, hl, strByteLen_uncompressed hc]; omega
  apply List.ext_getElem
  · rw [getCharsBytes_length c d hb he, hl_take]
  · intro k hk1 hk2
    have hk : k < 2 * (e - b) := by rw [getCharsBytes_length c d hb he] at hk1; exact hk1
    rw [getCharsBytes_uncompressed_getElem hc hl hb he k hk, List.getElem_take, List.getElem_drop]

/-! ## `Int.toBytes` and `BitVec.pmovzxbw` lemmas -/

theorem toBytes_ofInt_ofBytes (n : Nat) (bs : List UInt8) (hl : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  let x : BitVec (8 * n) := BitVec.ofInt (8 * n) (Int.ofBytes bs)
  have hround := BitVec.ofInt_ofBytes_toBytes (8 * n) n rfl x
  exact (ofInt_ofBytes_inj (8 * n) n rfl (Int.toBytes n x.toInt) bs
    (Int.toBytes_length _ _) hl).mp hround

theorem toBytes_zeroExtend16_byte (b : UInt8) :
    Int.toBytes 2 (b.toBitVec.zeroExtend 16).toInt = [b, 0] := by
  have hof : Int.ofBytes [b, 0] = (b.toNat : Int) := by
    simp [Int.ofBytes]
  have heq : b.toBitVec.zeroExtend 16 = BitVec.ofInt 16 (Int.ofBytes [b, 0]) := by
    rw [hof]
    apply BitVec.eq_of_toNat_eq
    have hlt : b.toNat < 2 ^ 8 := b.toBitVec.isLt
    change (b.toBitVec.setWidth 16).toNat = (BitVec.ofInt 16 (b.toNat : Int)).toNat
    rw [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofInt]
    rw [Nat.mod_eq_of_lt (by omega), Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  rw [heq]
  exact toBytes_ofInt_ofBytes 2 [b, 0] rfl

private theorem bv_getLsbD_ge_false {w : Nat} (v : BitVec w) {i : Nat} (hi : w ≤ i) :
    v.getLsbD i = false := by
  have hlt : v.toNat < 2 ^ i :=
    Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hi)
  simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

private theorem foldl_ofLanes16_getLsbD (w : Nat) (hw : w % 16 = 0) (f : Nat → BitVec 16)
    (m : Nat) (hm : m ≤ w / 16) (idx : Nat) (hidx : idx < w) :
    ((List.range m).foldl (fun a i => a ||| ((f i).setWidth w <<< (16 * i))) 0#w).getLsbD idx =
      (decide (idx / 16 < m) && (f (idx / 16)).getLsbD (idx % 16)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, ih (by omega), BitVec.getLsbD_shiftLeft]
    by_cases hle : 16 * m ≤ idx
    · by_cases hlt : idx - 16 * m < 16
      · have hdiv : idx / 16 = m := by omega
        have h1 : decide (idx / 16 < m) = false := decide_eq_false (by omega)
        have h2 : decide (idx / 16 < m + 1) = true := decide_eq_true (by omega)
        have h4 : decide (idx < 16 * m) = false := decide_eq_false (by omega)
        rw [h1, h2, h4, BitVec.getLsbD_setWidth, show idx - 16 * m = idx % 16 by omega,
          hdiv, decide_eq_true hidx, decide_eq_true (by omega : idx % 16 < w)]
        simp
      · have h1 : decide (idx / 16 < m) = false := decide_eq_false (by omega)
        have h2 : decide (idx / 16 < m + 1) = false := decide_eq_false (by omega)
        have hfl_ge : (f m).getLsbD (idx - 16 * m) = false :=
          bv_getLsbD_ge_false (f m) (by omega)
        rw [h1, h2, BitVec.getLsbD_setWidth, hfl_ge]
        simp
    · have h1 : decide (idx / 16 < m) = true := decide_eq_true (by omega)
      have h2 : decide (idx / 16 < m + 1) = true := decide_eq_true (by omega)
      have h4 : decide (idx < 16 * m) = true := decide_eq_true (by omega)
      simp [h1, h2, h4]

theorem ofLanes16_getLsbD (w : Nat) (hw : w % 16 = 0) (f : Nat → BitVec 16)
    (idx : Nat) (hidx : idx < w) :
    (BitVec.ofLanes w 16 f).getLsbD idx = (f (idx / 16)).getLsbD (idx % 16) := by
  unfold BitVec.ofLanes
  rw [foldl_ofLanes16_getLsbD w hw f (w / 16) (Nat.le_refl _) idx hidx]
  have : idx / 16 < w / 16 := by omega
  simp [this]

theorem pmovzxbw_eq_ofBytes (n : Nat) {w' : Nat} (_hn : 8 * n ≤ w') (a : BitVec w')
    (bs : List UInt8) (hbs : bs.length = n)
    (hlane : ∀ i (hi : i < n), a.lane 8 i = (bs[i]'(by omega)).toBitVec) :
    BitVec.pmovzxbw (16 * n) a = BitVec.ofInt (16 * n) (Int.ofBytes (expBytes bs)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro idx hidx
  rw [BitVec.pmovzxbw, ofLanes16_getLsbD (16 * n) (by omega) _ idx hidx]
  have hi_n : idx / 16 < n := by omega
  have hj_2n : idx / 8 < 2 * n := by omega
  rw [hlane (idx / 16) hi_n]
  have hbyte_exp : (BitVec.ofInt (16 * n) (Int.ofBytes (expBytes bs))).lane 8 (idx / 8) =
      ((expBytes bs)[idx / 8]'(by rw [expBytes_length, hbs]; exact hj_2n)).toBitVec := by
    rw [show 16 * n = 8 * (2 * n) by omega]
    exact lane_ofInt_ofBytes (2 * n) (expBytes bs) (by rw [expBytes_length, hbs]) (idx / 8) hj_2n
  have hbit_rhs : (BitVec.ofInt (16 * n) (Int.ofBytes (expBytes bs))).getLsbD idx =
      (((expBytes bs)[idx / 8]'(by rw [expBytes_length, hbs]; exact hj_2n)).toBitVec).getLsbD (idx % 8) := by
    have := congrArg (fun bv : BitVec 8 => bv.getLsbD (idx % 8)) hbyte_exp
    simpa [BitVec.lane, BitVec.getLsbD_extractLsb', show idx % 8 < 8 by omega,
      show 8 * (idx / 8) + idx % 8 = idx by omega] using this
  rw [hbit_rhs, expBytes_getElem bs (idx / 8) (by rw [hbs]; exact hj_2n)]
  simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, show idx % 16 < 16 by omega,
    decide_true, Bool.true_and]
  by_cases hlow : idx % 16 < 8
  · have heven : (idx / 8) % 2 = 0 := by omega
    have hdiv : (idx / 8) / 2 = idx / 16 := by omega
    have hmod : idx % 16 = idx % 8 := by omega
    simp [heven, hdiv, hmod]
  · have hodd : (idx / 8) % 2 ≠ 0 := by omega
    have hfalse : ((bs[idx / 16]'(by omega)).toBitVec).getLsbD (idx % 16) = false :=
      bv_getLsbD_ge_false _ (by omega)
    simp [hodd, hfalse]

theorem toBytes_pmovzxbw_256 (bs : List UInt8) (hbs : bs.length = 16) :
    Int.toBytes 32 (BitVec.pmovzxbw 256 (BitVec.ofInt 128 (Int.ofBytes bs))).toInt =
      expBytes bs := by
  have hp := pmovzxbw_eq_ofBytes 16 (by decide) (BitVec.ofInt 128 (Int.ofBytes bs)) bs hbs
    (fun i hi => by
      have := lane_ofInt_ofBytes 16 bs hbs i hi
      simpa using this)
  change Int.toBytes (2 * 16) (BitVec.pmovzxbw (16 * 16) _).toInt = _
  rw [hp]
  exact toBytes_ofInt_ofBytes 32 (expBytes bs) (by rw [expBytes_length, hbs])

theorem toBytes_pmovzxbw_128 (bs : List UInt8) (hbs : bs.length = 8) :
    Int.toBytes 16 (BitVec.pmovzxbw 128 (BitVec.ofInt 64 (Int.ofBytes bs))).toInt =
      expBytes bs := by
  have hp := pmovzxbw_eq_ofBytes 8 (by decide) (BitVec.ofInt 64 (Int.ofBytes bs)) bs hbs
    (fun i hi => by
      have := lane_ofInt_ofBytes 8 bs hbs i hi
      simpa using this)
  change Int.toBytes (2 * 8) (BitVec.pmovzxbw (16 * 8) _).toInt = _
  rw [hp]
  exact toBytes_ofInt_ofBytes 16 (expBytes bs) (by rw [expBytes_length, hbs])

theorem toBytes_pmovzxbw_64 (bs : List UInt8) (hbs : bs.length = 4) :
    Int.toBytes 8
      ((BitVec.pmovzxbw 128 ((BitVec.ofInt 32 (Int.ofBytes bs)).zeroExtend 128)).take 64).toInt =
      expBytes bs := by
  let a : BitVec 128 := (BitVec.ofInt 32 (Int.ofBytes bs)).zeroExtend 128
  have hlane : ∀ i (hi : i < 4), a.lane 8 i = (bs[i]'(by omega)).toBitVec := by
    intro i hi
    have h4 := lane_ofInt_ofBytes 4 bs hbs i hi
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hlt32 : 8 * i + b < 32 := by omega
    have hlt128 : 8 * i + b < 128 := by omega
    have hget := congrArg (fun bv : BitVec 8 => bv.getLsbD b) h4
    simp only [a, BitVec.lane, BitVec.getLsbD_extractLsb', BitVec.zeroExtend,
      BitVec.getLsbD_setWidth] at hget ⊢
    simpa [hb, hlt32, hlt128] using hget
  have hp64 : (BitVec.pmovzxbw 128 a).take 64 = BitVec.pmovzxbw 64 a := by
    apply BitVec.eq_of_getLsbD_eq
    intro idx hidx
    simp only [BitVec.take, BitVec.getLsbD_extractLsb', hidx, decide_true, Bool.true_and,
      Nat.zero_add, BitVec.pmovzxbw]
    rw [ofLanes16_getLsbD 128 (by decide) _ idx (by omega),
      ofLanes16_getLsbD 64 (by decide) _ idx hidx]
  have hp := pmovzxbw_eq_ofBytes 4 (by decide) a bs hbs hlane
  change Int.toBytes 8 ((BitVec.pmovzxbw 128 a).take 64).toInt = _
  rw [hp64, show (64 : Nat) = 16 * 4 by rfl, hp]
  exact toBytes_ofInt_ofBytes 8 (expBytes bs) (by rw [expBytes_length, hbs])

/-! ## Separation-memory slice and `bufReplace` helpers -/

/-- Replace the `[off, off + len)` slice of `buf` with `w`. -/
@[expose] def bufReplace (buf : List UInt8) (off len : Nat) (w : List UInt8) : List UInt8 :=
  buf.take off ++ w ++ buf.drop (off + len)

theorem bufReplace_length {buf w : List UInt8} {off len : Nat}
    (hle : off + len ≤ buf.length) (hw : w.length = len) :
    (bufReplace buf off len w).length = buf.length := by
  simp only [bufReplace, List.length_append, List.length_take, List.length_drop, hw]
  omega

theorem bufReplace_getElem {buf w : List UInt8} {off len : Nat}
    (hle : off + len ≤ buf.length) (hw : w.length = len)
    (j : Nat) (hj : j < buf.length) :
    (bufReplace buf off len w)[j]'(by rw [bufReplace_length hle hw]; exact hj) =
      if h : off ≤ j ∧ j < off + len then w[j - off]'(by omega) else buf[j]'hj := by
  apply Option.some_inj.mp
  rw [← List.getElem?_eq_getElem]
  have htake : (buf.take off).length = off := by simp [List.length_take]; omega
  unfold bufReplace
  by_cases h1 : j < off
  · have hn : ¬ (off ≤ j ∧ j < off + len) := by omega
    simp only [hn, ↓reduceDIte]
    rw [← List.getElem?_eq_getElem]
    rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take]
    simp [h1]
  · by_cases h2 : j < off + len
    · have hy : off ≤ j ∧ j < off + len := by omega
      simp only [hy.1, hy.2, and_self, ↓reduceDIte]
      rw [← List.getElem?_eq_getElem]
      rw [List.getElem?_append_left (by rw [List.length_append, htake, hw]; omega),
        List.getElem?_append_right (by omega), htake]
    · have hn : ¬ (off ≤ j ∧ j < off + len) := by omega
      simp only [hn, ↓reduceDIte]
      rw [← List.getElem?_eq_getElem]
      rw [List.getElem?_append_right (by rw [List.length_append, htake, hw]; omega),
        List.length_append, htake, hw, List.getElem?_drop]
      congr 1; omega

private theorem mem_sep_slice_of_at {bs : List UInt8} {addr : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (Eq (bs.At addr) ⋆ R) m) (hbound : bs.length ≤ 2 ^ 64)
    {off len : Nat} (hle : off + len ≤ bs.length) :
    ∃ R', (Eq (((bs.drop off).take len).At (addr + .ofNat 64 off)) ⋆ R') m := by
  let pre := bs.take off
  let mid := (bs.drop off).take len
  let post := bs.drop (off + len)
  have hpre_len : pre.length = off := by simp [pre, List.length_take]; omega
  have hmid_len : mid.length = len := by simp [mid, List.length_take, List.length_drop]; omega
  have hpost_len : post.length = bs.length - (off + len) := by simp [post, List.length_drop]
  have hsum : pre.length + (mid.length + post.length) ≤ 2 ^ 64 := by omega
  have hsplit : bs = pre ++ (mid ++ post) := by
    have h1 : bs.take off ++ bs.drop off = bs := List.take_append_drop off bs
    have h2 : (bs.drop off).take len ++ (bs.drop off).drop len = bs.drop off :=
      List.take_append_drop len (bs.drop off)
    have h3 : (bs.drop off).drop len = bs.drop (off + len) := by
      rw [List.drop_drop, Nat.add_comm]
    dsimp only [pre, mid, post]
    rw [← h3, h2, h1]
  rw [hsplit] at hm
  have happ1 := Mem.At_append_sep pre (mid ++ post) addr (by simp only [List.length_append]; exact hsum)
  have happ2 := Mem.At_append_sep mid post (addr + BitVec.ofNat 64 off) (by omega)
  rw [happ1, hpre_len, happ2] at hm
  rw [sep_assoc, sep_assoc] at hm
  rw [sep_comm_l] at hm
  exact ⟨_, hm⟩

theorem mem_expose_src_slice {s₀ : MachineData} {A : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {dstAddr : BitVec 64} {R : Mem 64 → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hl : d.length = strByteLen c) (hold : old.length = buf.length)
    (_hbuf_lt : buf.length < 2 ^ 64)
    {off len : Nat} (hle : off + len ≤ d.length) :
    ∃ Rs, (Eq (((d.drop off).take len).At (A + 16#64 + .ofNat 64 off)) ⋆ Rs)
      (s₀.dmem.storeBytes dstAddr buf) := by
  have hpad : padBytes d.length < 8 := by unfold padBytes; omega
  have hd_lt : d.length < 2 ^ 32 - 1 := by rw [hl]; exact strByteLen_lt c
  have hpad_bound : (padded d).length ≤ 2 ^ 64 := by simp [padded]; omega
  rw [sep_comm (StringAt A c d) (Eq (old.At dstAddr)), sep_assoc] at hmem
  have hstored : (Eq (buf.At dstAddr) ⋆ (StringAt A c d ⋆ R)) (s₀.dmem.storeBytes dstAddr buf) :=
    Mem.storeBytes_sep dstAddr buf.length old buf (StringAt A c d ⋆ R) s₀.dmem ⟨hmem, hold, rfl⟩
  rw [sep_comm_l] at hstored
  unfold StringAt at hstored
  rw [sep_assoc, sep_comm_l] at hstored
  have hstr : (Eq ((padded d).At (A + 16#64)) ⋆
      (Eq ((Int.toBytes 4 c.toInt).At (A + 8#64)) ⋆ (Eq (buf.At dstAddr) ⋆ R)))
      (s₀.dmem.storeBytes dstAddr buf) := by
    simpa [padded] using hstored
  obtain ⟨R', hslice⟩ := mem_sep_slice_of_at hstr hpad_bound (off := off) (len := len) (by simp [padded]; omega)
  have hslice_eq : ((padded d).drop off).take len = (d.drop off).take len := by
    apply List.ext_getElem
    · simp [padded, List.length_take, List.length_drop]; omega
    · intro i hi1 hi2
      simp only [padded, List.getElem_take, List.getElem_drop]
      exact List.getElem_append_left (by simp [List.length_take, List.length_drop] at hi2; omega)
  rw [hslice_eq] at hslice
  exact ⟨R', hslice⟩

theorem mem_loadInt_src_slice {s₀ : MachineData} {A : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {dstAddr : BitVec 64} {R : Mem 64 → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hl : d.length = strByteLen c) (hold : old.length = buf.length)
    (hbuf_lt : buf.length < 2 ^ 64)
    {off len : Nat} (hle : off + len ≤ d.length) (hpow : len ≤ 2 ^ 64) :
    (s₀.dmem.storeBytes dstAddr buf).loadInt (A + 16#64 + .ofNat 64 off) len =
      some (Int.ofBytes ((d.drop off).take len)) := by
  obtain ⟨Rs, hRs⟩ := mem_expose_src_slice hmem hl hold hbuf_lt hle
  exact Mem.loadInt_sep _ _ len Rs _ hRs
    (by simp [List.length_take, List.length_drop]; omega) hpow

theorem mem_expose_dst_slice {s₀ : MachineData} {A : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {dstAddr : BitVec 64} {R : Mem 64 → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hold : old.length = buf.length) (hbuf_bound : buf.length ≤ 2 ^ 64)
    {off len : Nat} (hle : off + len ≤ buf.length) :
    ∃ R', (Eq (((buf.drop off).take len).At (dstAddr + .ofNat 64 off)) ⋆ R')
      (s₀.dmem.storeBytes dstAddr buf) := by
  rw [sep_comm (StringAt A c d) (Eq (old.At dstAddr)), sep_assoc] at hmem
  have hstored : (Eq (buf.At dstAddr) ⋆ (StringAt A c d ⋆ R)) (s₀.dmem.storeBytes dstAddr buf) :=
    Mem.storeBytes_sep dstAddr buf.length old buf (StringAt A c d ⋆ R) s₀.dmem ⟨hmem, hold, rfl⟩
  exact mem_sep_slice_of_at hstored hbuf_bound hle

theorem storeInt_bufReplace {m : Mem 64} {dstAddr : BitVec 64} {buf : List UInt8}
    {off len : Nat} (hle : off + len ≤ buf.length) (hbound : buf.length ≤ 2 ^ 64)
    (v : Int) :
    (m.storeBytes dstAddr buf).storeInt (dstAddr + .ofNat 64 off) len v =
      m.storeBytes dstAddr (bufReplace buf off len (Int.toBytes len v)) := by
  unfold Mem.storeInt bufReplace
  let pre := buf.take off
  let mid := (buf.drop off).take len
  let post := buf.drop (off + len)
  have hpre_len : pre.length = off := by simp [pre, List.length_take]; omega
  have hmid_len : mid.length = len := by simp [mid, List.length_take, List.length_drop]; omega
  have hpost_len : post.length = buf.length - (off + len) := by simp [post, List.length_drop]
  have hsplit : buf = pre ++ mid ++ post := by
    have h1 : buf.take off ++ buf.drop off = buf := List.take_append_drop off buf
    have h2 : (buf.drop off).take len ++ (buf.drop off).drop len = buf.drop off :=
      List.take_append_drop len (buf.drop off)
    have h3 : (buf.drop off).drop len = buf.drop (off + len) := by
      rw [List.drop_drop, Nat.add_comm]
    dsimp only [pre, mid, post]
    rw [List.append_assoc, ← h3, h2, h1]
  have hbound' : pre.length + mid.length + post.length ≤ 2 ^ 64 := by omega
  have hmb : m.storeBytes dstAddr buf = m.storeBytes dstAddr (pre ++ mid ++ post) :=
    congrArg (m.storeBytes dstAddr) hsplit
  have hbuf_eq : pre ++ Int.toBytes len v ++ post =
      buf.take off ++ Int.toBytes len v ++ buf.drop (off + len) := rfl
  rw [hmb, ← hbuf_eq, ← hpre_len]
  exact Mem.storeBytes_splice m dstAddr pre mid post (Int.toBytes len v)
    (by simp [Int.toBytes_length, hmid_len]) hbound'

theorem load_string_count_sep {s₀ : MachineData} {A : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {dstAddr : BitVec 64} {R : Mem 64 → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hold : old.length = buf.length) :
    ∃ Rc, (Eq ((Int.toBytes 4 c.toInt).At (A + 8#64)) ⋆ Rc) (s₀.dmem.storeBytes dstAddr buf) := by
  rw [sep_comm (StringAt A c d) (Eq (old.At dstAddr)), sep_assoc] at hmem
  have hstored : (Eq (buf.At dstAddr) ⋆ (StringAt A c d ⋆ R)) (s₀.dmem.storeBytes dstAddr buf) :=
    Mem.storeBytes_sep dstAddr buf.length old buf (StringAt A c d ⋆ R) s₀.dmem ⟨hmem, hold, rfl⟩
  rw [sep_comm_l] at hstored
  unfold StringAt at hstored
  rw [sep_assoc] at hstored
  exact ⟨_, hstored⟩

/-! ## Flag, alignment, and ZMM framing lemmas -/

theorem bitvec32_and_one_eq_zero (c : BitVec 32) :
    (c &&& 1#32 == 0#32) = !c.getLsbD 0 := by bv_decide

theorem test_and1_of_count (c : BitVec 32) :
    (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 c.toInt)) &&& 1#32 == 0#32) = !c.getLsbD 0 := by
  rw [BitVec.ofInt_ofBytes_toBytes 32 4 rfl c]
  exact bitvec32_and_one_eq_zero c

theorem ofNat32_sub_eq_zero {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0#32) = decide (x = y) := by
  rw [sub_beq_zero]
  by_cases h : x = y
  · subst h; simp
  · have hne : BitVec.ofNat 32 x ≠ BitVec.ofNat 32 y := fun heq => by
      have := congrArg BitVec.toNat heq
      simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
      exact h this
    rw [beq_eq_false_iff_ne.mpr hne]; simp [h]

theorem jbe_ofNat32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    ((BitVec.ofNat 32 x - BitVec.ofNat 32 y).unsigned !=
      (BitVec.ofNat 32 x).unsigned - (BitVec.ofNat 32 y).unsigned ||
      (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0#32)) = decide (x ≤ y) := by
  rw [cf_ofNat32 hx hy, ofNat32_sub_eq_zero hx hy]
  by_cases hlt : x < y <;> by_cases heq : x = y
  · omega
  · simp [hlt, heq] <;> omega
  · simp [heq]
  · simp [hlt, heq] <;> omega

theorem ja_ofNat32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (!(BitVec.ofNat 32 x - BitVec.ofNat 32 y).unsigned !=
      (BitVec.ofNat 32 x).unsigned - (BitVec.ofNat 32 y).unsigned &&
      !(BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0#32)) = decide (y < x) := by
  rw [cf_ofNat32 hx hy, ofNat32_sub_eq_zero hx hy]
  by_cases hlt : x < y <;> by_cases heq : x = y
  · omega
  · simp [hlt, heq] <;> omega
  · simp [heq]
  · simp [hlt, heq] <;> omega

theorem sub64_add64_ofNat32 (n : Nat) :
    (BitVec.ofNat 32 n - 64#32) + 64#32 = BitVec.ofNat 32 n := by
  bv_decide

theorem align32_even_props (p0 : BitVec 64) (hp0 : p0.getLsbD 0 = false) :
    let t := -((p0.setWidth 32 &&& 31#32) - 32#32)
    let sh := (t >>> 1).toNat
    1 ≤ sh ∧ sh ≤ 16 ∧ t = BitVec.ofNat 32 (2 * sh) ∧ (t >>> 1) = BitVec.ofNat 32 sh := by
  have hp32 : (p0.setWidth 32).getLsbD 0 = false := by simpa using hp0
  have hbv : ∀ x : BitVec 32, x.getLsbD 0 = false →
      let t := -((x &&& 31#32) - 32#32)
      2#32 ≤ t ∧ t ≤ 32#32 ∧ (t >>> 1) * 2#32 = t := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩ <;> bv_decide
  obtain ⟨hle2, hle32, hmul⟩ := hbv (p0.setWidth 32) hp32
  have hlo : 2 ≤ (-((p0.setWidth 32 &&& 31#32) - 32#32)).toNat := by
    simpa [BitVec.le_def] using hle2
  have hhi : (-((p0.setWidth 32 &&& 31#32) - 32#32)).toNat ≤ 32 := by
    simpa [BitVec.le_def] using hle32
  dsimp only
  generalize -((p0.setWidth 32 &&& 31#32) - 32#32) = t at hlo hhi hmul ⊢
  have hsh_def : (t >>> 1).toNat = t.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hmul_nat := congrArg BitVec.toNat hmul
  rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 by rfl, hsh_def] at hmul_nat
  have hmul_eq : t.toNat / 2 * 2 = t.toNat := by
    rw [Nat.mod_eq_of_lt (by omega)] at hmul_nat; exact hmul_nat
  refine ⟨by omega, by omega, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp [hsh_def, show 2 * (t.toNat / 2) = t.toNat by omega]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (t >>> 1).isLt]

/-- Frame invariant on `RegZmms`: registers outside `ymm0.base` and `ymm1.base` match `s₀.zmms`. -/
@[expose] def ZmmsFrame (ymm0 ymm1 : AvxReg .W256) (s₀ : MachineData) (z : RegZmms) : Prop :=
  ∀ r : RegMm, r ≠ ymm0.base → r ≠ ymm1.base → z.get512 r = s₀.zmms.get512 r

theorem zmmsFrame_refl (ymm0 ymm1 : AvxReg .W256) (s₀ : MachineData) :
    ZmmsFrame ymm0 ymm1 s₀ s₀.zmms := fun _ _ _ => rfl

theorem zmmsFrame_set_ymm0 {ymm0 ymm1 : AvxReg .W256} {s₀ : MachineData} {z : RegZmms}
    (h : ZmmsFrame ymm0 ymm1 s₀ z) (v : BitVec 256) :
    ZmmsFrame ymm0 ymm1 s₀ (z.set ymm0 v) := by
  intro r hr0 hr1
  cases ymm0 with | ymm b0 =>
  change (z.set512 b0 (v.zeroExtend 512)).get512 r = s₀.zmms.get512 r
  rw [get512_set512]
  have hne : r ≠ b0 := hr0
  simp [hne, h r hr0 hr1]

theorem zmmsFrame_set_ymm1 {ymm0 ymm1 : AvxReg .W256} {s₀ : MachineData} {z : RegZmms}
    (h : ZmmsFrame ymm0 ymm1 s₀ z) (v : BitVec 256) :
    ZmmsFrame ymm0 ymm1 s₀ (z.set ymm1 v) := by
  intro r hr0 hr1
  cases ymm1 with | ymm b1 =>
  change (z.set512 b1 (v.zeroExtend 512)).get512 r = s₀.zmms.get512 r
  rw [get512_set512]
  have hne : r ≠ b1 := hr1
  simp [hne, h r hr0 hr1]

theorem zmmsFrame_set_xmm0 {ymm0 ymm1 : AvxReg .W256} {s₀ : MachineData} {z : RegZmms}
    (h : ZmmsFrame ymm0 ymm1 s₀ z) (v : BitVec 128) :
    ZmmsFrame ymm0 ymm1 s₀ (z.set (.xmm ymm0.base) v) := by
  intro r hr0 hr1
  change (z.set512 ymm0.base (v.zeroExtend 512)).get512 r = s₀.zmms.get512 r
  rw [get512_set512]
  simp [hr0, h r hr0 hr1]

private theorem take128_take256_ze512 (x : BitVec 512) :
    ((((x.take 256).zeroExtend 512).take 128).zeroExtend 512 : BitVec 512) =
      ((x.take 128).zeroExtend 512) := by
  simp only [BitVec.take]; bv_decide

theorem zmmsFrame_zeroUpper (ymm0 ymm1 : AvxReg .W256)
    (h0 : ymm0.base ∈ lowMm) (h1 : ymm1.base ∈ lowMm) (hne : ymm0.base ≠ ymm1.base)
    {s₀ : MachineData} {z : RegZmms} (h : ZmmsFrame ymm0 ymm1 s₀ z) :
    ∃ vs, z.zeroUpper = (s₀.zmms.setAll [ymm0, ymm1] vs).zeroUpper := by
  refine ⟨[z.get ymm0, z.get ymm1], ?_⟩
  apply regZmms_ext
  intro r
  simp only [RegZmms.setAll]
  by_cases hlow : r ∈ lowMm
  · rw [get512_zeroUpper_low z hlow, get512_zeroUpper_low _ hlow]
    by_cases hr1 : r = ymm1.base
    · subst hr1
      cases ymm1 with | ymm b1 =>
      simp only [AvxReg.base] at *
      have hg : ((s₀.zmms.set ymm0 (z.get ymm0)).set (.ymm b1) (z.get (.ymm b1))).get512 b1 =
          (z.get (.ymm b1)).zeroExtend 512 := by
        simp [RegZmms.set, get512_set512]
      rw [hg]
      change ((z.get512 b1).take 128).zeroExtend 512 = _
      exact (take128_take256_ze512 (z.get512 b1)).symm
    · by_cases hr0 : r = ymm0.base
      · subst hr0
        cases ymm0 with | ymm b0 =>
        cases ymm1 with | ymm b1 =>
        simp only [AvxReg.base] at *
        have hg : ((s₀.zmms.set (.ymm b0) (z.get (.ymm b0))).set (.ymm b1) (z.get (.ymm b1))).get512 b0 =
            (z.get (.ymm b0)).zeroExtend 512 := by
          simp [RegZmms.set, get512_set512, hne]
        rw [hg]
        change ((z.get512 b0).take 128).zeroExtend 512 = _
        exact (take128_take256_ze512 (z.get512 b0)).symm
      · cases ymm0 with | ymm b0 =>
        cases ymm1 with | ymm b1 =>
        simp only [AvxReg.base] at *
        have hg : ((s₀.zmms.set (.ymm b0) (z.get (.ymm b0))).set (.ymm b1) (z.get (.ymm b1))).get512 r =
            s₀.zmms.get512 r := by
          simp [RegZmms.set, get512_set512, hr0, hr1]
        rw [hg, h r hr0 hr1]
  · rw [get512_zeroUpper_high z hlow, get512_zeroUpper_high _ hlow]
    have hr0 : r ≠ ymm0.base := fun heq => hlow (heq ▸ h0)
    have hr1 : r ≠ ymm1.base := fun heq => hlow (heq ▸ h1)
    cases ymm0 with | ymm b0 =>
    cases ymm1 with | ymm b1 =>
    simp only [AvxReg.base] at *
    have hg : ((s₀.zmms.set (.ymm b0) (z.get (.ymm b0))).set (.ymm b1) (z.get (.ymm b1))).get512 r =
        s₀.zmms.get512 r := by
      simp [RegZmms.set, get512_set512, hr0, hr1]
    rw [hg, h r hr0 hr1]

end GetCharsProof

end

end Kraken.X64.Art
