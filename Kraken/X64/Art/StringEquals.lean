module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
import Kraken.X64.Parser
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

open Std
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/-- ART `String.count_`: length << 1 | flag, flag 0 = compressed (1B/char), 1 = uncompressed (2B/char). -/
@[expose] def strByteLen (count : BitVec 32) : Nat :=
  if count.getLsbD 0 then 2 * (count >>> 1).toNat else (count >>> 1).toNat

/-- Zero-padded byte count in the string object (`kObjectAlignment = 8`). -/
@[expose] def padBytes (len : Nat) : Nat := (8 - (len % 8)) % 8

/-- Total allocated data bytes of the string, including 8-byte zero-padding. -/
@[expose] def allocatedBytes (len : Nat) : Nat := len + padBytes len

/--
A valid ART String object in memory:
- 32-bit `count_` field at `p + 8`
- byte payload `data` followed by `padBytes data.length` zeroes at `p + 16`
-/
@[expose] def StringAt (p : BitVec 64) (count : BitVec 32) (data : List UInt8) : Mem 64 → Prop :=
  Eq ((Int.toBytes 4 count.toInt).At (p + 8#64)) ⋆
  Eq ((data ++ List.replicate (padBytes data.length) (0 : UInt8)).At (p + 16#64))

/-- Java `String.equals` specification: two strings are equal iff their count fields and byte payloads match. -/
@[expose] def stringEquals (s₁ s₂ : BitVec 64) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8) : Bool :=
  s₁ == s₂ || (c₁ == c₂ && d₁ == d₂)

/--
Memory condition for two string references `s₁` and `s₂`:
either they point to the same object, or to two disjoint string objects in memory,
framed by `R`.
-/
@[expose] def StringsInMem (s₁ s₂ : BitVec 64) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  if s₁ = s₂ then
    c₁ = c₂ ∧ d₁ = d₂ ∧ (m =⋆ StringAt s₁ c₁ d₁ ⋆ R)
  else
    m =⋆ StringAt s₁ c₁ d₁ ⋆ StringAt s₂ c₂ d₂ ⋆ R

/--
Specification postcondition: `t` is `{ s with ... }` where `dmem` is unchanged,
`out` holds the boolean result, `n` and `off` hold scratch values, and `zmms` are
either preserved (on early exit) or zero-uppered with `ymm` clobbered (after `vzeroupper`).
-/
@[expose] def StringEqualsPost (str arg n off out : Reg64) (ymm : AvxReg .W256)
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8) (s t : MachineData) : Prop :=
  let res : BitVec 64 := if stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ then 1#64 else 0#64
  ∃ (vn voff : BitVec 64) (zmms : RegZmms) (flags : StatusFlags),
    (zmms = s.zmms ∨ ∃ vymm, zmms = (s.zmms.set ymm vymm).zeroUpper) ∧
    t = { s with
      regs := ((s.regs.set64 n vn).set64 off voff).set64 out res,
      zmms := zmms,
      status := flags }

/--
Parameterized assembly template for AVX2 String.equals.
Uses vector register `ymm` and core registers `str`, `arg`, `n`, `off`, `out`.
-/
@[expose] def stringEqualsProg (str arg n off out : Reg64) (ymm : AvxReg .W256) : _root_.Program := parse("
    # 1. Reference equality check: if str == arg return true
    cmpl %❰.low arg .W32❱, %❰.low str .W32❱
    je return_true

    # 2. Load and compare count_ fields: if count(str) != count(arg) return false
    movl 8(%❰str❱), %❰.low n .W32❱
    cmpl 8(%❰arg❱), %❰.low n .W32❱
    jne return_false

    # 3. If count == 0 return true
    testl %❰.low n .W32❱, %❰.low n .W32❱
    je return_true

    # 4. Convert count to byte length n: if bit 0 is 1 (uncompressed) then n &= ~1 else n >>= 1
    testl $1, %❰.low n .W32❱
    jne uncompressed
    shrl $1, %❰.low n .W32❱
    jmp len_done
  uncompressed:
    andl $-2, %❰.low n .W32❱
  len_done:

    # 5. off = 0
    xorq %❰.low off .W64❱, %❰.low off .W64❱

    # 6. Check if n >= 32
    cmpl $32, %❰.low n .W32❱
    jb short

  # 7. AVX loop: compare 32 bytes per iteration
  avx_loop:
    vmovdqu 16(%❰str❱,%❰off❱,1), %❰ymm❱
    vpcmpeqb 16(%❰arg❱,%❰off❱,1), %❰ymm❱, %❰ymm❱
    vpmovmskb %❰ymm❱, %❰.low out .W32❱
    cmpl $-1, %❰.low out .W32❱
    jne return_false_vzero
    addq $32, %❰.low off .W64❱
    subl $32, %❰.low n .W32❱
    cmpl $32, %❰.low n .W32❱
    jae avx_loop

  # 8. Short tail: qwords remaining = (n + 7) / 8
  short:
    addl $7, %❰.low n .W32❱
    shrl $3, %❰.low n .W32❱
    je return_true_vzero

  qword_loop:
    movq 16(%❰str❱,%❰off❱,1), %❰.low out .W64❱
    cmpq 16(%❰arg❱,%❰off❱,1), %❰.low out .W64❱
    jne return_false_vzero
    addq $8, %❰.low off .W64❱
    subl $1, %❰.low n .W32❱
    jne qword_loop

  # 9. Return true with vzeroupper
  return_true_vzero:
    vzeroupper
  return_true:
    movl $1, %❰.low out .W32❱
    jmp end

  # 10. Return false with vzeroupper
  return_false_vzero:
    vzeroupper
  return_false:
    xorl %❰.low out .W32❱, %❰.low out .W32❱
  end:
")

/-! ## Proof of `stringEquals_correct` -/

namespace Proof


theorem get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

theorem get_low32 (s : Reg64s) (r : Reg64) : s.get (.low r .W32) = (s.get64 r).setWidth 32 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Width.bits]
  ext i hi; simp

theorem get_low64 (s : Reg64s) (r : Reg64) : s.get (.low r .W64) = s.get64 r := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Width.bits]
  ext i hi; simp

theorem set_low32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    s.set (.low r .W32) v = s.set64 r (v.setWidth 64) := rfl

theorem set_low64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    s.set (.low r .W64) v = s.set64 r v := rfl

theorem get512_set512 (s : RegZmms) (r r' : RegMm) (v : BitVec 512) :
    (s.set512 r v).get512 r' = if r' = r then v else s.get512 r' := by
  cases r <;> cases r' <;> simp [RegZmms.set512, RegZmms.get512] <;> rfl

theorem zeroUpper_take128 (s : RegZmms) (r : RegMm) :
    (s.zeroUpper.get512 r).take 128 = (s.get512 r).take 128 := by
  have h : ∀ x : BitVec 512,
      BitVec.extractLsb' 0 128 (BitVec.setWidth 512 (BitVec.extractLsb' 0 128 x)) =
        BitVec.extractLsb' 0 128 x := by
    intro x; bv_decide
  cases r <;> simp [RegZmms.zeroUpper, RegZmms.set512, RegZmms.get512, BitVec.take] <;> exact h _

theorem pmovmskb_pcmpeqb (x y : BitVec 256) :
    BitVec.pmovmskb (BitVec.pcmpeqb x y) = -1#32 ↔ x = y := by
  simp only [BitVec.pmovmskb, BitVec.pcmpeqb, BitVec.ofLanes, BitVec.lane, List.range,
    List.range.loop, List.foldl, Nat.reduceDiv, beq_iff_eq]
  bv_decide

theorem addr_base_disp [Labels] (regs : Reg64s) (r : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := none, disp := .int64 d } regs p).zeroExtend 64 =
      regs.get64 r + d.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Width.bits, Int.add_zero]
  rw [BitVec.ofInt_add, BitVec.extractLsb'_eq_self, BitVec.ofInt_toInt, ← Int64.toInt_toBitVec,
    BitVec.ofInt_toInt]
  simp

theorem addr_sib1_disp [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W8⟩, disp := .int64 d } regs p).zeroExtend 64 =
      regs.get64 r + regs.get64 i + d.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Width.bits, Width.bytes]
  rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.extractLsb'_eq_self, BitVec.ofInt_toInt,
    ← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  simp

theorem addr_base_disp' [Labels] (regs : Reg64s) (r : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := none, disp := .int64 d } regs p : BitVec 64) =
      regs.get64 r + d.toBitVec := by
  have := addr_base_disp regs r d p
  simpa using this

theorem addr_sib1_disp' [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W8⟩, disp := .int64 d } regs p : BitVec 64) =
      regs.get64 r + regs.get64 i + d.toBitVec := by
  have := addr_sib1_disp regs r i d p
  simpa using this

theorem loadInt_eq (m : Mem 64) (a : BitVec 64) (n : Nat)
    (h : ∀ i < n, (m[a + .ofNat 64 i]?).isSome) :
    m.loadInt a n = some (Int.ofBytes ((List.range n).map fun i => (m[a + .ofNat 64 i]?).getD 0)) := by
  rw [Mem.loadInt, Mem.loadBytes, List.map_congr_left (g := fun i => some ((m[a + .ofNat 64 i]?).getD 0))
    (fun i hi => ?_)]
  · simp [List.allSome, ← Option.pure_def, List.mapM_pure]; rfl
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i (List.mem_range.mp hi))
    simp [Std.ExtHashMap.get?_eq_getElem?, hv]

theorem ofInt_ofBytes_inj (w n : Nat) (hw : w = 8 * n) (l₁ l₂ : List UInt8)
    (h₁ : l₁.length = n) (h₂ : l₂.length = n) :
    BitVec.ofInt w (Int.ofBytes l₁) = BitVec.ofInt w (Int.ofBytes l₂) ↔ l₁ = l₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hlt₁ := Int.ofBytes_lt l₁
  have hlt₂ := Int.ofBytes_lt l₂
  have hge₁ := Int.ofBytes_ge_zero l₁
  have hge₂ := Int.ofBytes_ge_zero l₂
  have hpow : (256 : Int) ^ n = 2 ^ w := by
    rw [hw, Int.pow_mul]; rfl
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt] at h'
  rw [h₁, hpow] at hlt₁
  rw [h₂, hpow] at hlt₂
  have e : Int.ofBytes l₁ = Int.ofBytes l₂ := by
    have := Int.emod_eq_of_lt hge₁ hlt₁
    have := Int.emod_eq_of_lt hge₂ hlt₂
    have hh : (Int.ofBytes l₁ % 2 ^ w).toNat = (Int.ofBytes l₂ % 2 ^ w).toNat := by
      exact_mod_cast h'
    omega
  have := Int.toBytes_ofBytes n l₁ (by omega)
  have := Int.toBytes_ofBytes n l₂ (by omega)
  rw [List.take_of_length_le (by omega)] at *
  grind

theorem i64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

theorem sub_beq_zero {w : Nat} (a b : BitVec w) : (a - b == 0#w) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0#w := fun h' => h (by
      have := BitVec.sub_add_cancel a b; rw [h', BitVec.zero_add] at this; exact this.symm)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem ofNat_succ_sub_one (m : Nat) : BitVec.ofNat 32 (m + 1) - 1#32 = BitVec.ofNat 32 m := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem ofNat_add_lit (k c : Nat) : BitVec.ofNat 64 c + BitVec.ofNat 64 k = BitVec.ofNat 64 (k + c) := by
  rw [BitVec.ofNat_add]; ac_rfl

theorem ofNat32_add_lit (k c : Nat) : BitVec.ofNat 32 k + BitVec.ofNat 32 c = BitVec.ofNat 32 (k + c) := by
  rw [BitVec.ofNat_add]

theorem ofNat32_sub_lit {r c : Nat} (h : c ≤ r) : BitVec.ofNat 32 r - BitVec.ofNat 32 c = BitVec.ofNat 32 (r - c) := by
  conv => lhs; rw [show r = (r - c) + c by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem ofNat32_eq_zero {m : Nat} (hm : m < 2 ^ 32) : (BitVec.ofNat 32 m == 0#32) = (m == 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 m ≠ 0#32 := fun h' => h (by
      have := congrArg BitVec.toNat h'; simp at this; omega)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem ofNat32_ushiftRight {x : Nat} (hx : x < 2 ^ 32) (c : Nat) :
    (BitVec.ofNat 32 x).ushiftRight c = BitVec.ofNat 32 (x / 2 ^ c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]
  rw [Nat.mod_eq_of_lt (by exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem cf_ofNat32 {x c : Nat} (hx : x < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.unsigned (BitVec.ofNat 32 x - BitVec.ofNat 32 c) !=
      BitVec.unsigned (BitVec.ofNat 32 x) - BitVec.unsigned (BitVec.ofNat 32 c)) = decide (x < c) := by
  simp only [BitVec.unsigned, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hc]
  by_cases h : x < c
  · have : (2 ^ 32 - c + x) % 2 ^ 32 = 2 ^ 32 - c + x := Nat.mod_eq_of_lt (by omega)
    simp [h, this] <;> omega
  · have : (2 ^ 32 - c + x) % 2 ^ 32 = x - c := by
      rw [show 2 ^ 32 - c + x = (x - c) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [h, this] <;> omega

theorem sw32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  ext i hi; simp

theorem sw32_ofNat (c : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 c) = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd c (by decide)

theorem cnt1 : (BitVec.extractLsb' 0 8 1#64).toNat &&& 31 = 1 := by decide
theorem cnt3 : (BitVec.extractLsb' 0 8 3#64).toNat &&& 31 = 3 := by decide

theorem sw_m1 : BitVec.setWidth 32 (-1#64) = -1#32 := by decide

theorem pm_self (y : BitVec 256) : BitVec.pmovmskb (BitVec.pcmpeqb y y) = -1#32 :=
  (pmovmskb_pcmpeqb y y).mpr rfl

theorem prefix_ext {P : Nat → Prop} {k w : Nat} (hpre : ∀ i < k, P i) (heq : ∀ j < w, P (k + j)) :
    ∀ i < k + w, P i := fun i hi =>
  if h : i < k then hpre i h else by
    have := heq (i - k) (by omega); rwa [Nat.add_sub_cancel' (by omega)] at this

theorem reg64s_ext {a b : Reg64s} (h : ∀ r, a.get64 r = b.get64 r) : a = b := by
  cases a; cases b
  simp only [Reg64s.mk.injEq]
  exact ⟨UInt64.toBitVec_inj.mp (h .rax), UInt64.toBitVec_inj.mp (h .rbx),
    UInt64.toBitVec_inj.mp (h .rcx), UInt64.toBitVec_inj.mp (h .rdx),
    UInt64.toBitVec_inj.mp (h .rsi), UInt64.toBitVec_inj.mp (h .rdi),
    UInt64.toBitVec_inj.mp (h .rsp), UInt64.toBitVec_inj.mp (h .rbp),
    UInt64.toBitVec_inj.mp (h .r8), UInt64.toBitVec_inj.mp (h .r9),
    UInt64.toBitVec_inj.mp (h .r10), UInt64.toBitVec_inj.mp (h .r11),
    UInt64.toBitVec_inj.mp (h .r12), UInt64.toBitVec_inj.mp (h .r13),
    UInt64.toBitVec_inj.mp (h .r14), UInt64.toBitVec_inj.mp (h .r15)⟩

theorem regZmms_ext {a b : RegZmms} (h : ∀ r, a.get512 r = b.get512 r) : a = b := by
  cases a; cases b
  simp only [RegZmms.mk.injEq]
  exact ⟨h .mm0, h .mm1, h .mm2, h .mm3, h .mm4, h .mm5, h .mm6, h .mm7, h .mm8, h .mm9, h .mm10,
    h .mm11, h .mm12, h .mm13, h .mm14, h .mm15, h .mm16, h .mm17, h .mm18, h .mm19, h .mm20,
    h .mm21, h .mm22, h .mm23, h .mm24, h .mm25, h .mm26, h .mm27, h .mm28, h .mm29, h .mm30, h .mm31⟩

/-- The registers whose upper bits `vzeroupper` clears. -/
abbrev lowMm : List RegMm := [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10,
  .mm11, .mm12, .mm13, .mm14, .mm15]

theorem get512_zeroUpper_low (z : RegZmms) {r : RegMm} (hr : r ∈ lowMm) :
    z.zeroUpper.get512 r = ((z.get512 r).take 128).setWidth 512 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [RegZmms.zeroUpper, RegZmms.set512, RegZmms.get512]

theorem get512_zeroUpper_high (z : RegZmms) {r : RegMm} (hr : r ∉ lowMm) :
    z.zeroUpper.get512 r = z.get512 r := by
  cases r <;> simp at hr <;> simp [RegZmms.zeroUpper, RegZmms.set512, RegZmms.get512] <;> rfl

theorem zmms_set_set (z : RegZmms) (y : AvxReg .W256) (u v : BitVec 256) :
    (z.set y u).set y v = z.set y v := by
  cases y with
  | ymm r => cases r <;> rfl

theorem zmms_get_set (z : RegZmms) (y : AvxReg .W256) (v : BitVec 256) : (z.set y v).get y = v := by
  cases y with
  | ymm r =>
    simp only [RegZmms.get, RegZmms.set, get512_set512, AvxReg.base, ↓reduceIte, BitVec.take]
    ext i hi; simp only [AvxWidth.bits] at hi; simp [hi]; intro; omega

theorem zeroUpper_set_get (z : RegZmms) (y : AvxReg .W256) (h : y.base ∈ lowMm) :
    (z.set y (z.get y)).zeroUpper = z.zeroUpper := by
  have hb : ∀ x : BitVec 512, ((((x.take 256).setWidth 512).take 128).setWidth 512 : BitVec 512) =
      ((x.take 128).setWidth 512) := by
    intro x; simp only [BitVec.take]; bv_decide
  apply regZmms_ext; intro r
  cases y with
  | ymm b =>
    simp only [AvxReg.base] at h
    by_cases hr : r = b
    · subst hr
      rw [get512_zeroUpper_low _ h, get512_zeroUpper_low _ h]
      simp only [RegZmms.set, RegZmms.get, AvxReg.base, get512_set512, ↓reduceIte]
      exact hb _
    · by_cases hl : r ∈ lowMm
      · rw [get512_zeroUpper_low _ hl, get512_zeroUpper_low _ hl]
        simp [RegZmms.set, get512_set512, hr]
      · rw [get512_zeroUpper_high _ hl, get512_zeroUpper_high _ hl]
        simp [RegZmms.set, get512_set512, hr]

/-! ## Separation logic: reading bytes -/

theorem sep_get_r {P Q : Mem 64 → Prop} {m : Mem 64} {k : BitVec 64} {v : UInt8}
    (h : (P ⋆ Q) m) (hQ : ∀ m₂, Q m₂ → m₂[k]? = some v) : m[k]? = some v := by
  obtain ⟨a, b, rfl, -, -, hb⟩ := h
  rw [union_eq, getElem?_union, hQ b hb]; rfl

theorem sep_get_l {P Q : Mem 64 → Prop} {m : Mem 64} {k : BitVec 64} {v : UInt8}
    (h : (P ⋆ Q) m) (hP : ∀ m₁, P m₁ → m₁[k]? = some v) : m[k]? = some v := by
  obtain ⟨a, b, rfl, hi, ha, -⟩ := h
  have hka := hP a ha
  have hkb : b[k]? = none := by
    apply getElem?_eq_none
    intro hb
    have : k ∈ a.inter b := by
      rw [inter_eq, mem_inter_iff]; exact ⟨mem_iff_isSome_getElem?.mpr (by simp [hka]), hb⟩
    rw [hi] at this; simp at this
  rw [union_eq, getElem?_union, hkb, hka]; rfl

theorem at_get (bs : List UInt8) (a : BitVec 64) {i : Nat} (hi : i < bs.length) (hl : bs.length ≤ 2 ^ 64) :
    ∀ m, Eq (bs.At a) m → m[a + .ofNat 64 i]? = some bs[i] := by
  rintro m rfl
  have := get?_At_idx bs a i (by omega) hl
  rw [get?_eq_getElem?] at this
  rw [this, List.getElem?_eq_getElem hi]

/-! ## Loads of string bytes -/

/-- Byte `i` of the character data of the string object at `p`. -/
abbrev byteAt (m : Mem 64) (p : BitVec 64) (i : Nat) : UInt8 := (m[p + 16#64 + .ofNat 64 i]?).getD 0

theorem load_chunk (m : Mem 64) (A : BitVec 64) (k w T : Nat)
    (hsome : ∀ i < T, (m[A + 16#64 + .ofNat 64 i]?).isSome) (hk : k + w ≤ T) :
    m.loadInt (A + .ofNat 64 k + 16#64) w =
      some (Int.ofBytes ((List.range w).map fun j => byteAt m A (k + j))) := by
  have ha : ∀ j, A + .ofNat 64 k + 16#64 + .ofNat 64 j = A + 16#64 + .ofNat 64 (k + j) := by
    intro j
    rw [BitVec.ofNat_add]
    ac_rfl
  rw [loadInt_eq _ _ _ (fun i hi => by rw [ha]; exact hsome _ (by omega))]
  simp only [ha]

theorem chunk_eq_iff (m : Mem 64) (A B : BitVec 64) (k w w' : Nat) (hw : w' = 8 * w) :
    BitVec.ofInt w' (Int.ofBytes ((List.range w).map fun j => byteAt m A (k + j))) =
      BitVec.ofInt w' (Int.ofBytes ((List.range w).map fun j => byteAt m B (k + j))) ↔
    ∀ j < w, byteAt m A (k + j) = byteAt m B (k + j) := by
  subst hw
  rw [ofInt_ofBytes_inj (8 * w) w rfl _ _ (by simp) (by simp), List.map_inj_left]
  simp

section
variable [Host] {str arg n off out : Reg64} {ymm : AvxReg .W256} {c₁ c₂ : BitVec 32}
  {d₁ d₂ : List UInt8}

/-- `t` agrees with `s` except for the temps `n`, `off`, `out`, the flags, and `ymm`. -/
def Frame (n off out : Reg64) (ymm : AvxReg .W256) (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ (∀ r, r ∉ [n, off, out] → t.regs.get64 r = s.regs.get64 r) ∧
  (t.zmms = s.zmms ∨ ∃ v, t.zmms = s.zmms.set ymm v)

/-- Labels are placed at the address of their index in the host program. -/
abbrev LabelsPlaced [Host] : Prop := ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i

macro "sstep" : tactic => `(tactic| (
  refine Program.loop_of_interp rfl ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, AvxOperation.interp, Operand.interp,
    RegOrMem.interp, AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set,
    MachineData.setReg, MachineData.setAvx, MachineData.setAvxReg, MachineData.load,
    MachineData.loadAvx, Effects.All, Effects.All_require_read_access, addr_base_disp,
    addr_sib1_disp, addr_base_disp', addr_sib1_disp', get_low32, get_low64, set_low32, set_low64,
    get64_set64, CondCode.interp,
    StatusFlags.from_result, Nat.add_assoc, Nat.reduceAdd, Int64.toBitVec_ofNat, Int64.toBitVec_neg,
    BitVec.truncate, Width.bits, AvxWidth.bits, Width.bytes, AvxWidth.bytes, BitVec.ofNat_eq_ofNat,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, sw32_64, zmms_get_set,
    zmms_set_set, Bool.false_eq_true, Bool.and_false, Bool.not_false, Bool.not_true, BitVec.zero_eq, BitVec.setWidth_eq, sw32_ofNat, cnt1, cnt3, Bool.false_and,
    ↓reduceIte]))

macro "cont" : tactic => `(tactic| refine Program.loopCont_of_le (by simp [stringEqualsProg]) ?_)

set_option hygiene false in
/-- Close a `Frame s t'` goal from `ht : Frame s t`, where `t'` only writes temps. -/
macro "frame_tac" : tactic => `(tactic| (
  refine ⟨?_, fun r hr' => ?_, ?_⟩
  · first | exact ht.1 | rfl
  · have hr'' := hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
    (simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2, ↓reduceIte]) <;>
    exact ht.2.1 r hr'
  · first
    | exact ht.2.2
    | (rcases ht.2.2 with h | ⟨w, h⟩
       · exact Or.inr ⟨_, by rw [h]⟩
       · exact Or.inr ⟨_, by rw [h, zmms_set_set]⟩)))

omit [Host] in
theorem post_of (hno : n ≠ out) (hfo : off ≠ out) (hnf : n ≠ off) {s t : MachineData}
    (v : BitVec 64)
    (hv : v = if stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ then 1#64 else 0#64)
    (hm : t.dmem = s.dmem) (hr : ∀ r, r ∉ [n, off, out] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ w, t.zmms = (s.zmms.set ymm w).zeroUpper) (st : StatusFlags) :
    StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s
      { regs := t.regs.set64 out v, zmms := t.zmms, status := st, dmem := t.dmem } := by
  refine ⟨t.regs.get64 n, t.regs.get64 off, t.zmms, st, hz, ?_⟩
  simp only [MachineData.mk.injEq, hm, and_true]
  apply reg64s_ext; intro r
  simp only [get64_set64]
  by_cases h1 : r = out
  · simp [h1, hv]
  by_cases h2 : r = off
  · subst h2; simp [h1]
  by_cases h3 : r = n
  · subst h3; simp [h1, h2]
  simp only [h1, h2, h3, ↓reduceIte]
  exact hr r (by simp [h1, h2, h3])

theorem ret_true (hno : n ≠ out) (hfo : off ≠ out) (hnf : n ≠ off) (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsProg str arg n off out ymm)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = true)
    (hm : t.dmem = s.dmem) (hr : ∀ r, r ∉ [n, off, out] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ w, t.zmms = (s.zmms.set ymm w).zeroUpper) :
    Program.Loop (stringEqualsProg str arg n off out ymm) H
      (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 40)⟩ := by
  sstep; cont; sstep; cont; sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 47) rfl]
  cont; sstep; cont
  exact Program.loop_done (post_of hno hfo hnf _ (by simp [hb]) hm hr hz _)

theorem ret_false (hno : n ≠ out) (hfo : off ≠ out) (hnf : n ≠ off) (_hlab : LabelsPlaced)
    (H : Embedding (stringEqualsProg str arg n off out ymm)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = false)
    (hm : t.dmem = s.dmem) (hr : ∀ r, r ∉ [n, off, out] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ w, t.zmms = (s.zmms.set ymm w).zeroUpper) :
    Program.Loop (stringEqualsProg str arg n off out ymm) H
      (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 45)⟩ := by
  sstep; cont; sstep; intro _; cont; sstep; cont
  exact Program.loop_done (post_of hno hfo hnf _ (by simp [hb]) hm hr hz _)

omit [Host] in
theorem zmms_vzero_ok (h_ymm : ymm.base ∈ lowMm) {s t : MachineData}
    (hz : t.zmms = s.zmms ∨ ∃ v, t.zmms = s.zmms.set ymm v) :
    t.zmms.zeroUpper = s.zmms ∨ ∃ w, t.zmms.zeroUpper = (s.zmms.set ymm w).zeroUpper := by
  rcases hz with h | ⟨v, h⟩
  · exact Or.inr ⟨s.zmms.get ymm, by rw [h, zeroUpper_set_get _ _ h_ymm]⟩
  · exact Or.inr ⟨v, by rw [h]⟩

theorem ret_true_vzero (hno : n ≠ out) (hfo : off ≠ out) (hnf : n ≠ off) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsProg str arg n off out ymm)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = true)
    (ht : Frame n off out ymm s t) :
    Program.Loop (stringEqualsProg str arg n off out ymm) H
      (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 38)⟩ := by
  sstep; cont; sstep; cont
  exact ret_true hno hfo hnf hlab H s _ hb ht.1 ht.2.1 (zmms_vzero_ok h_ymm ht.2.2)

theorem ret_false_vzero (hno : n ≠ out) (hfo : off ≠ out) (hnf : n ≠ off) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsProg str arg n off out ymm)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = false)
    (ht : Frame n off out ymm s t) :
    Program.Loop (stringEqualsProg str arg n off out ymm) H
      (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 43)⟩ := by
  sstep; cont; sstep; cont
  exact ret_false hno hfo hnf hlab H s _ hb ht.1 ht.2.1 (zmms_vzero_ok h_ymm ht.2.2)
set_option hygiene false in
macro "rs" : tactic => `(tactic| try simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1,
  Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9,
  Ne.symm h10, ↓reduceIte, hstr, harg, hoff, ht.1, get64_set64, get_low32, get_low64, sw32_64,
  sw32_ofNat])

/-- The facts about the two strings that the loops need, for `A ≠ B` and equal counts. -/
structure Strings (s : MachineData) (str arg : Reg64) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (A B : BitVec 64) (T : Nat) : Prop where
  hA : s.regs.get64 str = A
  hB : s.regs.get64 arg = B
  hT : T ≤ 2 ^ 33
  hsA : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome
  hsB : ∀ i < T, (s.dmem[B + 16#64 + .ofNat 64 i]?).isSome
  hTrue : (∀ i < T, byteAt s.dmem A i = byteAt s.dmem B i) → stringEquals A B c₁ c₂ d₁ d₂ = true
  hFalse : (∃ i < T, byteAt s.dmem A i ≠ byteAt s.dmem B i) → stringEquals A B c₁ c₂ d₁ d₂ = false

theorem qword (h_distinct : [str, arg, n, off, out].Nodup) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced) (H : Embedding (stringEqualsProg str arg n off out ymm))
    (s : MachineData) (A B : BitVec 64) (T : Nat) (hS : Strings s str arg c₁ c₂ d₁ d₂ A B T) :
    ∀ m k (t : MachineData), Frame n off out ymm s t →
      t.regs.get64 off = .ofNat 64 k → (t.regs.get64 n).setWidth 32 = .ofNat 32 m → 0 < m →
      k + 8 * m = T → (∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i) →
      Program.Loop (stringEqualsProg str arg n off out ymm) H
        (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
        ⟨t, Host.addrOf (H.start + 31)⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h_distinct
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h_distinct
  obtain ⟨hA, hB, hT, hsA, hsB, hTrue, hFalse⟩ := hS
  subst hA hB
  intro m
  induction m with
  | zero => intro _ _ _ _ _ h; omega
  | succ m ih =>
  intro k t ht hoff hn _ hk hpre
  have hstr : t.regs.get64 str = s.regs.get64 str := ht.2.1 str (by simp [h2, h3, h4])
  have harg : t.regs.get64 arg = s.regs.get64 arg := ht.2.1 arg (by simp [h5, h6, h7])
  sstep; cont; sstep
  rw [hstr, hoff, ht.1, load_chunk _ _ k 8 T hsA (by omega)]
  simp only []
  cont; sstep
  rs
  rw [load_chunk _ _ k 8 T hsB (by omega)]
  simp only []
  cont; sstep
  by_cases heq : ∀ j < 8, byteAt s.dmem (s.regs.get64 str) (k + j) = byteAt s.dmem (s.regs.get64 arg) (k + j)
  · rw [(chunk_eq_iff s.dmem _ _ k 8 64 rfl).mpr heq]
    simp only [BitVec.sub_self, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep; rs
    simp only [ofNat_add_lit]
    cont; sstep; rs
    cont; sstep
    simp only [hn, ofNat_succ_sub_one, ofNat32_eq_zero (show m < 2 ^ 32 by omega)]
    by_cases hm0 : m = 0
    · simp only [hm0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      refine ret_true_vzero h9 h10 h8 h_ymm hlab H s _ (hTrue fun i hi => ?_) (by frame_tac)
      by_cases hik : i < k
      · exact hpre i hik
      · have := heq (i - k) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
    · simp only [beq_eq_false_iff_ne.mpr hm0, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 31) rfl]
      cont
      refine ih (k + 8) _ (by frame_tac) (by rs) (by rs) (by omega) (by omega) fun i hi => ?_
      by_cases hik : i < k
      · exact hpre i hik
      · have := heq (i - k) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
  · have hne := mt (chunk_eq_iff s.dmem _ _ k 8 64 rfl).mp heq
    simp only [sub_beq_zero, beq_eq_false_iff_ne.mpr hne, Bool.not_false,
      ↓reduceIte, addrOf_label hlab (H := H) (i := 43) rfl]
    cont
    refine ret_false_vzero h9 h10 h8 h_ymm hlab H s _ (hFalse ?_) (by frame_tac)
    refine Classical.byContradiction fun hc => heq fun j hj => ?_
    exact Classical.byContradiction fun hne' => hc ⟨k + j, by omega, hne'⟩
theorem short (h_distinct : [str, arg, n, off, out].Nodup) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced) (H : Embedding (stringEqualsProg str arg n off out ymm))
    (s : MachineData) (A B : BitVec 64) (T L : Nat) (hS : Strings s str arg c₁ c₂ d₁ d₂ A B T)
    (hTL : T = L + padBytes L) :
    ∀ k r (t : MachineData), Frame n off out ymm s t →
      t.regs.get64 off = .ofNat 64 k → (t.regs.get64 n).setWidth 32 = .ofNat 32 r →
      k + r = L → r < 32 → k % 8 = 0 → (∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i) →
      Program.Loop (stringEqualsProg str arg n off out ymm) H
        (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
        ⟨t, Host.addrOf (H.start + 27)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, -, -, -, hTrue, -⟩ := hS'
  subst hA hB
  intro k r t ht hoff hn hkr hr hk8 hpre
  have hstr : t.regs.get64 str = s.regs.get64 str := ht.2.1 str (by simp [h2, h3, h4])
  have harg : t.regs.get64 arg = s.regs.get64 arg := ht.2.1 arg (by simp [h5, h6, h7])
  sstep; cont; sstep; rs
  simp only [hn, ofNat32_add_lit]
  cont; sstep; rs
  intro _ _
  cont; sstep
  simp only [ofNat32_ushiftRight (show 7 + r < 2 ^ 32 by omega),
    ofNat32_eq_zero (show (7 + r) / 2 ^ 3 < 2 ^ 32 by omega)]
  by_cases hm : (7 + r) / 2 ^ 3 = 0
  · simp only [hm, beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 38) rfl]
    cont
    refine ret_true_vzero h9 h10 h8 h_ymm hlab H s _ (hTrue fun i hi => ?_) (by frame_tac)
    have : padBytes L = 0 := by simp only [padBytes]; omega
    exact hpre i (by omega)
  · simp only [beq_eq_false_iff_ne.mpr hm, Bool.false_eq_true, ↓reduceIte]
    cont
    refine qword h_distinct h_ymm hlab H s _ _ T hS ((7 + r) / 2 ^ 3) k _ (by frame_tac) (by rs)
      (by rs) (by omega) (by simp only [hTL, padBytes]; omega) hpre
theorem avx (h_distinct : [str, arg, n, off, out].Nodup) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced) (H : Embedding (stringEqualsProg str arg n off out ymm))
    (s : MachineData) (A B : BitVec 64) (T L : Nat) (hS : Strings s str arg c₁ c₂ d₁ d₂ A B T)
    (hTL : T = L + padBytes L) (hL : L < 2 ^ 32) :
    ∀ r k (t : MachineData), Frame n off out ymm s t →
      t.regs.get64 off = .ofNat 64 k → (t.regs.get64 n).setWidth 32 = .ofNat 32 r →
      k + r = L → 32 ≤ r → k % 8 = 0 → (∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i) →
      Program.Loop (stringEqualsProg str arg n off out ymm) H
        (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
        ⟨t, Host.addrOf (H.start + 17)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, hT, hsA, hsB, hTrue, hFalse⟩ := hS'
  subst hA hB
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t ht hoff hn hkr hr hk8 hpre
  have hstr : t.regs.get64 str = s.regs.get64 str := ht.2.1 str (by simp [h2, h3, h4])
  have harg : t.regs.get64 arg = s.regs.get64 arg := ht.2.1 arg (by simp [h5, h6, h7])
  sstep; cont; sstep; rs
  rw [load_chunk _ _ k 32 T hsA (by omega)]
  simp only []
  cont; sstep; rs
  rw [load_chunk _ _ k 32 T hsB (by omega)]
  simp only []
  cont; sstep; cont; sstep; rs
  simp only [sw_m1, sub_beq_zero]
  cont; sstep
  by_cases heq : ∀ j < 32, byteAt s.dmem (s.regs.get64 str) (k + j) = byteAt s.dmem (s.regs.get64 arg) (k + j)
  · rw [(chunk_eq_iff s.dmem _ _ k 32 256 rfl).mpr heq]
    simp only [pm_self, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep; rs
    simp only [ofNat_add_lit]
    cont; sstep; rs
    simp only [hn, ofNat32_sub_lit (show 32 ≤ r by omega)]
    cont; sstep; rs
    simp only [cf_ofNat32 (show r - 32 < 2 ^ 32 by omega) (show 32 < 2 ^ 32 by decide)]
    cont; sstep
    by_cases hlt : r - 32 < 32
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      exact short h_distinct h_ymm hlab H s _ _ T L hS hTL (k + 32) (r - 32) _ (by frame_tac)
        (by rs) (by rs) (by omega) (by omega) (by omega) (prefix_ext hpre heq)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 17) rfl]
      cont
      exact ih (r - 32) (by omega) (k + 32) _ (by frame_tac) (by rs) (by rs) (by omega) (by omega)
        (by omega) (prefix_ext hpre heq)
  · have hne := mt (chunk_eq_iff s.dmem _ _ k 32 256 rfl).mp heq
    have hm := mt (pmovmskb_pcmpeqb _ _).mp hne
    simp only [beq_eq_false_iff_ne.mpr hm, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 43) rfl]
    cont
    refine ret_false_vzero h9 h10 h8 h_ymm hlab H s _ (hFalse ?_) (by frame_tac)
    refine Classical.byContradiction fun hc => heq fun j hj => ?_
    exact Classical.byContradiction fun hne' => hc ⟨k + j, by omega, hne'⟩
theorem len_done (h_distinct : [str, arg, n, off, out].Nodup) (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced) (H : Embedding (stringEqualsProg str arg n off out ymm))
    (s : MachineData) (A B : BitVec 64) (T L : Nat) (hS : Strings s str arg c₁ c₂ d₁ d₂ A B T)
    (hTL : T = L + padBytes L) (hL : L < 2 ^ 32) (t : MachineData) (ht : Frame n off out ymm s t)
    (hn : (t.regs.get64 n).setWidth 32 = .ofNat 32 L) :
    Program.Loop (stringEqualsProg str arg n off out ymm) H
      (StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 13)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := hd
  have hstr : t.regs.get64 str = s.regs.get64 str := ht.2.1 str (by simp [h2, h3, h4])
  have harg : t.regs.get64 arg = s.regs.get64 arg := ht.2.1 arg (by simp [h5, h6, h7])
  have hoff : True := trivial
  sstep; cont; sstep
  intro _
  cont; sstep; rs
  simp only [BitVec.xor_self, hn, cf_ofNat32 hL (show 32 < 2 ^ 32 by decide)]
  cont; sstep
  by_cases hlt : L < 32
  · simp only [hlt, decide_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 27) rfl]
    cont
    exact short h_distinct h_ymm hlab H s A B T L hS hTL 0 L _ (by frame_tac) (by rs) (by rs; exact hn)
      (by omega) hlt (by omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    cont
    exact avx h_distinct h_ymm hlab H s A B T L hS hTL hL L 0 _ (by frame_tac) (by rs) (by rs; exact hn)
      (by omega) (by omega) (by omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
/-! ## Facts about the string objects -/

/-- The data of a string followed by its zero padding. -/
abbrev padded (d : List UInt8) : List UInt8 := d ++ List.replicate (padBytes d.length) 0

omit [Host] in
theorem stringAt_cnt {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {i : Nat} (hi : i < 4) :
    ∀ m, StringAt p c d m →
      m[p + 8#64 + .ofNat 64 i]? = some ((Int.toBytes 4 c.toInt)[i]'(by simp [Int.toBytes_length, hi])) :=
  fun _ h => sep_get_l h (at_get _ _ _ (by simp [Int.toBytes_length]))

omit [Host] in
theorem stringAt_data {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {i : Nat}
    (hi : i < (padded d).length) (hl : (padded d).length ≤ 2 ^ 64) :
    ∀ m, StringAt p c d m → m[p + 16#64 + .ofNat 64 i]? = some ((padded d)[i]'hi) :=
  fun _ h => sep_get_r h (at_get _ _ _ hl)

omit [Host] in
theorem load_count (m : Mem 64) (p : BitVec 64) (c : BitVec 32)
    (h : ∀ i (hi : i < 4), m[p + 8#64 + .ofNat 64 i]? =
      some ((Int.toBytes 4 c.toInt)[i]'(by simp [Int.toBytes_length, hi]))) :
    m.loadInt (p + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 c.toInt)) := by
  rw [loadInt_eq m _ 4 (fun i hi => by rw [h i hi]; rfl)]
  congr 2
  apply List.ext_getElem (by simp [Int.toBytes_length])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  simp at h1
  rw [h i h1]; rfl

omit [Host] in
theorem cnt_val (c : BitVec 32) : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 c.toInt)) = c :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl c

omit [Host] in
theorem strByteLen_lt (c : BitVec 32) : strByteLen c < 2 ^ 32 - 1 := by
  have : (c >>> 1).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := c.isLt; omega
  unfold strByteLen; split <;> omega

omit [Host] in
theorem strings_of {s : MachineData} {c : BitVec 32} {d₁ d₂ : List UInt8} {R : Mem 64 → Prop}
    (hAB : s.regs.get64 str ≠ s.regs.get64 arg)
    (hmem : (StringAt (s.regs.get64 str) c d₁ ⋆ StringAt (s.regs.get64 arg) c d₂ ⋆ R) s.dmem)
    (h₁ : d₁.length = strByteLen c) (h₂ : d₂.length = strByteLen c) :
    Strings s str arg c c d₁ d₂ (s.regs.get64 str) (s.regs.get64 arg)
      (strByteLen c + padBytes (strByteLen c)) := by
  have hL := strByteLen_lt c
  have hpl₁ : (padded d₁).length = strByteLen c + padBytes (strByteLen c) := by simp [h₁]
  have hpl₂ : (padded d₂).length = strByteLen c + padBytes (strByteLen c) := by simp [h₂]
  have hpad : padBytes (strByteLen c) < 8 := by unfold padBytes; omega
  have dA : ∀ i (hi : i < strByteLen c + padBytes (strByteLen c)),
      s.dmem[s.regs.get64 str + 16#64 + .ofNat 64 i]? = some ((padded d₁)[i]'(by omega)) :=
    fun i hi => sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data _ (by omega)))
  have dB : ∀ i (hi : i < strByteLen c + padBytes (strByteLen c)),
      s.dmem[s.regs.get64 arg + 16#64 + .ofNat 64 i]? = some ((padded d₂)[i]'(by omega)) :=
    fun i hi => sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data _ (by omega)))
  refine ⟨rfl, rfl, by omega, fun i hi => by simp [dA i hi], fun i hi => by simp [dB i hi],
    fun h => ?_, fun ⟨i, hi, hne⟩ => ?_⟩
  · have hp : padded d₁ = padded d₂ := by
      apply List.ext_getElem (by omega)
      intro i h1 h2
      have := h i (by omega)
      simp only [byteAt, dA i (by omega), dB i (by omega), Option.getD_some] at this
      exact this
    have : d₁ = d₂ := List.append_inj_left hp (by omega)
    simp [stringEquals, this]
  · simp only [stringEquals, beq_eq_false_iff_ne.mpr hAB, Bool.false_or, beq_self_eq_true,
      Bool.true_and, beq_eq_false_iff_ne]
    rintro rfl
    simp [byteAt, dA i hi, dB i hi] at hne

omit [Host] in
theorem low32_beq {a b : BitVec 64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a.setWidth 32 == b.setWidth 32) = (a == b) := by
  by_cases h : a = b
  · simp [h]
  · have : a.setWidth 32 ≠ b.setWidth 32 := fun h' => h (by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      exact this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

omit [Host] in
theorem lsb_and1 (c : BitVec 32) : (c &&& 1#32 == 0#32) = !c.getLsbD 0 := by bv_decide

omit [Host] in
theorem and_m2 {c : BitVec 32} (h : c.getLsbD 0 = true) :
    c &&& 4294967294#32 = BitVec.ofNat 32 (strByteLen c) := by
  have e : c &&& 4294967294#32 = (c >>> 1) <<< 1 := by bv_decide
  rw [e, strByteLen, ite_eq_left h]
  apply BitVec.eq_of_toNat_eq
  have hlt : (c >>> 1).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := c.isLt; omega
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [Host] in
theorem shr1 {c : BitVec 32} (h : c.getLsbD 0 = false) :
    c.ushiftRight 1 = BitVec.ofNat 32 (strByteLen c) := by
  have h' : (c.getLsbD 0 = true) = False := by rw [h]; decide
  rw [strByteLen, ite_eq_right (by rw [h']; exact id)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl
end

end Proof

open Proof Std.WP in
/--
Correctness theorem: `stringEqualsProg` satisfies its specification on any `Host` program.
`s₀` is the initial state, which the postcondition refers to.
`ymm` is VEX-encodable (ymm0–ymm15), which is all ART emits.
-/
theorem stringEquals_correct [Host]
    (str arg n off out : Reg64) (ymm : AvxReg .W256)
    (h_distinct : [str, arg, n, off, out].Nodup)
    (h_ymm : ymm.base ∈ [RegMm.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10,
      .mm11, .mm12, .mm13, .mm14, .mm15])
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧
        (s.regs.get64 str).toNat < 2 ^ 32 ∧
        (s.regs.get64 arg).toNat < 2 ^ 32 ∧
        d₁.length = strByteLen c₁ ∧
        d₂.length = strByteLen c₂ ∧
        ∃ R, StringsInMem (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ R s.dmem ⦄
      stringEqualsProg str arg n off out ymm
    ⦃ fun _ => StringEqualsPost str arg n off out ymm c₁ c₂ d₁ d₂ s₀; fun _ _ => False ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hA32, hB32, hl₁, hl₂, ⟨R, hmem⟩⟩
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := hd
  apply Program.wp_of_loop
  intro H
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  sstep; cont; sstep
  simp only [sub_beq_zero, low32_beq hA32 hB32]
  by_cases hAB : s.regs.get64 str = s.regs.get64 arg
  · simp only [hAB, beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 40) rfl]
    cont
    exact ret_true h9 h10 h8 hlab H s _ (by simp [stringEquals, hAB]) rfl (fun _ _ => rfl) (Or.inl rfl)
  simp only [beq_eq_false_iff_ne.mpr hAB, Bool.false_eq_true, ↓reduceIte]
  rw [StringsInMem, ite_eq_right hAB] at hmem
  have cA := fun i (hi : i < 4) => sep_get_l hmem (fun _ h => sep_get_l h (stringAt_cnt (i := i) hi))
  have cB := fun i (hi : i < 4) => sep_get_l hmem (fun _ h => sep_get_r h (stringAt_cnt (i := i) hi))
  cont; sstep
  rw [load_count _ _ _ cA]
  simp only [cnt_val]
  cont; sstep
  simp only [h5, ↓reduceIte]
  rw [load_count _ _ _ cB]
  simp only [cnt_val, sub_beq_zero]
  cont; sstep
  by_cases hc : ¬c₁ = c₂
  · simp only [beq_eq_false_iff_ne.mpr hc, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 45) rfl]
    cont
    refine ret_false h9 h10 h8 hlab H s _ (by simp [stringEquals, hAB, hc]) rfl (fun r hr => ?_)
      (Or.inl rfl)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [get64_set64, hr.1]
  simp only [Classical.not_not] at hc
  subst hc
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [Effects.All]
  have ht : Frame n off out ymm s s := ⟨rfl, fun _ _ => rfl, Or.inl rfl⟩
  have hS := strings_of hAB hmem hl₁ hl₂
  have hL := strByteLen_lt c₁
  cont; sstep
  simp only [BitVec.and_self]
  intro _
  cont; sstep
  by_cases hc0 : c₁ = 0
  · simp only [hc0, addrOf_label hlab (H := H) (i := 40) rfl]
    cont
    have e₁ : d₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₁, hc0]; rfl)
    have e₂ : d₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₂, hc0]; rfl)
    refine ret_true h9 h10 h8 hlab H s _ (by simp [stringEquals, e₁, e₂]) rfl (fun r hr => ?_)
      (Or.inl rfl)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [get64_set64, hr.1]
  simp only [beq_eq_false_iff_ne.mpr (show c₁ ≠ 0#32 from hc0), Bool.false_eq_true, ↓reduceIte]
  cont; sstep
  intro _
  cont; sstep
  simp only [lsb_and1, Bool.not_not]
  by_cases hbit : c₁.getLsbD 0 = true
  · simp only [hbit, ↓reduceIte, addrOf_label hlab (H := H) (i := 11) rfl]
    cont; sstep; cont; sstep
    intro _
    cont
    exact len_done h_distinct h_ymm hlab H s _ _ _ _ hS rfl (by omega) _ (by frame_tac)
      (by simp [get64_set64, and_m2 hbit])
  · simp only [Bool.not_eq_true] at hbit
    simp only [hbit, Bool.false_eq_true, ↓reduceIte]
    cont; sstep
    intro _
    cont; sstep
    simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 13) rfl]
    cont
    exact len_done h_distinct h_ymm hlab H s _ _ _ _ hS rfl (by omega) _ (by frame_tac)
      (by simp only [get64_set64, ↓reduceIte, sw32_64, shr1 hbit])

end

end Kraken.X64.Art
