module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
import Kraken.X64.Parser
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
public import Kraken.X64.Art.StringCompareToSpec

open Std
open Std.ExtHashMap
open Std.WP

namespace Kraken.X64.Art

public section

/--
Core AVX2 assembly template for `String.compareTo` without the `arg == null` check,
matching `VisitStringCompareTo` codegen verbatim. Implicit `TMP` in the mixed loop
is `.r11` (`%r11d`).
-/
@[expose] def stringCompareToNoCheckProg
    (str arg out c1 c2 n off : Reg64) (ymm : AvxReg .W256) : _root_.Program := parse("
    xorl %❰.low out .W32❱, %❰.low out .W32❱
    cmpl %❰.low arg .W32❱, %❰.low str .W32❱
    jz done

    movl 8(%❰str❱), %❰.low c1 .W32❱
    movl 8(%❰arg❱), %❰.low c2 .W32❱
    movl %❰.low c1 .W32❱, %❰.low n .W32❱
    movl %❰.low c2 .W32❱, %❰.low off .W32❱
    shrl $1, %❰.low n .W32❱
    shrl $1, %❰.low off .W32❱

    movl %❰.low n .W32❱, %❰.low out .W32❱
    subl %❰.low off .W32❱, %❰.low out .W32❱
    cmovg %❰.low off .W32❱, %❰.low n .W32❱

    testl %❰.low n .W32❱, %❰.low n .W32❱
    jz done

    xorl %❰.low c1 .W32❱, %❰.low c2 .W32❱
    testl $1, %❰.low c2 .W32❱
    jnz mixed_init

    andl $1, %❰.low c1 .W32❱
    leal (%❰n❱, %❰n❱, 1), %❰.low c2 .W32❱
    cmovne %❰.low c2 .W32❱, %❰.low n .W32❱
    xorl %❰.low off .W32❱, %❰.low off .W32❱
    cmpl $32, %❰.low n .W32❱
    jb qword_loop

  avx2_loop:
    vmovdqu 16(%❰str❱, %❰off❱), %❰ymm❱
    vpcmpeqb 16(%❰arg❱, %❰off❱), %❰ymm❱, %❰ymm❱
    vpmovmskb %❰ymm❱, %❰.low c2 .W32❱
    cmpl $-1, %❰.low c2 .W32❱
    jnz avx2_diff
    addq $32, %❰.low off .W64❱
    subl $32, %❰.low n .W32❱
    cmpl $32, %❰.low n .W32❱
    jae avx2_loop

    testl %❰.low n .W32❱, %❰.low n .W32❱
    jz avx2_done
    leaq -32(%❰off❱, %❰n❱, 1), %❰.low off .W64❱
    vmovdqu 16(%❰str❱, %❰off❱), %❰ymm❱
    vpcmpeqb 16(%❰arg❱, %❰off❱), %❰ymm❱, %❰ymm❱
    vpmovmskb %❰ymm❱, %❰.low c2 .W32❱
    cmpl $-1, %❰.low c2 .W32❱
    jnz avx2_diff
  avx2_done:
    vzeroupper
    jmp done

  avx2_diff:
    vzeroupper
    notl %❰.low c2 .W32❱
    bsfl %❰.low c2 .W32❱, %❰.low c2 .W32❱
    addl %❰.low c2 .W32❱, %❰.low off .W32❱

  diff:
    testl %❰.low c1 .W32❱, %❰.low c1 .W32❱
    jnz diff_u16
    movzbl 16(%❰str❱, %❰off❱), %❰.low out .W32❱
    movzbl 16(%❰arg❱, %❰off❱), %❰.low c2 .W32❱
    subl %❰.low c2 .W32❱, %❰.low out .W32❱
    jmp done

  diff_u16:
    andl $-2, %❰.low off .W32❱
    movzwl 16(%❰str❱, %❰off❱), %❰.low out .W32❱
    movzwl 16(%❰arg❱, %❰off❱), %❰.low c2 .W32❱
    subl %❰.low c2 .W32❱, %❰.low out .W32❱
    jmp done

  qword_loop:
    movq 16(%❰str❱, %❰off❱), %❰.low c2 .W64❱
    xorq 16(%❰arg❱, %❰off❱), %❰.low c2 .W64❱
    jnz qword_diff
    addq $8, %❰.low off .W64❱
    subl $8, %❰.low n .W32❱
    ja qword_loop
    jmp done

  qword_diff:
    bsfq %❰.low c2 .W64❱, %❰.low c2 .W64❱
    shrl $3, %❰.low c2 .W32❱
    cmpl %❰.low n .W32❱, %❰.low c2 .W32❱
    jae done
    addl %❰.low c2 .W32❱, %❰.low off .W32❱
    jmp diff

  mixed_init:
    movq %❰.low str .W64❱, %❰.low c2 .W64❱
    movq %❰.low arg .W64❱, %❰.low off .W64❱
    andl $1, %❰.low c1 .W32❱
    cmovne %❰.low arg .W64❱, %❰.low c2 .W64❱
    cmovne %❰.low str .W64❱, %❰.low off .W64❱
    shll $1, %❰.low n .W32❱
    subl %❰.low c1 .W32❱, %❰.low n .W32❱

  mixed_loop:
    movzbl 16(%❰c2❱), %❰.low c1 .W32❱
    movzwl 16(%❰off❱), %r11d
    subl %r11d, %❰.low c1 .W32❱
    jnz mixed_diff
    addq $1, %❰.low c2 .W64❱
    addq $2, %❰.low off .W64❱
    subl $2, %❰.low n .W32❱
    ja mixed_loop
    jmp done

  mixed_diff:
    movl %❰.low c1 .W32❱, %❰.low out .W32❱
    negl %❰.low c1 .W32❱
    testl $1, %❰.low n .W32❱
    cmovne %❰.low c1 .W32❱, %❰.low out .W32❱

  done:
")

/--
AVX2 assembly template for `String.compareTo` with the `arg == null` slow-path check:
two prefix instructions followed by `stringCompareToNoCheckProg`.
-/
@[expose] def stringCompareToProg (slow : Label)
    (str arg out c1 c2 n off : Reg64) (ymm : AvxReg .W256) : _root_.Program := parse("
    testl %❰.low arg .W32❱, %❰.low arg .W32❱
    ❰.instr (.regular .W64 .W64 (.jcc .z slow))❱
") ++ stringCompareToNoCheckProg str arg out c1 c2 n off ymm

end

/-! ## Proof helpers -/

namespace CompareToProof

open Proof (addr_base_disp addr_sib1_disp addr_base_disp' addr_sib1_disp'
  loadInt_eq ofInt_ofBytes_inj i64_add_sub sub_beq_zero
  ofNat_succ_sub_one ofNat_add_lit ofNat32_add_lit ofNat32_sub_lit ofNat32_eq_zero
  ofNat32_ushiftRight cf_ofNat32 sw32_64 sw32_ofNat cnt1 cnt3 sw_m1 pm_self
  prefix_ext reg64s_ext regZmms_ext lowMm zmms_get_set zmms_set_set zeroUpper_set_get
  zmms_vzero_ok get64_set64 get_low32 get_low64 set_low32 set_low64
  sep_get_l sep_get_r at_get byteAt load_chunk chunk_eq_iff
  padded stringAt_cnt stringAt_data load_count cnt_val strByteLen_lt
  low32_beq lsb_and1 and_m2 shr1)

section
variable [Host] {str arg out c1 c2 n off : Reg64} {ymm : AvxReg .W256} {c₁ c₂ : BitVec 32}
  {d₁ d₂ : List UInt8}

abbrev LabelsPlaced [Host] : Prop :=
  ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i

/-- `t` agrees with `s` except for `[out, c1, c2, n, off, .r11]`, flags, and `ymm` (not zero-uppered yet). -/
def PreVzeroFrame (out c1 c2 n off : Reg64) (ymm : AvxReg .W256) (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧
  (∀ r, r ∉ [out, c1, c2, n, off, .r11] → t.regs.get64 r = s.regs.get64 r) ∧
  (t.zmms = s.zmms ∨ ∃ v, t.zmms = s.zmms.set ymm v)

/-- `t` agrees with `s` except for `[out, c1, c2, n, off, .r11]`, flags, and post-`vzeroupper` `zmms`. -/
def PostFrame (out c1 c2 n off : Reg64) (ymm : AvxReg .W256) (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧
  (∀ r, r ∉ [out, c1, c2, n, off, .r11] → t.regs.get64 r = s.regs.get64 r) ∧
  (t.zmms = s.zmms ∨ ∃ w, t.zmms = (s.zmms.set ymm w).zeroUpper)

omit [Host] in
theorem sw_m2 : BitVec.setWidth 32 (-2#64) = (-2#32 : BitVec 32) := by decide

omit [Host] in
theorem sw64_ofNat32 {x : Nat} (hx : x < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]

omit [Host] in
theorem bv32_eq_of_toNat {v : BitVec 32} {r : Nat} (hv : v.toNat = r) (hr : r < 2 ^ 32) :
    v = BitVec.ofNat 32 r := by
  apply BitVec.eq_of_toNat_eq
  rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]

omit [Host] in
theorem ofNat32_sub_eq_zero {m c : Nat} (hm : m < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 m - BitVec.ofNat 32 c == 0#32) = decide (m = c) := by
  rw [sub_beq_zero]
  by_cases h : m = c
  · subst h; simp
  · have hne : BitVec.ofNat 32 m ≠ BitVec.ofNat 32 c := fun heq => h (by
      have := congrArg BitVec.toNat heq
      simpa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hc] using this)
    simp [hne, h]

omit [Host] in
theorem ofNat32_and1_eq_zero {x : Nat} :
    (BitVec.ofNat 32 x &&& 1#32 == 0#32) = decide (x % 2 = 0) := by
  have h : (BitVec.ofNat 32 x &&& 1#32).toNat = x % 2 := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    have h1 : (1 : Nat) % 2 ^ 32 = 1 := rfl
    rw [h1, Nat.and_one_is_mod, Nat.mod_mod_of_dvd x (by decide)]
  by_cases hmod : x % 2 = 0
  · have : BitVec.ofNat 32 x &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq (by simp [h, hmod])
    simp [this, hmod]
  · have hne : BitVec.ofNat 32 x &&& 1#32 ≠ 0#32 := fun heq => hmod (by
      have := congrArg BitVec.toNat heq; simp [h] at this; exact this)
    simp [hne, hmod]

omit [Host] in
theorem ofNat32_and_neg2 {k : Nat} (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k &&& (-2#32) = BitVec.ofNat 32 (2 * (k / 2)) := by
  rw [and_neg2_eq]
  congr 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

omit [Host] in
theorem leaq_tail_addr (k r : Nat) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 r + (-32 : Int64).toBitVec) =
      BitVec.ofNat 64 (k + r - 32) ∨ 32 > k + r := by
  by_cases h : 32 ≤ k + r
  · left
    have hkr : k + r = (k + r - 32) + 32 := by omega
    have hkr2 : k + r - 32 + 32 - 32 = k + r - 32 := by omega
    have h32 : (-32 : Int64).toBitVec = -BitVec.ofNat 64 32 := by decide
    rw [← BitVec.ofNat_add, h32, hkr, BitVec.ofNat_add, BitVec.add_assoc]
    have h0 : BitVec.ofNat 64 32 + -BitVec.ofNat 64 32 = 0#64 := by decide
    rw [h0, BitVec.add_zero, hkr2]
  · exact Or.inr (by omega)

omit [Host] in
theorem sub_cmovg_cond (x y : BitVec 32)
    (hx31 : x.toNat < 2 ^ 31) (hy31 : y.toNat < 2 ^ 31) :
    (!(x - y == 0#32) && ((x - y).msb == ((x - y).signed != x.signed - y.signed))) =
      decide (y.toNat < x.toNat) := by
  have hxs : x.toInt = (x.toNat : Int) := by rw [BitVec.toInt]; split <;> omega
  have hys : y.toInt = (y.toNat : Int) := by rw [BitVec.toInt]; split <;> omega
  have hof : ((x - y).signed != x.signed - y.signed) = false := by
    simp only [BitVec.signed, BitVec.toInt_sub, hxs, hys, Int.bmod, bne_eq_false_iff_eq]
    have hm : ((x.toNat : Int) - y.toNat) % (2 ^ 32 : Int) =
        if y.toNat ≤ x.toNat then (x.toNat : Int) - y.toNat else (x.toNat : Int) - y.toNat + 2 ^ 32 := by
      split <;> omega
    split <;> split at hm <;> omega
  rw [hof]
  by_cases hlt : y.toNat < x.toNat
  · have hne : x - y ≠ 0#32 := fun heq => by
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega
    have hmsb : (x - y).msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
      rw [BitVec.toNat_sub]
      have : (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 = x.toNat - y.toNat := by
        rw [show 2 ^ 32 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 32 by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega)
    simp [hlt, hne, hmsb]
  · simp only [hlt, decide_false]
    by_cases heq : x = y
    · subst heq; simp
    · have hlt' : x.toNat < y.toNat := by
        have hne : x.toNat ≠ y.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
        omega
      have hmsb : (x - y).msb = true := BitVec.msb_eq_true_iff_two_mul_ge.mpr (by
        rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
        omega)
      simp [hmsb]

omit [Host] in
theorem ofInt8_zeroExtend32 (b : UInt8) :
    (BitVec.ofInt 8 (Int.ofBytes [b])).zeroExtend 32 =
      (b.toBitVec.zeroExtend 16).zeroExtend 32 := by
  rw [show (BitVec.ofInt 8 (Int.ofBytes [b])) = b.toBitVec by
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hs : Int.ofBytes [b] = b.toNat := by simp [Int.ofBytes]
    rw [hs]
    apply BitVec.eq_of_toNat_eq
    simp]
  ext i hi; simp [BitVec.zeroExtend]

omit [Host] in
theorem ofInt16_zeroExtend32 (b0 b1 : UInt8) :
    (BitVec.ofInt 16 (Int.ofBytes [b0, b1])).zeroExtend 32 =
      (b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
  rw [word_of_bytes b0 b1]

omit [Host] in
theorem byte_diff_32 (b₁ b₂ : UInt8) :
    (BitVec.ofInt 8 (Int.ofBytes [b₁])).zeroExtend 32 -
      (BitVec.ofInt 8 (Int.ofBytes [b₂])).zeroExtend 32 =
    (b₁.toBitVec.zeroExtend 16).zeroExtend 32 - (b₂.toBitVec.zeroExtend 16).zeroExtend 32 := by
  rw [ofInt8_zeroExtend32, ofInt8_zeroExtend32]

omit [Host] in
theorem word_diff_32 (a0 a1 b0 b1 : UInt8) :
    (BitVec.ofInt 16 (Int.ofBytes [a0, a1])).zeroExtend 32 -
      (BitVec.ofInt 16 (Int.ofBytes [b0, b1])).zeroExtend 32 =
    (a0.toBitVec.zeroExtend 16 ||| (a1.toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 -
      (b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
  rw [ofInt16_zeroExtend32, ofInt16_zeroExtend32]

omit [Host] in
theorem c1_and1_eq (c : BitVec 32) :
    c &&& 1#32 = if c.getLsbD 0 then 1#32 else 0#32 := by
  cases h0 : c.getLsbD 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    rcases i with _ | j
    · simpa [BitVec.getLsbD_eq_getElem] using h0
    · have : (1#32 : BitVec 32).getLsbD (j + 1) = false := by
        simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero j))]
      simp [this]

omit [Host] in
theorem xor_lsb0_iff (a b : BitVec 32) :
    ((a ^^^ b) &&& 1#32 == 0#32) = (a.getLsbD 0 == b.getLsbD 0) := by
  rw [lsb_and1, BitVec.getLsbD_xor]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> rfl

omit [Host] in
theorem neg_32_ze64 (a b : BitVec 16) :
    (-(a.zeroExtend 32 - b.zeroExtend 32)).setWidth 64 =
      (b.zeroExtend 32 - a.zeroExtend 32).zeroExtend 64 := by
  rw [← compareToSpec_diff_neg b a]

omit [Host] in
theorem padBytes_mono {a b : Nat} (hab : a ≤ b) : a + padBytes a ≤ b + padBytes b := by
  simp only [padBytes]; omega

omit [Host] in
theorem qword_bound {k L : Nat} (hk8 : k % 8 = 0) (hkL : k < L) : k + 8 ≤ L + padBytes L := by
  simp only [padBytes]; omega

omit [Host] in
theorem uncomp_pair_lt {k minChars : Nat} (hk : k < 2 * minChars) : 2 * (k / 2) + 1 < 2 * minChars := by
  omega

omit [Host] in
theorem post_of (_hout_diff : out ∉ [c1, c2, n, off, .r11])
    {s t : MachineData} (v : BitVec 64)
    (hv : v = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, c1, c2, n, off, .r11] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ w, t.zmms = (s.zmms.set ymm w).zeroUpper) :
    StringCompareToPost out [c1, c2, n, off, .r11] [ymm]
      (strChars c₁ d₁) (strChars c₂ d₂) s
      { regs := t.regs.set64 out v, zmms := t.zmms, status := t.status, dmem := t.dmem } := by
  refine ⟨?_, fun r hr' => ?_, hm, zmms_post_singleton hz⟩
  · simp [get64_set64, hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [get64_set64, hr'.1, ↓reduceIte]
    exact hr r (by simp [hr'])

omit [Host] in
theorem post_of_done (s t : MachineData)
    (hout : t.regs.get64 out = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64)
    (ht : PostFrame out c1 c2 n off ymm s t) :
    StringCompareToPost out [c1, c2, n, off, .r11] [ymm]
      (strChars c₁ d₁) (strChars c₂ d₂) s t :=
  ⟨hout, ht.2.1, ht.1, zmms_post_singleton ht.2.2⟩

macro "sstep" : tactic => `(tactic| (
  refine Program.loop_of_interp rfl ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, AvxOperation.interp, Operand.interp,
    RegOrMem.interp, AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set,
    MachineData.setReg, MachineData.setAvx, MachineData.setAvxReg, MachineData.load,
    MachineData.loadAvx, Effects.All, Effects.All_require_read_access, addr_base_disp,
    addr_sib1_disp, addr_base_disp', addr_sib1_disp', get_low32, get_low64, set_low32, set_low64,
    get64_set64, CondCode.interp,
    StatusFlags.from_result, Nat.add_assoc, Nat.reduceAdd, Nat.reduceBEq, Nat.reduceLT,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg,
    BitVec.truncate, Width.bits, AvxWidth.bits, Width.bytes, AvxWidth.bytes, BitVec.ofNat_eq_ofNat,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, sw32_64, zmms_get_set,
    zmms_set_set, Bool.false_eq_true, Bool.and_false, Bool.not_false, Bool.not_true,
    BitVec.zero_eq, BitVec.setWidth_eq, sw32_ofNat, sw_m1, sw_m2, cnt1, cnt3, Bool.false_and,
    ↓reduceIte]))

macro "cont" : tactic => `(tactic| refine Program.loopCont_of_le (by simp [stringCompareToNoCheckProg]) ?_)

set_option hygiene false in
macro "post_frame_tac" : tactic => `(tactic| (
  refine ⟨?_, fun r hr' => ?_, ?_⟩
  · first | exact ht.1 | rfl
  · have hr'' := hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
    (simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
      hr''.2.2.2.2.2, ↓reduceIte]) <;>
    exact ht.2.1 r hr'
  · exact ht.2.2))

set_option hygiene false in
macro "pre_frame_tac" : tactic => `(tactic| (
  refine ⟨?_, fun r hr' => ?_, ?_⟩
  · first | exact ht.1 | rfl
  · have hr'' := hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
    (simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
      hr''.2.2.2.2.2, ↓reduceIte]) <;>
    exact ht.2.1 r hr'
  · first
    | exact ht.2.2
    | (rcases ht.2.2 with h | ⟨w, h⟩
       · exact Or.inr ⟨_, by rw [h]⟩
       · exact Or.inr ⟨_, by rw [h, zmms_set_set]⟩)))

set_option hygiene false in
macro "rs" : tactic => `(tactic| try simp only [
  h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11,
  h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11,
  h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11,
  h_c1_c2, h_c1_n, h_c1_off, h_c1_r11,
  h_c2_n, h_c2_off, h_c2_r11,
  h_n_off, h_n_r11,
  h_off_r11,
  Ne.symm h_str_arg, Ne.symm h_str_out, Ne.symm h_str_c1, Ne.symm h_str_c2, Ne.symm h_str_n, Ne.symm h_str_off, Ne.symm h_str_r11,
  Ne.symm h_arg_out, Ne.symm h_arg_c1, Ne.symm h_arg_c2, Ne.symm h_arg_n, Ne.symm h_arg_off, Ne.symm h_arg_r11,
  Ne.symm h_out_c1, Ne.symm h_out_c2, Ne.symm h_out_n, Ne.symm h_out_off, Ne.symm h_out_r11,
  Ne.symm h_c1_c2, Ne.symm h_c1_n, Ne.symm h_c1_off, Ne.symm h_c1_r11,
  Ne.symm h_c2_n, Ne.symm h_c2_off, Ne.symm h_c2_r11,
  Ne.symm h_n_off, Ne.symm h_n_r11,
  Ne.symm h_off_r11,
  ↓reduceIte, hstr, harg, hoff, ht.1, get64_set64, get_low32, get_low64, sw32_64, sw32_ofNat])

set_option hygiene false in
macro "rs_reg" : tactic => `(tactic| try simp only [
  h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11,
  h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11,
  h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11,
  h_c1_c2, h_c1_n, h_c1_off, h_c1_r11,
  h_c2_n, h_c2_off, h_c2_r11,
  h_n_off, h_n_r11,
  h_off_r11,
  Ne.symm h_str_arg, Ne.symm h_str_out, Ne.symm h_str_c1, Ne.symm h_str_c2, Ne.symm h_str_n, Ne.symm h_str_off, Ne.symm h_str_r11,
  Ne.symm h_arg_out, Ne.symm h_arg_c1, Ne.symm h_arg_c2, Ne.symm h_arg_n, Ne.symm h_arg_off, Ne.symm h_arg_r11,
  Ne.symm h_out_c1, Ne.symm h_out_c2, Ne.symm h_out_n, Ne.symm h_out_off, Ne.symm h_out_r11,
  Ne.symm h_c1_c2, Ne.symm h_c1_n, Ne.symm h_c1_off, Ne.symm h_c1_r11,
  Ne.symm h_c2_n, Ne.symm h_c2_off, Ne.symm h_c2_r11,
  Ne.symm h_n_off, Ne.symm h_n_r11,
  Ne.symm h_off_r11,
  ↓reduceIte, get64_set64, get_low32, get_low64, sw32_64, sw32_ofNat])

/-- Exit at `done:` (index 100). -/
theorem done_at (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s t : MachineData) (ht : PostFrame out c1 c2 n off ymm s t)
    (hout : t.regs.get64 out = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64) :
    Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
      (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 100)⟩ := by
  sstep; cont
  exact Program.loop_done (post_of_done s t hout ht)

/-- Same-compression comparison data when `A ≠ B` and `0 < minChars`. -/
structure SameEncStrings (s : MachineData) (str arg : Reg64) (c₁ c₂ : BitVec 32)
    (d₁ d₂ : List UInt8) (A B : BitVec 64) (L T : Nat) : Prop where
  hA : s.regs.get64 str = A
  hB : s.regs.get64 arg = B
  hl₁ : d₁.length = strByteLen c₁
  hl₂ : d₂.length = strByteLen c₂
  hcomp : c₁.getLsbD 0 = c₂.getLsbD 0
  hL_def : L = min (strByteLen c₁) (strByteLen c₂)
  hL_pos : 0 < L
  hL_lt : L < 2 ^ 32
  hT_def : T = L + padBytes L
  hT_lt : T ≤ 2 ^ 32
  hsA : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome
  hsB : ∀ i < T, (s.dmem[B + 16#64 + .ofNat 64 i]?).isSome
  hdA : ∀ i (hi : i < L), s.dmem[A + 16#64 + .ofNat 64 i]? = some (d₁[i]'(by omega))
  hdB : ∀ i (hi : i < L), s.dmem[B + 16#64 + .ofNat 64 i]? = some (d₂[i]'(by omega))

omit [Host] in
theorem sameEnc_byte_eq {s : MachineData} {A B : BitVec 64} {L T : Nat}
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T)
    {i : Nat} (hi : i < L) :
    (byteAt s.dmem A i = byteAt s.dmem B i) ↔
      (d₁[i]'(by have := hS.hl₁; have := hS.hL_def; omega) =
       d₂[i]'(by have := hS.hl₂; have := hS.hL_def; omega)) := by
  simp only [byteAt, hS.hdA i hi, hS.hdB i hi, Option.getD_some]

omit [Host] in
theorem sameEnc_all_eq_spec {s : MachineData} {A B : BitVec 64} {L T : Nat}
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T)
    (hall : ∀ i < L, byteAt s.dmem A i = byteAt s.dmem B i) :
    compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) = (c₁ >>> 1) - (c₂ >>> 1) := by
  rw [sub_len_eq_compareToSpec_prefix c₁ c₂ d₁ d₂]
  apply compareToSpec_prefix
  intro i hi1 hi2
  have hl1 := hS.hl₁
  have hl2 := hS.hl₂
  have hcomp := hS.hcomp
  have hL := hS.hL_def
  by_cases hc : c₁.getLsbD 0 = true
  · have hc2 : c₂.getLsbD 0 = true := by rw [← hcomp]; exact hc
    have hL' : L = 2 * min (c₁ >>> 1).toNat (c₂ >>> 1).toNat := by
      rw [hL, strByteLen_uncompressed hc, strByteLen_uncompressed hc2]; omega
    have hi1' : i < (c₁ >>> 1).toNat := by rwa [strChars_length] at hi1
    have hi2' : i < (c₂ >>> 1).toNat := by rwa [strChars_length] at hi2
    have hlo : byteAt s.dmem A (2 * i) = byteAt s.dmem B (2 * i) := hall (2 * i) (by omega)
    have hhi : byteAt s.dmem A (2 * i + 1) = byteAt s.dmem B (2 * i + 1) := hall (2 * i + 1) (by omega)
    rw [sameEnc_byte_eq hS (by omega)] at hlo
    rw [sameEnc_byte_eq hS (by omega)] at hhi
    exact strChars_uncompressed_eq_of_bytes hc hc2 hl1 hl2 hi1 hi2 hlo hhi
  · have hc1f : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
    have hc2f : c₂.getLsbD 0 = false := by rw [← hcomp]; exact hc1f
    have hL' : L = min (c₁ >>> 1).toNat (c₂ >>> 1).toNat := by
      rw [hL, strByteLen_compressed hc1f, strByteLen_compressed hc2f]
    have hi1' : i < (c₁ >>> 1).toNat := by rwa [strChars_length] at hi1
    have hi2' : i < (c₂ >>> 1).toNat := by rwa [strChars_length] at hi2
    have hb := hall i (by omega)
    rw [sameEnc_byte_eq hS (by omega)] at hb
    exact strChars_compressed_eq_of_bytes hc1f hc2f hl1 hl2 hi1 hi2 hb

/-- Cut-point at `diff:` (index 49), entered with first differing byte `k < L`. -/
theorem diff_at (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A B : BitVec 64) (L T : Nat)
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T)
    (k : Nat) (t : MachineData) (ht : PostFrame out c1 c2 n off ymm s t)
    (hc1 : (t.regs.get64 c1).setWidth 32 = if c₁.getLsbD 0 then 1#32 else 0#32)
    (hoff : t.regs.get64 off = .ofNat 64 k)
    (hkL : k < L)
    (hpre : ∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i)
    (hdiff : byteAt s.dmem A k ≠ byteAt s.dmem B k) :
    Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
      (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 49)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, hl₁, hl₂, hcomp, hL_def, -, hL_lt, -, hT_lt, hsA, hsB, -, -⟩ := hS'
  have hstr : t.regs.get64 str = A := hA ▸ ht.2.1 str (by simp [h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11])
  have harg : t.regs.get64 arg = B := hB ▸ ht.2.1 arg (by simp [h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11])
  sstep; cont; sstep
  intro _
  simp only [hc1, BitVec.and_self]
  cont; sstep
  by_cases huc : c₁.getLsbD 0 = true
  · have huc2 : c₂.getLsbD 0 = true := by rw [← hcomp]; exact huc
    have hL' : L = 2 * min (c₁ >>> 1).toNat (c₂ >>> 1).toNat := by
      rw [hL_def, strByteLen_uncompressed huc, strByteLen_uncompressed huc2]; omega
    have hc_len : k / 2 < (strChars c₁ d₁).length ∧ k / 2 < (strChars c₂ d₂).length := by
      rw [strChars_length, strChars_length]; omega
    have hk_pair : 2 * (k / 2) + 1 < L := by rw [hL'] at hkL ⊢; exact uncomp_pair_lt hkL
    have hT_le : L ≤ T := by rw [hS.hT_def]; omega
    simp only [huc, ↓reduceIte, show (1#32 == 0#32) = false by decide, Bool.not_false,
      addrOf_label hlab (H := H) (i := 56) rfl]
    cont; sstep
    cont; sstep
    intro _
    simp only [hoff, sw32_ofNat, ofNat32_and_neg2 (show k < 2 ^ 32 by omega)]
    cont; sstep
    rs
    simp only [sw64_ofNat32 (show 2 * (k / 2) < 2 ^ 32 by omega)]
    rw [load_chunk _ _ (2 * (k / 2)) 2 T hsA (by omega)]
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Nat.add_zero]
    cont; sstep
    rs
    rw [load_chunk _ _ (2 * (k / 2)) 2 T hsB (by omega)]
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Nat.add_zero]
    cont; sstep
    rs
    cont; sstep
    simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
    cont
    have hspec : compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) =
        ((BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (k / 2)), byteAt s.dmem A (2 * (k / 2) + 1)])).zeroExtend 32 -
         (BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem B (2 * (k / 2)), byteAt s.dmem B (2 * (k / 2) + 1)])).zeroExtend 32) := by
      rw [compareToSpec_diff hc_len.1 hc_len.2]
      · rw [strChars_uncompressed_getElem huc (k / 2) hc_len.1,
          strChars_uncompressed_getElem huc2 (k / 2) hc_len.2]
        have hd1_0 : 2 * (k / 2) < d₁.length := by rw [hl₁, strByteLen_uncompressed huc]; omega
        have hd1_1 : 2 * (k / 2) + 1 < d₁.length := by rw [hl₁, strByteLen_uncompressed huc]; omega
        have hd2_0 : 2 * (k / 2) < d₂.length := by rw [hl₂, strByteLen_uncompressed huc2]; omega
        have hd2_1 : 2 * (k / 2) + 1 < d₂.length := by rw [hl₂, strByteLen_uncompressed huc2]; omega
        have ha0 := (sameEnc_byte_eq hS (show 2 * (k / 2) < L by omega))
        have ha1 := (sameEnc_byte_eq hS (show 2 * (k / 2) + 1 < L by omega))
        have hg10 : d₁.getD (2 * (k / 2)) 0 = d₁[2 * (k / 2)]'hd1_0 := by simp [List.getD, hd1_0]
        have hg11 : d₁.getD (2 * (k / 2) + 1) 0 = d₁[2 * (k / 2) + 1]'hd1_1 := by simp [List.getD, hd1_1]
        have hg20 : d₂.getD (2 * (k / 2)) 0 = d₂[2 * (k / 2)]'hd2_0 := by simp [List.getD, hd2_0]
        have hg21 : d₂.getD (2 * (k / 2) + 1) 0 = d₂[2 * (k / 2) + 1]'hd2_1 := by simp [List.getD, hd2_1]
        rw [hg10, hg11, hg20, hg21, word_diff_32]
        have hba0 : byteAt s.dmem A (2 * (k / 2)) = d₁[2 * (k / 2)]'hd1_0 := by
          simp [byteAt, hS.hdA (2 * (k / 2)) (by omega)]
        have hba1 : byteAt s.dmem A (2 * (k / 2) + 1) = d₁[2 * (k / 2) + 1]'hd1_1 := by
          simp [byteAt, hS.hdA (2 * (k / 2) + 1) (by omega)]
        have hbb0 : byteAt s.dmem B (2 * (k / 2)) = d₂[2 * (k / 2)]'hd2_0 := by
          simp [byteAt, hS.hdB (2 * (k / 2)) (by omega)]
        have hbb1 : byteAt s.dmem B (2 * (k / 2) + 1) = d₂[2 * (k / 2) + 1]'hd2_1 := by
          simp [byteAt, hS.hdB (2 * (k / 2) + 1) (by omega)]
        rw [hba0, hba1, hbb0, hbb1]
      · intro i hi
        have h1' : 2 * i < k := by omega
        have h2' : 2 * i + 1 < k := by omega
        have he1 := hpre (2 * i) h1'
        have he2 := hpre (2 * i + 1) h2'
        rw [sameEnc_byte_eq hS (by omega)] at he1
        rw [sameEnc_byte_eq hS (by omega)] at he2
        exact strChars_uncompressed_eq_of_bytes huc huc2 hl₁ hl₂ _ _ he1 he2
      · have hne_d : d₁[k]'(by omega) ≠ d₂[k]'(by omega) := by
          intro h; apply hdiff; exact (sameEnc_byte_eq hS hkL).mpr h
        exact strChars_uncompressed_ne_of_byte huc huc2 hl₁ hl₂ (by omega) (by omega) hne_d
          hc_len.1 hc_len.2
    refine done_at H s _ (by post_frame_tac) ?_
    rs
    simp only [hspec]
  · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr huc
    have hcf2 : c₂.getLsbD 0 = false := by rw [← hcomp]; exact hcf
    have hL' : L = min (c₁ >>> 1).toNat (c₂ >>> 1).toNat := by
      rw [hL_def, strByteLen_compressed hcf, strByteLen_compressed hcf2]
    have hk_len : k < (strChars c₁ d₁).length ∧ k < (strChars c₂ d₂).length := by
      rw [strChars_length, strChars_length]; omega
    have hT_le : L ≤ T := by rw [hS.hT_def]; omega
    simp only [hcf, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.not_true]
    cont; sstep
    rs
    rw [load_chunk _ _ k 1 T hsA (by omega)]
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Nat.add_zero]
    cont; sstep
    rs
    rw [load_chunk _ _ k 1 T hsB (by omega)]
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Nat.add_zero]
    cont; sstep
    rs
    cont; sstep
    simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
    cont
    have hspec : compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) =
        ((BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k])).zeroExtend 32 -
         (BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem B k])).zeroExtend 32) := by
      rw [compareToSpec_diff hk_len.1 hk_len.2]
      · rw [strChars_compressed_getElem hcf k hk_len.1, strChars_compressed_getElem hcf2 k hk_len.2]
        have hd1k : k < d₁.length := by rw [hl₁, strByteLen_compressed hcf, ← strChars_length (data := d₁)]; exact hk_len.1
        have hd2k : k < d₂.length := by rw [hl₂, strByteLen_compressed hcf2, ← strChars_length (data := d₂)]; exact hk_len.2
        have hg1 : d₁.getD k 0 = d₁[k]'hd1k := by simp [List.getD, hd1k]
        have hg2 : d₂.getD k 0 = d₂[k]'hd2k := by simp [List.getD, hd2k]
        rw [hg1, hg2, byte_diff_32]
        have hba : byteAt s.dmem A k = d₁[k]'hd1k := by simp [byteAt, hS.hdA k hkL]
        have hbb : byteAt s.dmem B k = d₂[k]'hd2k := by simp [byteAt, hS.hdB k hkL]
        rw [hba, hbb]
      · intro i hi
        have he := hpre i hi
        rw [sameEnc_byte_eq hS (by omega)] at he
        exact strChars_compressed_eq_of_bytes hcf hcf2 hl₁ hl₂ _ _ he
      · have hne_d : d₁[k]'(by omega) ≠ d₂[k]'(by omega) := by
          intro h; apply hdiff; exact (sameEnc_byte_eq hS hkL).mpr h
        exact strChars_compressed_ne_of_bytes hcf hcf2 hl₁ hl₂ hk_len.1 hk_len.2 hne_d
    refine done_at H s _ (by post_frame_tac) ?_
    rs
    simp only [hspec]

/-- Cut-point at `avx2_diff:` (index 44), reached after `jnz avx2_diff` from main loop or tail. -/
theorem avx2_diff_at (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A B : BitVec 64) (L T : Nat)
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T)
    (j : Nat) (t : MachineData) (ht : PreVzeroFrame out c1 c2 n off ymm s t)
    (hc1 : (t.regs.get64 c1).setWidth 32 = if c₁.getLsbD 0 then 1#32 else 0#32)
    (hoff : t.regs.get64 off = .ofNat 64 j)
    (hjL : j + 32 ≤ L)
    (hpre : ∀ i < j, byteAt s.dmem A i = byteAt s.dmem B i)
    (hc2 : (t.regs.get64 c2).setWidth 32 =
      BitVec.pmovmskb (BitVec.pcmpeqb
        (BitVec.ofInt 256 (Int.ofBytes ((List.range 32).map fun idx => byteAt s.dmem A (j + idx))))
        (BitVec.ofInt 256 (Int.ofBytes ((List.range 32).map fun idx => byteAt s.dmem B (j + idx))))))
    (hne : (t.regs.get64 c2).setWidth 32 ≠ -1#32) :
    Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
      (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 44)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, -, -, -, -, -, hL_lt, -, -, -, -, -, -⟩ := hS'
  have hstr : t.regs.get64 str = A := hA ▸ ht.2.1 str (by simp [h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11])
  have harg : t.regs.get64 arg = B := hB ▸ ht.2.1 arg (by simp [h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11])
  let bs₁ := (List.range 32).map fun idx => byteAt s.dmem A (j + idx)
  let bs₂ := (List.range 32).map fun idx => byteAt s.dmem B (j + idx)
  have hm_ne : BitVec.pmovmskb (BitVec.pcmpeqb
      (BitVec.ofInt 256 (Int.ofBytes bs₁)) (BitVec.ofInt 256 (Int.ofBytes bs₂))) ≠ -1#32 := by
    rwa [← hc2]
  obtain ⟨b, hb_lt, _, hb_bsf, hb_eq, hb_ne⟩ := pmovmskb_pcmpeqb_first_diff bs₁ bs₂ (by simp [bs₁]) (by simp [bs₂]) hm_ne
  have hnot_ne : ~~~(t.regs.get64 c2).setWidth 32 ≠ 0#32 := by
    intro h0
    apply hne
    have : ~~~(~~~((t.regs.get64 c2).setWidth 32)) = ~~~0#32 := congrArg (~~~·) h0
    simpa using this
  have hbsf_eq : BitVec.bsf (~~~(t.regs.get64 c2).setWidth 32) = BitVec.ofNat 32 b := by
    rw [hc2]; exact hb_bsf
  sstep; cont; sstep; cont; sstep; cont; sstep
  intro _ _ _ _ _
  rw [beq_eq_false_iff_ne.mpr hnot_ne]
  try simp only [Bool.false_eq_true, ↓reduceIte]
  cont; sstep
  rs
  simp only [hbsf_eq, ofNat32_add_lit, Nat.add_comm b j]
  cont
  refine diff_at h_distinct hlab H s A B L T hS (j + b) _ ?_ ?_ ?_ (by omega) ?_ ?_
  · refine ⟨rfl, fun r hr' => ?_, zmms_vzero_ok h_ymm ht.2.2⟩
    have hr'' := hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
    simp only [get64_set64, hr''.2.2.1, hr''.2.2.2.2.1, ↓reduceIte]
    exact ht.2.1 r hr'
  · simp [get64_set64, h_c1_off, h_c1_c2, hc1]
  · simp only [get64_set64, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j + b < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show j + b < 2 ^ 64 by omega)]
  · intro i hi
    by_cases hij : i < j
    · exact hpre i hij
    · have hib : i - j < b := by omega
      have hsame := hb_eq (i - j) hib
      simp only [bs₁, bs₂, List.getElem_map, List.getElem_range] at hsame
      rwa [Nat.add_sub_cancel' (by omega)] at hsame
  · simp only [bs₁, bs₂, List.getElem_map, List.getElem_range] at hb_ne
    exact hb_ne

/-- AVX2 loop induction (index 23) handling both full 32-byte chunks and the overlapping 32-byte tail. -/
theorem avx2_loop_ind (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (h_ymm : ymm.base ∈ lowMm)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A B : BitVec 64) (L T : Nat)
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T) :
    ∀ r k (t : MachineData), PreVzeroFrame out c1 c2 n off ymm s t →
      t.regs.get64 out = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64 →
      (t.regs.get64 c1).setWidth 32 = (if c₁.getLsbD 0 then 1#32 else 0#32) →
      t.regs.get64 off = .ofNat 64 k →
      (t.regs.get64 n).setWidth 32 = .ofNat 32 r →
      k + r = L → 32 ≤ r →
      (∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i) →
      Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
        (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
        (fun _ _ => False) ⟨t, Host.addrOf (H.start + 23)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, -, -, -, -, -, hL_lt, -, hT_lt, hsA, hsB, -, -⟩ := hS'
  have hT_le : L ≤ T := by rw [hS.hT_def]; omega
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t ht hout hc1 hoff hn hkr hr hpre
  have hstr : t.regs.get64 str = A := hA ▸ ht.2.1 str (by simp [h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11])
  have harg : t.regs.get64 arg = B := hB ▸ ht.2.1 arg (by simp [h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11])
  sstep; cont; sstep; rs
  rw [load_chunk _ _ k 32 T hsA (by omega)]
  simp only []
  cont; sstep; rs
  rw [load_chunk _ _ k 32 T hsB (by omega)]
  simp only []
  cont; sstep; cont; sstep; rs
  simp only [sub_beq_zero]
  cont; sstep
  by_cases heq : ∀ idx < 32, byteAt s.dmem A (k + idx) = byteAt s.dmem B (k + idx)
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
      cont; sstep; intro _; rs
      simp only [BitVec.and_self, ofNat32_eq_zero (show r - 32 < 2 ^ 32 by omega)]
      cont; sstep
      by_cases hrem0 : r - 32 = 0
      · simp only [hrem0, beq_self_eq_true, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 41) rfl]
        cont; sstep; cont; sstep; cont; sstep
        simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
        cont
        have hall : ∀ i < L, byteAt s.dmem A i = byteAt s.dmem B i := by
          have : k + 32 = L := by omega
          rw [← this]; exact prefix_ext hpre heq
        refine done_at H s _ ?_ ?_
        · refine ⟨rfl, fun r hr' => ?_, ?_⟩
          · have hr'' := hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
            simp only [get64_set64, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1, ↓reduceIte]
            exact ht.2.1 r hr'
          · rcases ht.2.2 with hzm | ⟨v, hzm⟩
            · exact Or.inr ⟨_, by rw [hzm]⟩
            · exact Or.inr ⟨_, by rw [hzm, zmms_set_set]⟩
        · rs; simp only [hout, sameEnc_all_eq_spec hS hall]
      · simp only [beq_eq_false_iff_ne.mpr hrem0, Bool.false_eq_true, ↓reduceIte]
        have h32L : 32 ≤ L := by omega
        have htail_addr : (BitVec.ofNat 64 (k + 32) + (BitVec.ofNat 32 (r - 32)).setWidth 64 + (-32#64 : BitVec 64)) =
            BitVec.ofNat 64 (L - 32) := by
          rw [sw64_ofNat32 (show r - 32 < 2 ^ 32 by omega),
            show (-32#64 : BitVec 64) = (-32 : Int64).toBitVec by decide]
          have h1 := leaq_tail_addr (k + 32) (r - 32)
          rcases h1 with heq' | hlt'
          · rw [show k + 32 + (r - 32) - 32 = L - 32 by omega] at heq'
            exact heq'
          · omega
        cont; sstep; rs
        simp only [htail_addr]
        cont; sstep; rs
        rw [load_chunk _ _ (L - 32) 32 T hsA (by omega)]
        simp only []
        cont; sstep; rs
        rw [load_chunk _ _ (L - 32) 32 T hsB (by omega)]
        simp only []
        cont; sstep; cont; sstep; rs
        simp only [sub_beq_zero]
        cont; sstep
        have hpre_all : ∀ i < k + 32, byteAt s.dmem A i = byteAt s.dmem B i := prefix_ext hpre heq
        have hpre_tail : ∀ i < L - 32, byteAt s.dmem A i = byteAt s.dmem B i :=
          fun i hi => hpre_all i (by omega)
        by_cases heq_tail : ∀ idx < 32, byteAt s.dmem A (L - 32 + idx) = byteAt s.dmem B (L - 32 + idx)
        · rw [(chunk_eq_iff s.dmem _ _ (L - 32) 32 256 rfl).mpr heq_tail]
          simp only [pm_self, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cont; sstep; cont; sstep; cont; sstep
          simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
          cont
          have hall : ∀ i < L, byteAt s.dmem A i = byteAt s.dmem B i := by
            have : (L - 32) + 32 = L := by omega
            rw [← this]; exact prefix_ext hpre_tail heq_tail
          refine done_at H s _ ?_ ?_
          · refine ⟨rfl, fun r hr' => ?_, ?_⟩
            · have hr'' := hr'
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
              simp only [get64_set64, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1, ↓reduceIte]
              exact ht.2.1 r hr'
            · rcases ht.2.2 with hzm | ⟨v, hzm⟩
              · exact Or.inr ⟨_, by rw [hzm]⟩
              · exact Or.inr ⟨_, by rw [hzm, zmms_set_set]⟩
          · rs; simp only [hout, sameEnc_all_eq_spec hS hall]
        · have hne_t := mt (chunk_eq_iff s.dmem _ _ (L - 32) 32 256 rfl).mp heq_tail
          have hm_t := mt (Proof.pmovmskb_pcmpeqb _ _).mp hne_t
          simp only [beq_eq_false_iff_ne.mpr hm_t, Bool.not_false, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 44) rfl]
          cont
          refine avx2_diff_at h_distinct h_ymm hlab H s A B L T hS (L - 32) _ (by pre_frame_tac)
            (by rs; exact hc1) (by rs) (by omega) hpre_tail (by rs) (by rs; exact hm_t)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 23) rfl]
      cont
      exact ih (r - 32) (by omega) (k + 32) _ (by pre_frame_tac) (by rs; exact hout)
        (by rs; exact hc1) (by rs) (by rs) (by omega) (by omega) (prefix_ext hpre heq)
  · have hne := mt (chunk_eq_iff s.dmem _ _ k 32 256 rfl).mp heq
    have hm := mt (Proof.pmovmskb_pcmpeqb _ _).mp hne
    simp only [beq_eq_false_iff_ne.mpr hm, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 44) rfl]
    cont
    refine avx2_diff_at h_distinct h_ymm hlab H s A B L T hS k _ (by pre_frame_tac)
      (by rs; exact hc1) (by rs) (by omega) hpre (by rs) (by rs; exact hm)

/-- Cut-point at `qword_diff:` (index 70). -/
theorem qword_diff_at (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A B : BitVec 64) (L T : Nat)
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T)
    (k rem : Nat) (t : MachineData) (ht : PostFrame out c1 c2 n off ymm s t)
    (hout : t.regs.get64 out = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64)
    (hc1 : (t.regs.get64 c1).setWidth 32 = if c₁.getLsbD 0 then 1#32 else 0#32)
    (hoff : t.regs.get64 off = .ofNat 64 k)
    (hn : (t.regs.get64 n).setWidth 32 = .ofNat 32 rem)
    (hkr : k + rem = L) (hrem_pos : 0 < rem) (hrem_lt : rem < 32)
    (hk8 : k % 8 = 0)
    (hpre : ∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i)
    (hc2 : t.regs.get64 c2 =
      BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem A (k + j))) ^^^
      BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem B (k + j))))
    (hne_xor : t.regs.get64 c2 ≠ 0#64) :
    Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
      (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 70)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, -, -, -, -, -, hL_lt, -, -, -, -, -, -⟩ := hS'
  have hstr : t.regs.get64 str = A := hA ▸ ht.2.1 str (by simp [h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11])
  have harg : t.regs.get64 arg = B := hB ▸ ht.2.1 arg (by simp [h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11])
  let bs₁ := (List.range 8).map fun j => byteAt s.dmem A (k + j)
  let bs₂ := (List.range 8).map fun j => byteAt s.dmem B (k + j)
  have hxor_ne : BitVec.ofInt 64 (Int.ofBytes bs₁) ^^^ BitVec.ofInt 64 (Int.ofBytes bs₂) ≠ 0#64 := by
    rwa [← hc2]
  obtain ⟨r, hr_lt, hr_sh, hr_eq, hr_ne⟩ :=
    xor_bsf_first_diff_byte bs₁ bs₂ (by simp [bs₁]) (by simp [bs₂]) hxor_ne
  have hbsf_sh : ((t.regs.get64 c2).bsf.setWidth 32).ushiftRight 3 = BitVec.ofNat 32 r := by
    apply bv32_eq_of_toNat
    · rw [hc2]; exact hr_sh
    · omega
  sstep; cont; sstep
  intro _ _ _ _ _
  rw [beq_eq_false_iff_ne.mpr hne_xor]
  try simp only [Bool.false_eq_true, ↓reduceIte]
  cont; sstep
  intro _ _
  rs
  simp only [hbsf_sh]
  cont; sstep
  rs
  simp only [hn, cf_ofNat32 (show r < 2 ^ 32 by omega) (show rem < 2 ^ 32 by omega)]
  cont; sstep
  by_cases hrem : rem ≤ r
  · have hnlt : ¬(r < rem) := by omega
    simp only [hnlt, decide_false, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 100) rfl]
    cont
    have hall : ∀ i < L, byteAt s.dmem A i = byteAt s.dmem B i := by
      intro i hi
      by_cases hik : i < k
      · exact hpre i hik
      · have hjr : i - k < r := by omega
        have hsame := hr_eq (i - k) hjr
        simp only [bs₁, bs₂, List.getElem_map, List.getElem_range] at hsame
        rwa [Nat.add_sub_cancel' (by omega)] at hsame
    refine done_at H s _ (by post_frame_tac) ?_
    rs; simp only [hout, sameEnc_all_eq_spec hS hall]
  · have hlt_rem : r < rem := by omega
    simp only [hlt_rem, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep
    rs
    simp only [ofNat32_add_lit, Nat.add_comm r k]
    cont; sstep
    simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 49) rfl]
    cont
    refine diff_at h_distinct hlab H s A B L T hS (k + r) _ (by post_frame_tac)
      (by rs; exact hc1) ?_ (by omega) ?_ ?_
    · simp only [get64_set64, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show k + r < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show k + r < 2 ^ 64 by omega)]
    · intro i hi
      by_cases hik : i < k
      · exact hpre i hik
      · have hsame := hr_eq (i - k) (by omega)
        simp only [bs₁, bs₂, List.getElem_map, List.getElem_range] at hsame
        rwa [Nat.add_sub_cancel' (by omega)] at hsame
    · simp only [bs₁, bs₂, List.getElem_map, List.getElem_range] at hr_ne
      exact hr_ne

/-- QWORD loop induction at `qword_loop:` (index 62) for `0 < L < 32`. -/
theorem qword_loop_ind (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A B : BitVec 64) (L T : Nat)
    (hS : SameEncStrings s str arg c₁ c₂ d₁ d₂ A B L T) :
    ∀ rem k (t : MachineData), PostFrame out c1 c2 n off ymm s t →
      t.regs.get64 out = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64 →
      (t.regs.get64 c1).setWidth 32 = (if c₁.getLsbD 0 then 1#32 else 0#32) →
      t.regs.get64 off = .ofNat 64 k →
      (t.regs.get64 n).setWidth 32 = .ofNat 32 rem →
      k + rem = L → 0 < rem → rem < 32 → k % 8 = 0 →
      (∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i) →
      Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
        (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
        (fun _ _ => False) ⟨t, Host.addrOf (H.start + 62)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hS' := hS
  obtain ⟨hA, hB, -, -, -, -, -, hL_lt, -, hT_lt, hsA, hsB, -, -⟩ := hS'
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro k t ht hout hc1 hoff hn hkr hpos hlt hk8 hpre
  have hstr : t.regs.get64 str = A := hA ▸ ht.2.1 str (by simp [h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11])
  have harg : t.regs.get64 arg = B := hB ▸ ht.2.1 arg (by simp [h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11])
  have hkq : k + 8 ≤ T := by rw [hS.hT_def]; exact qword_bound hk8 (by omega)
  sstep; cont; sstep; rs
  rw [load_chunk _ _ k 8 T hsA hkq]
  simp only []
  cont; sstep; rs
  rw [load_chunk _ _ k 8 T hsB hkq]
  simp only []
  intro _
  cont; sstep; rs
  by_cases heq : ∀ j < 8, byteAt s.dmem A (k + j) = byteAt s.dmem B (k + j)
  · rw [(chunk_eq_iff s.dmem _ _ k 8 64 rfl).mpr heq]
    simp only [BitVec.xor_self, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep; rs
    simp only [ofNat_add_lit]
    cont; sstep; rs
    simp only [hn, cf_ofNat32 (show rem < 2 ^ 32 by omega) (show 8 < 2 ^ 32 by decide),
      ofNat32_sub_eq_zero (show rem < 2 ^ 32 by omega) (show 8 < 2 ^ 32 by decide)]
    cont; sstep
    by_cases hgt : 8 < rem
    · have h1 : decide (rem < 8) = false := decide_eq_false (by omega)
      have h2 : decide (rem = 8) = false := decide_eq_false (by omega)
      simp only [h1, h2, Bool.not_false, Bool.and_self, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 62) rfl]
      cont
      refine ih (rem - 8) (by omega) (k + 8) _ (by post_frame_tac) (by rs; exact hout)
        (by rs; exact hc1) (by rs) ?_ (by omega) (by omega) (by omega) (by omega) (prefix_ext hpre heq)
      · rs; exact ofNat32_sub_lit (by omega)
    · have hle8 : rem ≤ 8 := Nat.le_of_not_lt hgt
      have hfl : (!(decide (rem < 8)) && !(decide (rem = 8))) = false := by
        rcases Nat.lt_or_eq_of_le hle8 with h1 | h2
        · simp [h1]
        · simp [h2]
      simp only [hfl, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
      cont
      have hall : ∀ i < L, byteAt s.dmem A i = byteAt s.dmem B i := by
        intro i hi
        by_cases hik : i < k
        · exact hpre i hik
        · have hj8 : i - k < 8 := by omega
          have := heq (i - k) hj8
          rwa [Nat.add_sub_cancel' (by omega)] at this
      refine done_at H s _ (by post_frame_tac) ?_
      rs; simp only [hout, sameEnc_all_eq_spec hS hall]
  · have hne_w :
        BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem A (k + j))) ≠
        BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem B (k + j))) :=
      mt (chunk_eq_iff s.dmem _ _ k 8 64 rfl).mp heq
    have hxor_ne :
        BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem A (k + j))) ^^^
        BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem B (k + j))) ≠ 0#64 :=
      fun h0 => hne_w (BitVec.xor_eq_zero_iff.mp h0)
    simp only [beq_eq_false_iff_ne.mpr hxor_ne, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 70) rfl]
    cont
    refine qword_diff_at h_distinct hlab H s A B L T hS k rem _ (by post_frame_tac)
      (by rs; exact hout) (by rs; exact hc1) (by rs) (by rs; exact hn) hkr hpos hlt hk8 hpre
      (by rs) (by rs; exact hxor_ne)

/-- Mixed-compression comparison data when `A ≠ B`, `0 < minChars`, and `c₁[0] ≠ c₂[0]`. -/
structure MixedEncStrings (s : MachineData) (str arg : Reg64) (c₁ c₂ : BitVec 32)
    (d₁ d₂ : List UInt8) (A_c A_u : BitVec 64) (d_c d_u : List UInt8) (minChars : Nat) : Prop where
  hA_c : A_c = if c₁.getLsbD 0 then s.regs.get64 arg else s.regs.get64 str
  hA_u : A_u = if c₁.getLsbD 0 then s.regs.get64 str else s.regs.get64 arg
  hd_c : d_c = if c₁.getLsbD 0 then d₂ else d₁
  hd_u : d_u = if c₁.getLsbD 0 then d₁ else d₂
  hl₁ : d₁.length = strByteLen c₁
  hl₂ : d₂.length = strByteLen c₂
  hmix : c₁.getLsbD 0 ≠ c₂.getLsbD 0
  hmin_def : minChars = min (c₁ >>> 1).toNat (c₂ >>> 1).toNat
  hmin_pos : 0 < minChars
  hmin_lt : minChars < 2 ^ 31
  hdc_len : minChars ≤ d_c.length
  hdu_len : 2 * minChars ≤ d_u.length
  hsc : ∀ i < minChars, (s.dmem[A_c + 16#64 + .ofNat 64 i]?).isSome
  hsu : ∀ i < 2 * minChars, (s.dmem[A_u + 16#64 + .ofNat 64 i]?).isSome
  hdc : ∀ i (hi : i < minChars), s.dmem[A_c + 16#64 + .ofNat 64 i]? = some (d_c[i]'(by omega))
  hdu : ∀ i (hi : i < 2 * minChars), s.dmem[A_u + 16#64 + .ofNat 64 i]? = some (d_u[i]'(by omega))

omit [Host] in
theorem mixed_chars_at (s : MachineData) {A_c A_u : BitVec 64} {d_c d_u : List UInt8}
    {minChars idx : Nat}
    (hM : MixedEncStrings s str arg c₁ c₂ d₁ d₂ A_c A_u d_c d_u minChars)
    (hidx : idx < minChars) :
    let bc := byteAt s.dmem A_c idx
    let bu0 := byteAt s.dmem A_u (2 * idx)
    let bu1 := byteAt s.dmem A_u (2 * idx + 1)
    let cc : BitVec 16 := bc.toBitVec.zeroExtend 16
    let cu : BitVec 16 := bu0.toBitVec.zeroExtend 16 ||| (bu1.toBitVec.zeroExtend 16 <<< 8)
    idx < (strChars c₁ d₁).length ∧ idx < (strChars c₂ d₂).length ∧
      ((c₁.getLsbD 0 = false → (strChars c₁ d₁)[idx]'(by rw [strChars_length]; have := hM.hmin_def; omega) = cc ∧
                                (strChars c₂ d₂)[idx]'(by rw [strChars_length]; have := hM.hmin_def; omega) = cu) ∧
       (c₁.getLsbD 0 = true → (strChars c₁ d₁)[idx]'(by rw [strChars_length]; have := hM.hmin_def; omega) = cu ∧
                               (strChars c₂ d₂)[idx]'(by rw [strChars_length]; have := hM.hmin_def; omega) = cc)) := by
  have h1 : idx < (strChars c₁ d₁).length := by rw [strChars_length]; have := hM.hmin_def; omega
  have h2 : idx < (strChars c₂ d₂).length := by rw [strChars_length]; have := hM.hmin_def; omega
  refine ⟨h1, h2, ⟨fun hc1 => ?_, fun hc1 => ?_⟩⟩
  · have hc2 : c₂.getLsbD 0 = true := by
      have hm := hM.hmix; cases h : c₂.getLsbD 0 <;> simp_all
    have hdc_eq : d_c = d₁ := by rw [hM.hd_c, hc1]; simp
    have hdu_eq : d_u = d₂ := by rw [hM.hd_u, hc1]; simp
    have hdcl : minChars ≤ d₁.length := hdc_eq ▸ hM.hdc_len
    have hdul : 2 * minChars ≤ d₂.length := hdu_eq ▸ hM.hdu_len
    have hbc : byteAt s.dmem A_c idx = d₁[idx]'(by omega) := by
      simp [byteAt, hM.hdc idx hidx, hdc_eq]
    have hbu0 : byteAt s.dmem A_u (2 * idx) = d₂[2 * idx]'(by omega) := by
      simp [byteAt, hM.hdu (2 * idx) (by omega), hdu_eq]
    have hbu1 : byteAt s.dmem A_u (2 * idx + 1) = d₂[2 * idx + 1]'(by omega) := by
      simp [byteAt, hM.hdu (2 * idx + 1) (by omega), hdu_eq]
    have hg1 : d₁.getD idx 0 = d₁[idx]'(by omega) := by simp [List.getD, show idx < d₁.length by omega]
    have hg2 : d₂.getD (2 * idx) 0 = d₂[2 * idx]'(by omega) := by simp [List.getD, show 2 * idx < d₂.length by omega]
    have hg3 : d₂.getD (2 * idx + 1) 0 = d₂[2 * idx + 1]'(by omega) := by simp [List.getD, show 2 * idx + 1 < d₂.length by omega]
    rw [strChars_compressed_getElem hc1 idx h1, strChars_uncompressed_getElem hc2 idx h2]
    rw [hg1, hg2, hg3, ← hbc, ← hbu0, ← hbu1]
    exact ⟨rfl, rfl⟩
  · have hc2 : c₂.getLsbD 0 = false := by
      have hm := hM.hmix; cases h : c₂.getLsbD 0 <;> simp_all
    have hdc_eq : d_c = d₂ := by rw [hM.hd_c, hc1]; simp
    have hdu_eq : d_u = d₁ := by rw [hM.hd_u, hc1]; simp
    have hdcl : minChars ≤ d₂.length := hdc_eq ▸ hM.hdc_len
    have hdul : 2 * minChars ≤ d₁.length := hdu_eq ▸ hM.hdu_len
    have hbc : byteAt s.dmem A_c idx = d₂[idx]'(by omega) := by
      simp [byteAt, hM.hdc idx hidx, hdc_eq]
    have hbu0 : byteAt s.dmem A_u (2 * idx) = d₁[2 * idx]'(by omega) := by
      simp [byteAt, hM.hdu (2 * idx) (by omega), hdu_eq]
    have hbu1 : byteAt s.dmem A_u (2 * idx + 1) = d₁[2 * idx + 1]'(by omega) := by
      simp [byteAt, hM.hdu (2 * idx + 1) (by omega), hdu_eq]
    have hg1 : d₂.getD idx 0 = d₂[idx]'(by omega) := by simp [List.getD, show idx < d₂.length by omega]
    have hg2 : d₁.getD (2 * idx) 0 = d₁[2 * idx]'(by omega) := by simp [List.getD, show 2 * idx < d₁.length by omega]
    have hg3 : d₁.getD (2 * idx + 1) 0 = d₁[2 * idx + 1]'(by omega) := by simp [List.getD, show 2 * idx + 1 < d₁.length by omega]
    rw [strChars_uncompressed_getElem hc1 idx h1, strChars_compressed_getElem hc2 idx h2]
    rw [hg1, hg2, hg3, ← hbc, ← hbu0, ← hbu1]
    exact ⟨rfl, rfl⟩

/-- Mixed loop induction at `mixed_loop:` (index 85). -/
theorem mixed_loop_ind (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A_c A_u : BitVec 64) (d_c d_u : List UInt8) (minChars : Nat)
    (hM : MixedEncStrings s str arg c₁ c₂ d₁ d₂ A_c A_u d_c d_u minChars) :
    ∀ rem idx (t : MachineData), PostFrame out c1 c2 n off ymm s t →
      t.regs.get64 out = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64 →
      t.regs.get64 c2 = A_c + .ofNat 64 idx →
      t.regs.get64 off = A_u + .ofNat 64 (2 * idx) →
      (t.regs.get64 n).setWidth 32 = .ofNat 32 (2 * rem - if c₁.getLsbD 0 then 1 else 0) →
      idx + rem = minChars → 0 < rem →
      (∀ i < idx, ∀ (hi1 : i < (strChars c₁ d₁).length) (hi2 : i < (strChars c₂ d₂).length),
        (strChars c₁ d₁)[i]'hi1 = (strChars c₂ d₂)[i]'hi2) →
      Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
        (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
        (fun _ _ => False) ⟨t, Host.addrOf (H.start + 85)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
  intro idx t ht hout hc2 hoff hn hidx hpos hpre
  have hstr : True := trivial
  have harg : True := trivial
  have hidx_lt : idx < minChars := by omega
  have ha1 : s.dmem.loadInt (A_c + .ofNat 64 idx + 16#64) 1 =
      some (Int.ofBytes [byteAt s.dmem A_c idx]) := by
    have := load_chunk s.dmem A_c idx 1 minChars hM.hsc (by omega)
    simpa [List.range, List.range.loop] using this
  have ha2 : s.dmem.loadInt (A_u + .ofNat 64 (2 * idx) + 16#64) 2 =
      some (Int.ofBytes [byteAt s.dmem A_u (2 * idx), byteAt s.dmem A_u (2 * idx + 1)]) := by
    have := load_chunk s.dmem A_u (2 * idx) 2 (2 * minChars) hM.hsu (by omega)
    simpa [List.range, List.range.loop] using this
  let bc := byteAt s.dmem A_c idx
  let bu0 := byteAt s.dmem A_u (2 * idx)
  let bu1 := byteAt s.dmem A_u (2 * idx + 1)
  let cc : BitVec 16 := bc.toBitVec.zeroExtend 16
  let cu : BitVec 16 := bu0.toBitVec.zeroExtend 16 ||| (bu1.toBitVec.zeroExtend 16 <<< 8)
  sstep; cont; sstep
  rs
  rw [hc2, ha1]
  simp only []
  cont; sstep
  rs
  rw [ha2]
  simp only []
  cont; sstep
  rs
  simp only [ofInt8_zeroExtend32, ofInt16_zeroExtend32]
  change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 89)⟩
  cont; sstep
  by_cases hch : cc = cu
  · dsimp only [cc, cu] at hch
    rw [hch, BitVec.sub_self]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep; rs
    simp only [hc2, show (1#64 : BitVec 64) + (A_c + .ofNat 64 idx) = A_c + .ofNat 64 (idx + 1) by
      rw [← BitVec.add_assoc, BitVec.add_comm 1#64 A_c, BitVec.add_assoc, BitVec.add_comm 1#64,
        ofNat_add_lit, Nat.add_comm 1 idx]]
    cont; sstep; rs
    simp only [show (2#64 : BitVec 64) + (A_u + .ofNat 64 (2 * idx)) = A_u + .ofNat 64 (2 * (idx + 1)) by
      rw [← BitVec.add_assoc, BitVec.add_comm 2#64 A_u, BitVec.add_assoc, BitVec.add_comm 2#64,
        ofNat_add_lit, show 2 + 2 * idx = 2 * (idx + 1) by omega]]
    cont; sstep; rs
    have hn_lt : 2 * rem - (if c₁.getLsbD 0 then 1 else 0) < 2 ^ 32 := by
      have := hM.hmin_lt; omega
    simp only [hn, cf_ofNat32 hn_lt (show 2 < 2 ^ 32 by decide),
      ofNat32_sub_eq_zero hn_lt (show 2 < 2 ^ 32 by decide)]
    cont; sstep
    have hpre' : ∀ i < idx + 1, ∀ (hi1 : i < (strChars c₁ d₁).length) (hi2 : i < (strChars c₂ d₂).length),
        (strChars c₁ d₁)[i]'hi1 = (strChars c₂ d₂)[i]'hi2 := by
      intro i hi hi1 hi2
      by_cases hi_old : i < idx
      · exact hpre i hi_old hi1 hi2
      · have hi_eq : i = idx := by omega
        subst hi_eq
        obtain ⟨_, _, hcs, hcu⟩ := mixed_chars_at s hM hidx_lt
        cases hflag : c₁.getLsbD 0
        · obtain ⟨e1, e2⟩ := hcs hflag; rw [e1, e2, hch]
        · obtain ⟨e1, e2⟩ := hcu hflag; rw [e1, e2, hch]
    by_cases hgt1 : 1 < rem
    · have hgt2 : 2 < 2 * rem - (if c₁.getLsbD 0 then 1 else 0) := by split <;> omega
      have h1 : decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) < 2) = false := decide_eq_false (by omega)
      have h2 : decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) = 2) = false := decide_eq_false (by omega)
      simp only [h1, h2, Bool.not_false, Bool.and_self, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 85) rfl]
      cont
      refine ih (rem - 1) (by omega) (idx + 1) _ (by post_frame_tac) (by rs; exact hout)
        (by rs) (by rs) ?_ (by omega) (by omega) hpre'
      · rs; rw [ofNat32_sub_lit (by split <;> omega)]
        congr 1; split <;> omega
    · have hrem1 : rem = 1 := by omega
      have hn_le2 : 2 * rem - (if c₁.getLsbD 0 then 1 else 0) ≤ 2 := by split <;> omega
      have hfl : (!(decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) < 2)) &&
          !(decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) = 2))) = false := by
        cases h_a : decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) < 2) <;>
        cases h_b : decide (2 * rem - (if c₁.getLsbD 0 then 1 else 0) = 2) <;> simp_all <;> omega
      simp only [hfl, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 100) rfl]
      cont
      have hall : compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) = (c₁ >>> 1) - (c₂ >>> 1) := by
        rw [sub_len_eq_compareToSpec_prefix c₁ c₂ d₁ d₂]
        apply compareToSpec_prefix
        intro i hi1 hi2
        have hilt : i < idx + 1 := by
          rw [strChars_length] at hi1 hi2
          have := hM.hmin_def
          omega
        exact hpre' i hilt hi1 hi2
      refine done_at H s _ (by post_frame_tac) ?_
      rs; simp only [hout, hall]
  · have hdiff32 : cc.zeroExtend 32 - cu.zeroExtend 32 ≠ 0#32 := by
      intro h0
      apply hch
      have heq32 : cc.zeroExtend 32 = cu.zeroExtend 32 := by
        have := BitVec.sub_add_cancel (cc.zeroExtend 32) (cu.zeroExtend 32)
        rw [h0, BitVec.zero_add] at this; exact this.symm
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have := congrArg (fun v : BitVec 32 => v.getLsbD i) heq32
      simpa [BitVec.zeroExtend, hi, show i < 32 by omega] using this
    dsimp only [bc, bu0, bu1, cc, cu] at hdiff32
    simp only [beq_eq_false_iff_ne.mpr hdiff32, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 95) rfl]
    cont; sstep; rs
    cont; sstep; rs
    cont; sstep; rs
    cont; sstep; rs
    intro _
    simp only [hn, ofNat32_and1_eq_zero]
    cont; sstep; rs
    have hrem_mod : (2 * rem - (if c₁.getLsbD 0 then 1 else 0)) % 2 =
        if c₁.getLsbD 0 then 1 else 0 := by
      cases c₁.getLsbD 0 <;> simp <;> omega
    simp only [hrem_mod]
    obtain ⟨hl1, hl2, hcs, hcu⟩ := mixed_chars_at s hM hidx_lt
    have hpre_spec : ∀ (i : Nat) (hi : i < idx),
        (strChars c₁ d₁)[i]'(Nat.lt_trans hi hl1) = (strChars c₂ d₂)[i]'(Nat.lt_trans hi hl2) :=
      fun i hi => hpre i hi _ _
    cases hflag : c₁.getLsbD 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cont
      refine done_at H s _ (by post_frame_tac) ?_
      rs
      obtain ⟨e1, e2⟩ := hcs hflag
      have hne_c : (strChars c₁ d₁)[idx]'hl1 ≠ (strChars c₂ d₂)[idx]'hl2 := by
        rw [e1, e2]; exact hch
      rw [compareToSpec_diff hl1 hl2 hpre_spec hne_c, e1, e2]
      rfl
    · simp only [↓reduceIte, show decide (1 = 0) = false by decide, Bool.not_false]
      cont
      refine done_at H s _ (by post_frame_tac) ?_
      rs
      obtain ⟨e1, e2⟩ := hcu hflag
      have hne_c : (strChars c₁ d₁)[idx]'hl1 ≠ (strChars c₂ d₂)[idx]'hl2 := by
        rw [e1, e2]; exact Ne.symm hch
      rw [compareToSpec_diff hl1 hl2 hpre_spec hne_c, e1, e2, neg_32_ze64 cc cu]

/-- Cut-point at `mixed_init:` (index 77). -/
theorem mixed_init_at (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringCompareToNoCheckProg str arg out c1 c2 n off ymm))
    (s : MachineData) (A_c A_u : BitVec 64) (d_c d_u : List UInt8) (minChars : Nat)
    (hM : MixedEncStrings s str arg c₁ c₂ d₁ d₂ A_c A_u d_c d_u minChars)
    (t : MachineData) (ht : PostFrame out c1 c2 n off ymm s t)
    (hstr_r : t.regs.get64 str = s.regs.get64 str)
    (harg_r : t.regs.get64 arg = s.regs.get64 arg)
    (hout : t.regs.get64 out = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64)
    (hc1 : (t.regs.get64 c1).setWidth 32 = c₁)
    (hn : (t.regs.get64 n).setWidth 32 = .ofNat 32 minChars) :
    Program.Loop (stringCompareToNoCheckProg str arg out c1 c2 n off ymm) H
      (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 77)⟩ := by
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  have hstr : t.regs.get64 str = s.regs.get64 str := hstr_r
  have harg : t.regs.get64 arg = s.regs.get64 arg := harg_r
  have hoff : True := trivial
  sstep; rs; cont; sstep; rs; cont; sstep; rs; cont; sstep; rs
  intro _
  simp only [hc1, c1_and1_eq]
  cont; sstep; rs
  cont; sstep; rs
  cont; sstep; rs
  intro _
  simp only [hn]
  have hshl : BitVec.ofNat 32 minChars <<< (1 : Nat) = BitVec.ofNat 32 (2 * minChars) := by
    apply BitVec.eq_of_toNat_eq
    have := hM.hmin_lt
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show minChars < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show 2 * minChars < 2 ^ 32 by omega)]
    omega
  simp only [hshl]
  cont; sstep; rs
  have hsub : BitVec.ofNat 32 (2 * minChars) - (if c₁.getLsbD 0 then 1#32 else 0#32) =
      BitVec.ofNat 32 (2 * minChars - if c₁.getLsbD 0 then 1 else 0) := by
    cases c₁.getLsbD 0
    · simp
    · simp only [↓reduceIte]; exact ofNat32_sub_lit (by have := hM.hmin_pos; omega)
  simp only [hsub]
  cont
  refine mixed_loop_ind h_distinct hlab H s A_c A_u d_c d_u minChars hM minChars 0 _
    (by post_frame_tac) ?_ ?_ ?_ ?_ (by omega) hM.hmin_pos (fun i hi => absurd hi (Nat.not_lt_zero _))
  · rs; exact hout
  · rs
    have hAc := hM.hA_c
    by_cases h : c₁.getLsbD 0 = true <;> simp [h, hAc]
  · rs
    have hAu := hM.hA_u
    by_cases h : c₁.getLsbD 0 = true <;> simp [h, hAu]
  · rs

omit [Host] in
theorem sameEncStrings_of {s : MachineData} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop}
    (_hAB : s.regs.get64 str ≠ s.regs.get64 arg)
    (hmem : (StringAt (s.regs.get64 str) c₁ d₁ ⋆ StringAt (s.regs.get64 arg) c₂ d₂ ⋆ R) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hb₁ : (s.regs.get64 str).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hcomp : c₁.getLsbD 0 = c₂.getLsbD 0)
    (hmin_pos : 0 < min (c₁ >>> 1).toNat (c₂ >>> 1).toNat) :
    SameEncStrings s str arg c₁ c₂ d₁ d₂ (s.regs.get64 str) (s.regs.get64 arg)
      (min (strByteLen c₁) (strByteLen c₂))
      (min (strByteLen c₁) (strByteLen c₂) + padBytes (min (strByteLen c₁) (strByteLen c₂))) := by
  let L := min (strByteLen c₁) (strByteLen c₂)
  let T := L + padBytes L
  have hT_le₁ : T ≤ strByteLen c₁ + padBytes (strByteLen c₁) :=
    padBytes_mono (Nat.min_le_left _ _)
  have hT_le₂ : T ≤ strByteLen c₂ + padBytes (strByteLen c₂) :=
    padBytes_mono (Nat.min_le_right _ _)
  have h_all1 : allocatedBytes (strByteLen c₁) = strByteLen c₁ + padBytes (strByteLen c₁) := rfl
  have h_all2 : allocatedBytes (strByteLen c₂) = strByteLen c₂ + padBytes (strByteLen c₂) := rfl
  have hT_lt : T ≤ 2 ^ 32 := by omega
  have hL_lt : L < 2 ^ 32 := by omega
  have hL_pos : 0 < L := by
    cases h : c₁.getLsbD 0
    · have h2 : c₂.getLsbD 0 = false := by rw [← hcomp]; exact h
      simp only [L, strByteLen_compressed h, strByteLen_compressed h2]
      exact hmin_pos
    · have h2 : c₂.getLsbD 0 = true := by rw [← hcomp]; exact h
      simp only [L, strByteLen_uncompressed h, strByteLen_uncompressed h2]
      omega
  have hpl₁ : (padded d₁).length = strByteLen c₁ + padBytes (strByteLen c₁) := by simp [hl₁]
  have hpl₂ : (padded d₂).length = strByteLen c₂ + padBytes (strByteLen c₂) := by simp [hl₂]
  have h1_lt : (padded d₁).length ≤ 2 ^ 64 := by omega
  have h2_lt : (padded d₂).length ≤ 2 ^ 64 := by
    have := strByteLen_lt c₂
    have : padBytes (strByteLen c₂) < 8 := by unfold padBytes; omega
    omega
  have dA : ∀ i (hi : i < T),
      s.dmem[s.regs.get64 str + 16#64 + .ofNat 64 i]? = some ((padded d₁)[i]'(by omega)) :=
    fun i hi => sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data _ h1_lt))
  have dB : ∀ i (hi : i < T),
      s.dmem[s.regs.get64 arg + 16#64 + .ofNat 64 i]? = some ((padded d₂)[i]'(by omega)) :=
    fun i hi => sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data _ h2_lt))
  have hdA : ∀ i (hi : i < L),
      s.dmem[s.regs.get64 str + 16#64 + .ofNat 64 i]? = some (d₁[i]'(by omega)) := by
    intro i hi
    rw [dA i (by unfold T padBytes; omega)]
    congr 1; exact List.getElem_append_left (by omega)
  have hdB : ∀ i (hi : i < L),
      s.dmem[s.regs.get64 arg + 16#64 + .ofNat 64 i]? = some (d₂[i]'(by omega)) := by
    intro i hi
    rw [dB i (by unfold T padBytes; omega)]
    congr 1; exact List.getElem_append_left (by omega)
  exact ⟨rfl, rfl, hl₁, hl₂, hcomp, rfl, hL_pos, hL_lt, rfl, hT_lt,
    fun i hi => by simp [dA i hi], fun i hi => by simp [dB i hi], hdA, hdB⟩

omit [Host] in
theorem mixedEncStrings_of {s : MachineData} {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    {R : Mem 64 → Prop}
    (hmem : (StringAt (s.regs.get64 str) c₁ d₁ ⋆ StringAt (s.regs.get64 arg) c₂ d₂ ⋆ R) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hmix : c₁.getLsbD 0 ≠ c₂.getLsbD 0)
    (hmin_pos : 0 < min (c₁ >>> 1).toNat (c₂ >>> 1).toNat) :
    let A_c := if c₁.getLsbD 0 then s.regs.get64 arg else s.regs.get64 str
    let A_u := if c₁.getLsbD 0 then s.regs.get64 str else s.regs.get64 arg
    let d_c := if c₁.getLsbD 0 then d₂ else d₁
    let d_u := if c₁.getLsbD 0 then d₁ else d₂
    MixedEncStrings s str arg c₁ c₂ d₁ d₂ A_c A_u d_c d_u (min (c₁ >>> 1).toNat (c₂ >>> 1).toNat) := by
  have h1_lt : (padded d₁).length ≤ 2 ^ 64 := by
    have := strByteLen_lt c₁; have : padBytes (strByteLen c₁) < 8 := by unfold padBytes; omega
    simp [hl₁]; omega
  have h2_lt : (padded d₂).length ≤ 2 ^ 64 := by
    have := strByteLen_lt c₂; have : padBytes (strByteLen c₂) < 8 := by unfold padBytes; omega
    simp [hl₂]; omega
  have hmin_lt : min (c₁ >>> 1).toNat (c₂ >>> 1).toNat < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (ushiftRight1_lt c₁)
  have hp₁ : d₁.length ≤ (padded d₁).length := by simp
  have hp₂ : d₂.length ≤ (padded d₂).length := by simp
  refine ⟨rfl, rfl, rfl, rfl, hl₁, hl₂, hmix, rfl, hmin_pos, hmin_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hc : c₁.getLsbD 0 = true
    · have hc2 : c₂.getLsbD 0 = false := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hc, ↓reduceIte]; rw [hl₂, strByteLen_compressed hc2]; exact Nat.min_le_right _ _
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]; rw [hl₁, strByteLen_compressed hcf]; exact Nat.min_le_left _ _
  · by_cases hc : c₁.getLsbD 0 = true
    · simp only [hc, ↓reduceIte]; rw [hl₁, strByteLen_uncompressed hc]; omega
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      have hc2 : c₂.getLsbD 0 = true := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]; rw [hl₂, strByteLen_uncompressed hc2]; omega
  · intro i hi
    by_cases hc : c₁.getLsbD 0 = true
    · have hc2 : c₂.getLsbD 0 = false := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hc, ↓reduceIte]
      rw [sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data (i := i) (by
        rw [hl₂, strByteLen_compressed hc2] at hp₂; omega) h2_lt))]; rfl
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      rw [sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data (i := i) (by
        rw [hl₁, strByteLen_compressed hcf] at hp₁; omega) h1_lt))]; rfl
  · intro i hi
    by_cases hc : c₁.getLsbD 0 = true
    · simp only [hc, ↓reduceIte]
      rw [sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data (i := i) (by
        rw [hl₁, strByteLen_uncompressed hc] at hp₁; omega) h1_lt))]; rfl
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      have hc2 : c₂.getLsbD 0 = true := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      rw [sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data (i := i) (by
        rw [hl₂, strByteLen_uncompressed hc2] at hp₂; omega) h2_lt))]; rfl
  · intro i hi
    by_cases hc : c₁.getLsbD 0 = true
    · have hc2 : c₂.getLsbD 0 = false := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hc, ↓reduceIte]
      have h := sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data (i := i) (by
        rw [hl₂, strByteLen_compressed hc2] at hp₂; omega) h2_lt))
      rw [h]; congr 1; refine List.getElem_append_left (by rw [hl₂, strByteLen_compressed hc2]; omega)
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      have h := sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data (i := i) (by
        rw [hl₁, strByteLen_compressed hcf] at hp₁; omega) h1_lt))
      rw [h]; congr 1; refine List.getElem_append_left (by rw [hl₁, strByteLen_compressed hcf]; omega)
  · intro i hi
    by_cases hc : c₁.getLsbD 0 = true
    · simp only [hc, ↓reduceIte]
      have h := sep_get_l hmem (fun _ h => sep_get_l h (stringAt_data (i := i) (by
        rw [hl₁, strByteLen_uncompressed hc] at hp₁; omega) h1_lt))
      rw [h]; congr 1; refine List.getElem_append_left (by rw [hl₁, strByteLen_uncompressed hc]; omega)
    · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      have hc2 : c₂.getLsbD 0 = true := by cases h : c₂.getLsbD 0 <;> simp_all
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      have h := sep_get_l hmem (fun _ h => sep_get_r h (stringAt_data (i := i) (by
        rw [hl₂, strByteLen_uncompressed hc2] at hp₂; omega) h2_lt))
      rw [h]; congr 1; refine List.getElem_append_left (by rw [hl₂, strByteLen_uncompressed hc2]; omega)

end

end CompareToProof

open CompareToProof Proof in
/--
Correctness of the no-check AVX2 `String.compareTo` lowering `stringCompareToNoCheckProg`.
Implicit `TMP` (`.r11`) is included in the clobbered registers alongside `c1, c2, n, off`.
-/
public theorem stringCompareToNoCheck_correct [Host]
    (str arg out c1 c2 n off : Reg64) (ymm : AvxReg .W256)
    (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (h_ymm : ymm.base ∈ [RegMm.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10,
      .mm11, .mm12, .mm13, .mm14, .mm15])
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧
        (s.regs.get64 str).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32 ∧
        (s.regs.get64 arg).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32 ∧
        d₁.length = strByteLen c₁ ∧
        d₂.length = strByteLen c₂ ∧
        ∃ R, StringsInMem (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ R s.dmem ⦄
      stringCompareToNoCheckProg str arg out c1 c2 n off ymm
    ⦃ fun _ => StringCompareToPost out [c1, c2, n, off, .r11] [ymm]
        (strChars c₁ d₁) (strChars c₂ d₂) s₀;
      fun _ _ => False ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hb₁, hb₂, hl₁, hl₂, ⟨R, hmem⟩⟩
  have hA32 : (s.regs.get64 str).toNat < 2 ^ 32 := by omega
  have hB32 : (s.regs.get64 arg).toNat < 2 ^ 32 := by omega
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h_str_arg, h_str_out, h_str_c1, h_str_c2, h_str_n, h_str_off, h_str_r11⟩,
    ⟨h_arg_out, h_arg_c1, h_arg_c2, h_arg_n, h_arg_off, h_arg_r11⟩,
    ⟨h_out_c1, h_out_c2, h_out_n, h_out_off, h_out_r11⟩,
    ⟨h_c1_c2, h_c1_n, h_c1_off, h_c1_r11⟩,
    ⟨h_c2_n, h_c2_off, h_c2_r11⟩,
    ⟨h_n_off, h_n_r11⟩,
    h_off_r11, -⟩ := hd
  apply Program.wp_of_loop
  intro H
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  sstep
  intro _
  simp only [BitVec.xor_self]
  cont; sstep
  simp only [h_str_out, h_arg_out, ↓reduceIte, sub_beq_zero, low32_beq hA32 hB32]
  cont; sstep
  by_cases hAB : s.regs.get64 str = s.regs.get64 arg
  · simp only [hAB, beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 100) rfl]
    cont
    refine done_at H s _ ⟨rfl, fun r hr => ?_, Or.inl rfl⟩ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [get64_set64, hr.1]
    · simp [get64_set64, stringsInMem_same hmem hAB]
  simp only [beq_eq_false_iff_ne.mpr hAB, Bool.false_eq_true, ↓reduceIte]
  rw [StringsInMem, ite_eq_right hAB] at hmem
  have cA := fun i (hi : i < 4) => sep_get_l hmem (fun _ h => sep_get_l h (stringAt_cnt (i := i) hi))
  have cB := fun i (hi : i < 4) => sep_get_l hmem (fun _ h => sep_get_r h (stringAt_cnt (i := i) hi))
  have ht0 : PostFrame out c1 c2 n off ymm s s := ⟨rfl, fun _ _ => rfl, Or.inl rfl⟩
  cont; sstep
  simp only [h_str_out, ↓reduceIte]
  rw [load_count _ _ _ cA]
  simp only [cnt_val]
  cont; sstep
  simp only [h_arg_out, h_arg_c1, ↓reduceIte]
  rw [load_count _ _ _ cB]
  simp only [cnt_val]
  cont; sstep
  simp only [h_c1_c2, ↓reduceIte, sw32_64]
  cont; sstep
  simp only [h_c2_n, ↓reduceIte, sw32_64]
  cont; sstep
  intro _
  cont; sstep
  intro _
  cont; sstep
  simp only [h_n_off, Ne.symm h_n_off, ↓reduceIte, sw32_64]
  cont; sstep
  simp only [Ne.symm h_out_off, ↓reduceIte, sw32_64]
  have h1_lt : (c₁ >>> 1).toNat < 2 ^ 31 := ushiftRight1_lt c₁
  have h2_lt : (c₂ >>> 1).toNat < 2 ^ 31 := ushiftRight1_lt c₂
  cont; sstep
  simp only [Ne.symm h_out_n, h_n_off, Ne.symm h_out_off, ↓reduceIte, sw32_64,
    sub_cmovg_cond (c₁.ushiftRight 1) (c₂.ushiftRight 1) h1_lt h2_lt]
  let minChars := min (c₁ >>> 1).toNat (c₂ >>> 1).toNat
  have h_min_val :
      (if decide ((c₂.ushiftRight 1).toNat < (c₁.ushiftRight 1).toNat) = true
       then c₂.ushiftRight 1 else c₁.ushiftRight 1) =
        BitVec.ofNat 32 minChars := by
    apply BitVec.eq_of_toNat_eq
    change (if decide ((c₂ >>> 1).toNat < (c₁ >>> 1).toNat) = true
            then c₂ >>> 1 else c₁ >>> 1).toNat = (BitVec.ofNat 32 minChars).toNat
    by_cases hlt : (c₂ >>> 1).toNat < (c₁ >>> 1).toNat
    · have hid : (if decide ((c₂ >>> 1).toNat < (c₁ >>> 1).toNat) = true then c₂ >>> 1 else c₁ >>> 1) = c₂ >>> 1 := by
        rw [decide_eq_true hlt]; rfl
      rw [hid, BitVec.toNat_ofNat]
      simp only [minChars, Nat.min_eq_right (Nat.le_of_lt hlt)]
      exact (Nat.mod_eq_of_lt (by omega : (c₂ >>> 1).toNat < 2 ^ 32)).symm
    · have hid : (if decide ((c₂ >>> 1).toNat < (c₁ >>> 1).toNat) = true then c₂ >>> 1 else c₁ >>> 1) = c₁ >>> 1 := by
        rw [decide_eq_false hlt]; rfl
      rw [hid, BitVec.toNat_ofNat]
      simp only [minChars, Nat.min_eq_left (by omega : (c₁ >>> 1).toNat ≤ (c₂ >>> 1).toNat)]
      exact (Nat.mod_eq_of_lt (by omega : (c₁ >>> 1).toNat < 2 ^ 32)).symm
  simp only [h_min_val]
  cont; sstep
  intro _
  simp only [BitVec.and_self, ofNat32_eq_zero (show minChars < 2 ^ 32 by omega)]
  cont; sstep
  by_cases hmin0 : minChars = 0
  · simp only [hmin0, beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 100) rfl]
    cont
    refine done_at H s _ ?_ ?_
    · refine ⟨rfl, fun r hr' => ?_, Or.inl rfl⟩
      have hr'' := hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
      simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
        ↓reduceIte]
    · simp only [get64_set64, h_out_n, ↓reduceIte]
      rw [show c₁.ushiftRight 1 = c₁ >>> 1 from rfl, show c₂.ushiftRight 1 = c₂ >>> 1 from rfl,
        sub_len_eq_compareToSpec_prefix c₁ c₂ d₁ d₂]
      change BitVec.zeroExtend 64 (BitVec.ofInt 32 (↑(strChars c₁ d₁).length - ↑(strChars c₂ d₂).length)) =
        BitVec.zeroExtend 64 (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂))
      rw [compareToSpec_prefix (fun i hi1 hi2 => by rw [strChars_length] at hi1 hi2; omega)]
  · simp only [beq_eq_false_iff_ne.mpr hmin0, Bool.false_eq_true, ↓reduceIte]
    have hmin_pos : 0 < minChars := Nat.pos_of_ne_zero hmin0
    have hmin_lt : minChars < 2 ^ 31 := by omega
    cont; sstep
    intro _
    rs_reg
    cont; sstep
    intro _
    simp only [xor_lsb0_iff]
    cont; sstep
    by_cases hmix : c₁.getLsbD 0 ≠ c₂.getLsbD 0
    · have hceq_f : (c₂.getLsbD 0 == c₁.getLsbD 0) = false := by
        cases h1 : c₁.getLsbD 0 <;> cases h2 : c₂.getLsbD 0 <;> simp_all
      simp only [hceq_f, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 77) rfl]
      cont
      have hM := mixedEncStrings_of (str := str) (arg := arg) hmem hl₁ hl₂ hmix hmin_pos
      refine mixed_init_at h_distinct hlab H s _ _ _ _ minChars hM _ ?_ ?_ ?_ ?_ ?_ ?_
      · refine ⟨rfl, fun r hr' => ?_, Or.inl rfl⟩
        have hr'' := hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
        simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
          ↓reduceIte]
      · simp [get64_set64, h_str_n, h_str_out, h_str_off, h_str_c2, h_str_c1]
      · simp [get64_set64, h_arg_n, h_arg_out, h_arg_off, h_arg_c2, h_arg_c1]
      · simp [get64_set64, h_out_n, h_out_c2]
      · rs_reg
      · simp [get64_set64, Ne.symm h_c2_n]
    · have hcomp : c₁.getLsbD 0 = c₂.getLsbD 0 := Classical.not_not.mp hmix
      have hceq_t : (c₂.getLsbD 0 == c₁.getLsbD 0) = true := by
        rw [hcomp]; exact beq_self_eq_true _
      simp only [hceq_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hS := sameEncStrings_of (str := str) (arg := arg) hAB hmem hl₁ hl₂ hb₁ hcomp hmin_pos
      let L := min (strByteLen c₁) (strByteLen c₂)
      let T := L + padBytes L
      have hL_val : (if c₁.getLsbD 0 then BitVec.ofNat 32 (2 * minChars) else BitVec.ofNat 32 minChars) =
          BitVec.ofNat 32 L := by
        by_cases hc : c₁.getLsbD 0 = true
        · have hc2 : c₂.getLsbD 0 = true := by rw [← hcomp]; exact hc
          simp [hc, L, strByteLen_uncompressed hc, strByteLen_uncompressed hc2, minChars]
        · have hcf : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
          have hc2 : c₂.getLsbD 0 = false := by rw [← hcomp]; exact hcf
          rw [hcf]; simp [L, strByteLen_compressed hcf, strByteLen_compressed hc2, minChars]
      cont; sstep
      intro _
      rs_reg; simp only [c1_and1_eq]
      cont; sstep
      rs_reg
      have hlea : (((BitVec.ofNat 32 minChars).setWidth 64 + (BitVec.ofNat 32 minChars).setWidth 64 + 0#64).setWidth 32) =
          BitVec.ofNat 32 (2 * minChars) := by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt (show minChars < 2 ^ 32 by omega),
          Nat.mod_eq_of_lt (show 2 * minChars < 2 ^ 32 by omega)]
        omega
      simp only [hlea]
      cont; sstep
      rs_reg
      have hcond1 : ((if c₁.getLsbD 0 then 1#32 else 0#32) == 0#32) = !c₁.getLsbD 0 := by
        cases c₁.getLsbD 0 <;> decide
      simp only [hcond1, Bool.not_not, hL_val]
      cont; sstep
      intro _
      simp only [BitVec.xor_self]
      cont; sstep
      rs_reg
      rw [show (32#32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        cf_ofNat32 (show L < 2 ^ 32 from hS.hL_lt) (show 32 < 2 ^ 32 by decide)]
      cont; sstep
      by_cases hlt32 : L < 32
      · simp only [hlt32, decide_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 62) rfl]
        cont
        refine qword_loop_ind h_distinct hlab H s _ _ L T hS L 0 _ ?_ ?_ ?_ ?_ ?_ (Nat.zero_add L)
          hS.hL_pos hlt32 rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
        · refine ⟨rfl, fun r hr' => ?_, Or.inl rfl⟩
          have hr'' := hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
          simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
            ↓reduceIte]
        · rs_reg; rfl
        · rs_reg
        · rs_reg; decide
        · rs_reg
      · simp only [hlt32, decide_false, Bool.false_eq_true, ↓reduceIte]
        cont
        refine avx2_loop_ind h_distinct h_ymm hlab H s _ _ L T hS L 0 _ ?_ ?_ ?_ ?_ ?_ (Nat.zero_add L)
          (by omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
        · refine ⟨rfl, fun r hr' => ?_, Or.inl rfl⟩
          have hr'' := hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
          simp only [get64_set64, hr''.1, hr''.2.1, hr''.2.2.1, hr''.2.2.2.1, hr''.2.2.2.2.1,
            ↓reduceIte]
        · rs_reg; rfl
        · rs_reg
        · rs_reg; decide
        · rs_reg

/--
Correctness of the checked AVX2 `String.compareTo` lowering `stringCompareToProg`:
returns through `slow` with unchanged state when `arg = 0`, otherwise falls through
to `stringCompareToNoCheckProg`.
-/
public theorem stringCompareTo_correct [Host]
    (slow : Label) (str arg out c1 c2 n off : Reg64) (ymm : AvxReg .W256)
    (h_distinct : [str, arg, out, c1, c2, n, off, .r11].Nodup)
    (h_ymm : ymm.base ∈ [RegMm.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10,
      .mm11, .mm12, .mm13, .mm14, .mm15])
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧
        (s.regs.get64 str).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32 ∧
        (s.regs.get64 arg = 0#64 ∨
          ((s.regs.get64 arg).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32 ∧
           d₁.length = strByteLen c₁ ∧
           d₂.length = strByteLen c₂ ∧
           ∃ R, StringsInMem (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ R s.dmem)) ⦄
      stringCompareToProg slow str arg out c1 c2 n off ymm
    ⦃ fun _ => StringCompareToPost out [c1, c2, n, off, .r11] [ymm]
        (strChars c₁ d₁) (strChars c₂ d₂) s₀;
      StringCompareToSlow slow arg s₀ ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hb₁, harg⟩
  unfold stringCompareToProg
  change Program.wp
    (Directive.instr (.regular .W64 .W32 (.test (.reg (.low arg .W32)) (.reg (.low arg .W32)))) ::
     Directive.instr (.regular .W64 .W64 (.jcc .z slow)) ::
     stringCompareToNoCheckProg str arg out c1 c2 n off ymm) _ _ s
  refine Program.wp_cons ?_
  intro k0 hk0
  refine Host.eventually_of_interp hk0 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Width.bits, Effects.All, Proof.get_low32, BitVec.and_self]
  intro af
  refine Or.inl ⟨rfl, ?_⟩
  refine Program.wp_cons ?_
  intro k1 hk1
  refine Host.eventually_of_interp hk1 ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, CondCode.interp,
    StatusFlags.from_result, Effects.All, BitVec.zero_eq]
  by_cases h0 : s.regs.get64 arg = 0#64
  · have hlow0 : (s.regs.get64 arg).setWidth 32 = 0#32 := by simp [h0]
    simp only [hlow0, beq_self_eq_true, ↓reduceIte]
    exact Or.inr ⟨rfl, h0, rfl, rfl, rfl⟩
  · rcases harg with h_null | ⟨hb₂, hl₁, hl₂, ⟨R, hmem⟩⟩
    · exact False.elim (h0 h_null)
    · have hlt32 : (s.regs.get64 arg).toNat < 2 ^ 32 := by omega
      have hne0 : (s.regs.get64 arg).setWidth 32 ≠ 0#32 := fun heq => h0 (by
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat heq
        simpa [Nat.mod_eq_of_lt hlt32] using this)
      simp only [beq_eq_false_iff_ne.mpr hne0]
      refine Or.inl ⟨rfl, ?_⟩
      let s1 : MachineData := { s with
        status := StatusFlags.from_result ((s.regs.get64 arg).setWidth 32)
          { cf := false, af := af, of := false, df := s.status.df } }
      have hwp_nocheck := (Program.triple_iff.mp
        (stringCompareToNoCheck_correct str arg out c1 c2 n off ymm
          h_distinct h_ymm c₁ c₂ d₁ d₂ hlab s1))
        s1 ⟨rfl, hb₁, hb₂, hl₁, hl₂, ⟨R, hmem⟩⟩
      have hwp_post : Program.wp (stringCompareToNoCheckProg str arg out c1 c2 n off ymm)
          (StringCompareToPost out [c1, c2, n, off, .r11] [ymm] (strChars c₁ d₁) (strChars c₂ d₂) s)
          (StringCompareToSlow slow arg s) s1 :=
        Program.wp_mono
          (fun t ht => ⟨ht.1, fun r hr => ht.2.1 r hr, ht.2.2.1, ht.2.2.2⟩)
          (fun _ _ h => False.elim h) hwp_nocheck
      simpa only [s1, StatusFlags.from_result, BitVec.zero_eq,
        beq_eq_false_iff_ne.mpr hne0] using hwp_post

end Kraken.X64.Art
