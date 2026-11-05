module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
import Kraken.X64.Parser
public import Kraken.X64.WP.Rep
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

/--
Parameterized assembly template for the baseline (non-AVX2) `String.equals` lowering in ART,
using `repe cmpsq`.
Uses input registers `str` and `arg`, and pinned registers:
- `%rcx` (count / temporary)
- `%rdi` (pointer into `arg` / temporary)
- `%rsi` (pointer into `str`, and final boolean output)
-/
def stringEqualsRepProg (str arg : Reg64) : _root_.Program := parse("
    # 1. Reference equality check: if str == arg return true
    cmpl %❰.low arg .W32❱, %❰.low str .W32❱
    je return_true

    # 2. Load count_ fields: if count(str) != count(arg) return false
    movl 8(%❰str❱), %ecx
    cmpl 8(%❰arg❱), %ecx
    jne return_false

    # 3. If count == 0 return true
    jrcxz return_true

    # 4. Convert count to byte length and determine compression
    shrl $1, %ecx
    # CF = bit 0 of the original count (1 = uncompressed)
    jb uncompressed
    # compressed: chars -> words
    addl $1, %ecx
    shrl $1, %ecx
  uncompressed:
    lea 16(%❰str❱), %esi
    lea 16(%❰arg❱), %edi
    # words -> qwords
    addl $3, %ecx
    shrl $2, %ecx
    repe cmpsq
    jne return_false

  return_true:
    movl $1, %esi
    jmp end

  return_false:
    xorl %esi, %esi

  end:
")

theorem lea32_eq {p : BitVec 64} (hp : p.toNat + 16 < 2 ^ 32) :
    ((p + 16#64).setWidth 32).zeroExtend 64 = p + 16#64 := by
  apply BitVec.eq_of_toNat_eq
  change (((p + 16#64).setWidth 32).setWidth 64).toNat = (p + 16#64).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : (16 : Nat) % 2 ^ 64 = 16 := by decide
  rw [h1]
  have h2 : p.toNat + 16 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h2]
  have h3 : p.toNat + 16 < 2 ^ 32 := hp
  rw [Nat.mod_eq_of_lt h3]
  have h4 : p.toNat + 16 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h4]

theorem uncompressed_qwords_eq (n : Nat) :
    8 * ((n + 3) / 4) = 2 * n + padBytes (2 * n) := by
  unfold padBytes
  omega

theorem compressed_qwords_eq (n : Nat) (hn : 0 < n) :
    8 * (((n + 1) / 2 + 3) / 4) = n + padBytes n := by
  unfold padBytes
  omega

theorem ofNat64_toNat32 (v : BitVec 32) :
    BitVec.ofNat 64 v.toNat = v.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

theorem uncompressed_toNat_div4 (c : BitVec 32) :
    (((c >>> 1) + 3#32) >>> 2).toNat = ((c >>> 1).toNat + 3) / 4 := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hlt : (c >>> 1).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := c.isLt; omega
  have h3 : (3 : Nat) % 2 ^ 32 = 3 := by decide
  rw [h3, Nat.mod_eq_of_lt (by omega)]

theorem compressed_toNat_div (c : BitVec 32) :
    ((((c >>> 1) + 1#32) >>> 1 + 3#32) >>> 2).toNat = (((c >>> 1).toNat + 1) / 2 + 3) / 4 := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hlt : (c >>> 1).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := c.isLt; omega
  have h1 : (1 : Nat) % 2 ^ 32 = 1 := by decide
  have h3 : (3 : Nat) % 2 ^ 32 = 3 := by decide
  rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hmid : ((c >>> 1).toNat + 1) / 2 < 2 ^ 31 := by omega
  rw [h3, Nat.mod_eq_of_lt (by omega)]

theorem ofNat64_succ_sub_one (m : Nat) : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem ofNat64_eq_zero {m : Nat} (hm : m < 2 ^ 64) : (BitVec.ofNat 64 m == 0#64) = (m == 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 m ≠ 0#64 := fun h' => h (by
      have := congrArg BitVec.toNat h'; simp at this; omega)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

open Proof

theorem test_bv (c : BitVec 32) :
    BitVec.setWidth 64
      (BitVec.ushiftRight (3#32 + BitVec.setWidth 32 (BitVec.setWidth 64 (c.ushiftRight 1))) 2) =
    BitVec.zeroExtend 64 (((c >>> 1) + 3#32) >>> 2) := by
  bv_decide

theorem test_bv_comp (c : BitVec 32) :
    BitVec.setWidth 64
      (BitVec.ushiftRight
        (3#32 + BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ushiftRight (1#32 + c.ushiftRight 1) 1))) 2) =
    BitVec.zeroExtend 64 (((((c >>> 1) + 1#32) >>> 1 + 3#32) >>> 2)) := by
  bv_decide

theorem lea32_eq' {p : BitVec 64} (hp : p.toNat + 16 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.zeroExtend 32 (p + 16#64)) = p + 16#64 := by
  have := lea32_eq hp
  bv_decide

theorem cnt2 : (BitVec.extractLsb' 0 8 2#64).toNat &&& 31 = 2 := by decide

theorem rcx_zero_c1 :
    (BitVec.setWidth 64
      (BitVec.ushiftRight (3#32 + BitVec.setWidth 32 (BitVec.setWidth 64 ((1#32).ushiftRight 1))) 2) == 0#64) = true := by
  decide

theorem zf_c1 :
    (BitVec.ushiftRight (3#32 + BitVec.setWidth 32 (BitVec.setWidth 64 ((1#32).ushiftRight 1))) 2 == 0#32) = true := by
  decide

section
variable [Host] {str arg : Reg64} {ymm : AvxReg .W256} {c₁ c₂ : BitVec 32}
  {d₁ d₂ : List UInt8}

set_option hygiene false in
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
    zmms_set_set, Bool.false_eq_true, Bool.and_false, Bool.not_false, Bool.not_true, BitVec.zero_eq,
    BitVec.setWidth_eq, sw32_ofNat, cnt1, cnt2, cnt3, rcx_zero_c1, zf_c1, Bool.false_and, strStep_64_df_false,
    strStep_64_qword_false, ↓reduceIte]))

macro "cont" : tactic => `(tactic| refine Program.loopCont_of_le (by simp [stringEqualsRepProg]) ?_)

omit [Host] in
theorem post_of (str arg : Reg64) (ymm : AvxReg .W256) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    {s t : MachineData}
    (v : BitVec 64)
    (hv : v = if stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ then 1#64 else 0#64)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) (st : StatusFlags) :
    StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s
      { regs := t.regs.set64 .rsi v, zmms := t.zmms, status := st, dmem := t.dmem } := by
  unfold StringEqualsPost
  refine ⟨t.regs.get64 .rcx, t.regs.get64 .rdi, t.zmms, st, Or.inl hz, ?_⟩
  simp only [MachineData.mk.injEq, hm, and_true]
  apply reg64s_ext; intro r
  simp only [get64_set64]
  by_cases h1 : r = .rsi
  · simp [h1, hv]
  by_cases h2 : r = .rdi
  · subst h2; simp [h1]
  by_cases h3 : r = .rcx
  · subst h3; simp [h1, h2]
  simp only [h1, h2, h3, ↓reduceIte]
  exact hr r (by simp [h1, h2, h3])

theorem ret_true (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsRepProg str arg)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = true)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    Program.Loop (stringEqualsRepProg str arg) H
      (StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 17)⟩ := by
  sstep; cont; sstep; cont; sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 22) rfl]
  cont; sstep; cont
  exact Program.loop_done (post_of str arg ymm c₁ c₂ d₁ d₂ _ (by simp [hb]) hm hr hz _)

theorem ret_false (_hlab : LabelsPlaced)
    (H : Embedding (stringEqualsRepProg str arg)) (s t : MachineData)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = false)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    Program.Loop (stringEqualsRepProg str arg) H
      (StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 20)⟩ := by
  sstep; cont; sstep; intro _; cont; sstep; cont
  exact Program.loop_done (post_of str arg ymm c₁ c₂ d₁ d₂ _ (by simp [hb]) hm hr hz _)

omit [Host] in
theorem regs_cmps_frame (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) (r : Reg64)
    (hr : r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi]) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 r = regs.get64 r := by
  have h1 : r ≠ .rcx := by intro h; subst h; simp at hr
  have h2 : r ≠ .rdi := by intro h; subst h; simp at hr
  have h3 : r ≠ .rsi := by intro h; subst h; simp at hr
  rw [get64_set64, get64_set64, get64_set64]
  simp [h1, h2, h3]

omit [Host] in
theorem regs_cmps_frame' (regs : Reg64s) (v_rsi v_rdi : BitVec 64) (r : Reg64)
    (hr : r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi]) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 r = regs.get64 r := by
  have h2 : r ≠ .rdi := by intro h; subst h; simp at hr
  have h3 : r ≠ .rsi := by intro h; subst h; simp at hr
  rw [get64_set64, get64_set64]
  simp [h2, h3]

omit [Host] in
theorem regs_cmps_rcx (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rcx = regs.get64 .rcx := by
  rw [get64_set64, get64_set64]; rfl

omit [Host] in
theorem regs_cmps_rsi (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rsi = v_rsi := by
  rw [get64_set64, get64_set64]; rfl

omit [Host] in
theorem regs_cmps_rdi (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rdi = v_rdi := by
  rw [get64_set64]; rfl

omit [Host] in
theorem regs_cmps_set64_rcx (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rcx = v_rcx := by
  rw [get64_set64]; rfl

omit [Host] in
theorem regs_cmps_set64_rsi (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rsi = v_rsi := by
  rw [get64_set64, get64_set64, get64_set64]; rfl

omit [Host] in
theorem regs_cmps_set64_rdi (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rdi = v_rdi := by
  rw [get64_set64, get64_set64]; rfl

omit [Host] in
theorem regs_cmps_step_rsi (regs : Reg64s) (k : Nat) (A : BitVec 64) (v_rcx : BitVec 64)
    (hrsi : regs.get64 .rsi = A + 16#64 + .ofNat 64 k) :
    (((regs.set (Reg.low .rsi .W64) (regs.get (Reg.low .rsi .W64) + 8#64)).set
          (Reg.low .rdi .W64)
          ((regs.set (Reg.low .rsi .W64) (regs.get (Reg.low .rsi .W64) + 8#64)).get
              (Reg.low .rdi .W64) +
            8#64)).set64 .rcx v_rcx).get64 .rsi = A + 16#64 + .ofNat 64 (k + 8) := by
  simp only [set_low64, get_low64, regs_cmps_set64_rsi]
  rw [hrsi, BitVec.ofNat_add]
  ac_rfl

omit [Host] in
theorem regs_cmps_step_rdi (regs : Reg64s) (k : Nat) (B : BitVec 64) (v_rcx : BitVec 64)
    (hrdi : regs.get64 .rdi = B + 16#64 + .ofNat 64 k) :
    (((regs.set (Reg.low .rsi .W64) (regs.get (Reg.low .rsi .W64) + 8#64)).set
          (Reg.low .rdi .W64)
          ((regs.set (Reg.low .rsi .W64) (regs.get (Reg.low .rsi .W64) + 8#64)).get
              (Reg.low .rdi .W64) +
            8#64)).set64 .rcx v_rcx).get64 .rdi = B + 16#64 + .ofNat 64 (k + 8) := by
  simp only [set_low64, get_low64, get64_set64]
  have : Reg64.rdi ≠ Reg64.rsi := by decide
  simp only [this, ↓reduceIte]
  rw [hrdi, BitVec.ofNat_add]
  ac_rfl

omit [Host] in
theorem ofNat64_add_8 (k : Nat) : BitVec.ofNat 64 k + 8#64 = BitVec.ofNat 64 (k + 8) := by
  rw [BitVec.ofNat_add]

theorem cmps_zero (str arg : Reg64) (ymm : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsRepProg str arg)) (s t : MachineData)
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (hb : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = true)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (hzf : t.status.zf = true)
    (hrcx0 : t.regs.get64 .rcx = 0#64) :
    Program.Loop (stringEqualsRepProg str arg) H
      (StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
      ⟨t, Host.addrOf (H.start + 15)⟩ := by
  refine Program.loop_repe_cmpsq_zero (i := 15) rfl hrcx0 ?_
  refine Program.loopCont_of_le (j := 16) (by simp [stringEqualsRepProg]) ?_
  sstep
  simp only [hzf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  change Program.LoopCont _ _ _ _ ⟨t, Host.addrOf (H.start + 17)⟩
  refine Program.loopCont_of_le (j := 17) (by simp [stringEqualsRepProg]) ?_
  exact ret_true hlab H s t hb hm hr hz

theorem cmps_loop (str arg : Reg64) (ymm : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringEqualsRepProg str arg))
    (s : MachineData) (A B : BitVec 64) (T : Nat)
    (hS : Strings s str arg c₁ c₂ d₁ d₂ A B T)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hm_mem : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms)
      (hdf : t.status.df = false)
      (hrcx : t.regs.get64 .rcx = .ofNat 64 (m + 1))
      (hrsi : t.regs.get64 .rsi = A + 16#64 + .ofNat 64 k)
      (hrdi : t.regs.get64 .rdi = B + 16#64 + .ofNat 64 k)
      (hk : k + 8 * (m + 1) = T)
      (hpre : ∀ i < k, byteAt s.dmem A i = byteAt s.dmem B i),
      Program.Loop (stringEqualsRepProg str arg) H
        (StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s) (fun _ _ => False)
        ⟨t, Host.addrOf (H.start + 15)⟩ := by
  induction m with
  | zero =>
    intro k t hm_mem hr hz hdf hrcx hrsi hrdi hk hpre
    obtain ⟨hA, hB, hT, hsA, hsB, hTrue, hFalse⟩ := hS
    have haddrA : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have haddrB : B + 16#64 + .ofNat 64 k = B + .ofNat 64 k + 16#64 := by ac_rfl
    have hloadA : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 8 =
        some (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem A (k + j))) := by
      rw [haddrA, hm_mem, load_chunk _ _ k 8 T hsA (by omega)]
    have hloadB : t.dmem.loadInt (B + 16#64 + .ofNat 64 k) 8 =
        some (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem B (k + j))) := by
      rw [haddrB, hm_mem, load_chunk _ _ k 8 T hsB (by omega)]
    have hne0 : (BitVec.ofNat 64 1 == 0#64) = false := rfl
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte, Effects.All_require_read_access]
    rw [hrsi, hloadA]
    dsimp only []
    rw [hrdi, hloadB]
    dsimp only []
    simp only [Effects.All_require_read_access, MachineData.setReg, strStep_64_qword_false]
    if heq : ∀ j < 8, byteAt s.dmem A (k + j) = byteAt s.dmem B (k + j) then
      have hchunk : BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) =
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) := by
        rw [chunk_eq_iff _ _ _ _ 8 64 rfl]; exact heq
      have hrcx_eval : (((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).set
            (Reg.low Reg64.rdi Width.W64)
            ((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).get
                (Reg.low Reg64.rdi Width.W64) +
              8#64)).get64 Reg64.rcx - 1#64) = 0#64 := by
        simp only [set_low64, regs_cmps_rcx]
        rw [hrcx]; rfl
      rw [sub_beq_zero, hchunk, beq_self_eq_true, hrcx_eval]
      simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 16)⟩
      refine Program.loopCont_of_le (j := 16) (by simp [stringEqualsRepProg]) ?_
      sstep
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 17)⟩
      refine Program.loopCont_of_le (j := 17) (by simp [stringEqualsRepProg]) ?_
      have hT_eq : k + 8 = T := by omega
      have hall : ∀ i < T, byteAt s.dmem A i = byteAt s.dmem B i := by
        intro i hi; rw [← hT_eq] at hi; exact prefix_ext hpre heq i hi
      have hstr_eq : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = true := by
        rw [hA, hB]; exact hTrue hall
      exact ret_true hlab H s _ hstr_eq hm_mem
        (fun r hr_out => by simp only [set_low64, regs_cmps_frame _ _ _ _ _ hr_out]; exact hr _ hr_out) hz
    else
      have hchunk_ne : BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) ≠
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) := by
        intro h; rw [chunk_eq_iff _ _ _ _ 8 64 rfl] at h; exact heq h
      have hzf_false : (BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) -
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) == 0#64) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne.mpr hchunk_ne]
      rw [hzf_false]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 16)⟩
      refine Program.loopCont_of_le (j := 16) (by simp [stringEqualsRepProg]) ?_
      sstep
      rw [addrOf_label hlab (H := H) (i := 20) rfl]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 20)⟩
      refine Program.loopCont_of_le (j := 20) (by simp [stringEqualsRepProg]) ?_
      have hdiff : ∃ j, j < 8 ∧ byteAt s.dmem A (k + j) ≠ byteAt s.dmem B (k + j) :=
        Classical.byContradiction fun hc =>
          heq fun j hj => Classical.byContradiction fun hne => hc ⟨j, hj, hne⟩
      obtain ⟨j, hj8, hjdiff⟩ := hdiff
      have hstr_ne : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = false := by
        rw [hA, hB]; exact hFalse ⟨k + j, by omega, hjdiff⟩
      exact ret_false hlab H s _ hstr_ne hm_mem
        (fun r hr_out => by simp only [set_low64, regs_cmps_frame _ _ _ _ _ hr_out]; exact hr _ hr_out) hz
  | succ m' ih =>
    intro k t hm_mem hr hz hdf hrcx hrsi hrdi hk hpre
    obtain ⟨hA, hB, hT, hsA, hsB, hTrue, hFalse⟩ := hS
    have haddrA : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have haddrB : B + 16#64 + .ofNat 64 k = B + .ofNat 64 k + 16#64 := by ac_rfl
    have hloadA : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 8 =
        some (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem A (k + j))) := by
      rw [haddrA, hm_mem, load_chunk _ _ k 8 T hsA (by omega)]
    have hloadB : t.dmem.loadInt (B + 16#64 + .ofNat 64 k) 8 =
        some (Int.ofBytes ((List.range 8).map fun j => byteAt s.dmem B (k + j))) := by
      rw [haddrB, hm_mem, load_chunk _ _ k 8 T hsB (by omega)]
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == 0#64) = false := by
      simp [ofNat64_eq_zero (show m' + 1 + 1 < 2 ^ 64 by omega)]
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte, Effects.All_require_read_access]
    rw [hrsi, hloadA]
    dsimp only []
    rw [hrdi, hloadB]
    dsimp only []
    simp only [Effects.All_require_read_access, MachineData.setReg, strStep_64_qword_false]
    if heq : ∀ j < 8, byteAt s.dmem A (k + j) = byteAt s.dmem B (k + j) then
      have hchunk : BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) =
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) := by
        rw [chunk_eq_iff _ _ _ _ 8 64 rfl]; exact heq
      have hrcx_eval : (((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).set
            (Reg.low Reg64.rdi Width.W64)
            ((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).get
                (Reg.low Reg64.rdi Width.W64) +
              8#64)).get64 Reg64.rcx - 1#64) = .ofNat 64 (m' + 1) := by
        simp only [set_low64, regs_cmps_rcx]
        rw [hrcx, ofNat64_succ_sub_one]
      have hne_zero : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
        rw [bne_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [sub_beq_zero, hchunk, beq_self_eq_true, hrcx_eval, hne_zero]
      simp only [Bool.true_and, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 15)⟩
      refine Program.loopCont_of_le (j := 15) (by simp [stringEqualsRepProg]) ?_
      have hrsi' : (((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).set
            (Reg.low Reg64.rdi Width.W64)
            ((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).get
                (Reg.low Reg64.rdi Width.W64) +
              8#64)).set64 Reg64.rcx (.ofNat 64 (m' + 1))).get64 Reg64.rsi =
          A + 16#64 + BitVec.ofNat 64 (k + 8) :=
        regs_cmps_step_rsi _ _ _ _ hrsi
      have hrdi' : (((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).set
            (Reg.low Reg64.rdi Width.W64)
            ((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).get
                (Reg.low Reg64.rdi Width.W64) +
              8#64)).set64 Reg64.rcx (.ofNat 64 (m' + 1))).get64 Reg64.rdi =
          B + 16#64 + BitVec.ofNat 64 (k + 8) :=
        regs_cmps_step_rdi _ _ _ _ hrdi
      have hrcx' : (((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).set
            (Reg.low Reg64.rdi Width.W64)
            ((t.regs.set (Reg.low Reg64.rsi Width.W64) (t.regs.get (Reg.low Reg64.rsi Width.W64) + 8#64)).get
                (Reg.low Reg64.rdi Width.W64) +
              8#64)).set64 Reg64.rcx (.ofNat 64 (m' + 1))).get64 Reg64.rcx =
          .ofNat 64 (m' + 1) := by
        simp only [get64_set64, ↓reduceIte]
      exact ih (k + 8) _ hm_mem
        (fun r hr_out => by
          have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          have h3 : r ≠ .rsi := by intro h; subst h; simp at hr_out
          simp only [get64_set64, set_low64, get_low64, h1, h2, h3, ↓reduceIte]
          exact hr r hr_out) hz rfl
        hrcx' hrsi' hrdi' (by omega) (prefix_ext hpre heq)
    else
      have hchunk_ne : BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) ≠
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) := by
        intro h; rw [chunk_eq_iff _ _ _ _ 8 64 rfl] at h; exact heq h
      have hzf_false : (BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 8))) -
          BitVec.ofInt 64 (Int.ofBytes (List.map (fun j => byteAt s.dmem B (k + j)) (List.range 8))) == 0#64) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne.mpr hchunk_ne]
      rw [hzf_false]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 16)⟩
      refine Program.loopCont_of_le (j := 16) (by simp [stringEqualsRepProg]) ?_
      sstep
      rw [addrOf_label hlab (H := H) (i := 20) rfl]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 20)⟩
      refine Program.loopCont_of_le (j := 20) (by simp [stringEqualsRepProg]) ?_
      have hdiff : ∃ j, j < 8 ∧ byteAt s.dmem A (k + j) ≠ byteAt s.dmem B (k + j) :=
        Classical.byContradiction fun hc =>
          heq fun j hj => Classical.byContradiction fun hne => hc ⟨j, hj, hne⟩
      obtain ⟨j, hj8, hjdiff⟩ := hdiff
      have hstr_ne : stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ = false := by
        rw [hA, hB]; exact hFalse ⟨k + j, by omega, hjdiff⟩
      exact ret_false hlab H s _ hstr_ne hm_mem
        (fun r hr_out => by simp only [regs_cmps_frame _ _ _ _ _ hr_out]; exact hr _ hr_out) hz

open Std.WP in
/--
Correctness theorem for the baseline (repe cmpsq) `String.equals` lowering in ART,
proved against the exact same specification `StringEqualsPost`.
-/
theorem stringEqualsRep_correct [Host]
    (str arg : Reg64) (ymm : AvxReg .W256)
    (h_distinct : [str, arg, .rcx, .rdi, .rsi].Nodup)
    (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧
        s.status.df = false ∧
        (s.regs.get64 str).toNat + 16 < 2 ^ 32 ∧
        (s.regs.get64 arg).toNat + 16 < 2 ^ 32 ∧
        d₁.length = strByteLen c₁ ∧
        d₂.length = strByteLen c₂ ∧
        ∃ R, StringsInMem (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ d₁ d₂ R s.dmem ⦄
      stringEqualsRepProg str arg
    ⦃ fun _ => StringEqualsPost str arg .rcx .rdi .rsi ymm c₁ c₂ d₁ d₂ s₀; fun _ _ => False ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hdf, hA32, hB32, hl₁, hl₂, ⟨R, hmem⟩⟩
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := hd
  apply Program.wp_of_loop
  intro H
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  sstep; cont; sstep
  have hA32' : (s.regs.get64 str).toNat < 2 ^ 32 := by omega
  have hB32' : (s.regs.get64 arg).toNat < 2 ^ 32 := by omega
  simp only [sub_beq_zero, low32_beq hA32' hB32']
  by_cases hAB : s.regs.get64 str = s.regs.get64 arg
  · simp only [hAB, beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 17) rfl]
    cont
    exact ret_true hlab H s _ (by simp [stringEquals, hAB]) rfl (fun _ _ => rfl) rfl
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
      addrOf_label hlab (H := H) (i := 20) rfl]
    cont
    refine ret_false hlab H s _ (by simp [stringEquals, hAB, hc]) rfl ?hr rfl
    case hr =>
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      obtain ⟨hrcx_ne, hrdi_ne, hrsi_ne⟩ := hr_out
      simp only [get64_set64, hrcx_ne, ↓reduceIte]
  simp only [Classical.not_not] at hc
  subst hc
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hS := strings_of hAB hmem hl₁ hl₂
  cont; sstep
  by_cases hc0 : c₁ = 0
  · simp only [hc0, addrOf_label hlab (H := H) (i := 17) rfl]
    cont
    have e₁ : d₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₁, hc0]; rfl)
    have e₂ : d₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₂, hc0]; rfl)
    refine ret_true hlab H s _ (by simp [stringEquals, e₁, e₂]) rfl ?hr rfl
    case hr =>
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      obtain ⟨hrcx_ne, hrdi_ne, hrsi_ne⟩ := hr_out
      simp only [get64_set64, hrcx_ne, ↓reduceIte]
  have hc0_64 : (c₁.zeroExtend 64 == 0#64) = false := by
    revert hc0; bv_decide
  simp only [hc0_64, Bool.false_eq_true, ↓reduceIte]
  by_cases hbit : c₁.getLsbD 0 = true
  · -- Instruction 6: shr ecx, 1
    cont; sstep
    intro _ -- af
    -- Instruction 7: jc uncompressed
    cont; sstep
    simp only [hbit, ↓reduceIte, addrOf_label hlab (H := H) (i := 10) rfl]
    -- Directive 10: .label "uncompressed"
    cont; sstep
    -- Instruction 11: lea esi, [str+16]
    cont; sstep
    -- Instruction 12: lea edi, [arg+16]
    cont; sstep
    -- Instruction 13: add ecx, 3
    cont; sstep
    -- Instruction 14: shr ecx, 2
    cont; sstep
    intro _ -- af
    intro _ -- of
    -- Instruction 15: repe cmpsq!
    by_cases hc1 : c₁ = 1
    · subst hc1
      cont
      refine Program.loop_repe_cmpsq_zero rfl ?hrcx ?_
      case hrcx =>
        simp only [get64_set64, set_low64, get_low64, h8, h9, ↓reduceIte]
        decide
      -- 16: jnz return_false
      refine Program.loopCont_of_le (j := 16) (by simp [stringEqualsRepProg]) ?_
      sstep
      simp only [h8, h9, ↓reduceIte, zf_c1, Bool.not_true, Bool.false_eq_true]
      refine Program.loopCont_of_le (j := 17) (by simp [stringEqualsRepProg]) ?_
      have e₁ : d₁ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₁]; rfl)
      have e₂ : d₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hl₂]; rfl)
      have hseq : stringEquals (s.regs.get64 str) (s.regs.get64 arg) (1#32) (1#32) d₁ d₂ = true := by
        simp [stringEquals, e₁, e₂]
      refine ret_true (c₁ := 1#32) (c₂ := 1#32) (d₁ := d₁) (d₂ := d₂) hlab H s _ hseq rfl ?hr_c1 rfl
      case hr_c1 =>
        intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        obtain ⟨hrcx_ne, hrdi_ne, hrsi_ne⟩ := hr_out
        simp only [get64_set64, set_low64, get_low64, hrcx_ne, hrdi_ne, hrsi_ne, ↓reduceIte]
    · -- c₁ > 1: call cmps_loop
      have hM_ne : ((c₁ >>> 1) + 3#32) >>> 2 ≠ 0#32 := by
        revert hc0 hc1 hbit; bv_decide
      have hM_pos : 0 < (((c₁ >>> 1) + 3#32) >>> 2).toNat := by
        apply Nat.pos_of_ne_zero
        intro h; apply hM_ne; apply BitVec.eq_of_toNat_eq; simp [h]
      let m := (((c₁ >>> 1) + 3#32) >>> 2).toNat - 1
      have hm1 : m + 1 = (((c₁ >>> 1) + 3#32) >>> 2).toNat := by omega
      cont
      refine cmps_loop str arg ymm hlab H s (s.regs.get64 str) (s.regs.get64 arg) _ hS m 0 _ rfl ?hr rfl hdf ?hrcx ?hrsi ?hrdi ?hk (fun _ hi => by omega)
      case hr =>
        intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        obtain ⟨hrcx_ne, hrdi_ne, hrsi_ne⟩ := hr_out
        simp only [get64_set64, set_low64, get_low64, hrcx_ne, hrdi_ne, hrsi_ne, ↓reduceIte]
      case hrcx =>
        simp only [get64_set64, set_low64, get_low64, h8, h9, ↓reduceIte]
        rw [test_bv, hm1, ofNat64_toNat32]
      case hrsi =>
        have h_rsi_rdi : Reg64.rsi ≠ Reg64.rdi := Ne.symm h10
        have h_rsi_rcx : Reg64.rsi ≠ Reg64.rcx := Ne.symm h9
        simp only [get64_set64, set_low64, get_low64, h_rsi_rcx, h_rsi_rdi, h2, ↓reduceIte]
        rw [lea32_eq' hA32]
        bv_decide
      case hrdi =>
        have h_rdi_rcx : Reg64.rdi ≠ Reg64.rcx := Ne.symm h8
        simp only [get64_set64, set_low64, get_low64, h_rdi_rcx, h5, h7, ↓reduceIte]
        rw [lea32_eq' hB32]
        bv_decide
      case hk =>
        rw [Nat.zero_add, hm1, uncompressed_toNat_div4]
        have heq := uncompressed_qwords_eq (c₁ >>> 1).toNat
        rw [strByteLen]
        simp only [hbit, ite_true]
        exact heq
  · -- Compressed: hbit = false
    simp only [Bool.not_eq_true] at hbit
    -- 6: shr ecx, 1
    cont; sstep
    intro _ -- af
    -- 7: jc uncompressed (CF is false, so it falls through to 8)
    cont; sstep
    simp only [hbit, Bool.false_eq_true, ↓reduceIte]
    -- 8: add ecx, 1
    cont; sstep
    -- 9: shr ecx, 1
    cont; sstep
    intro _ -- af
    -- 10: .label "uncompressed"
    cont; sstep
    -- 11: lea esi, [str+16]
    cont; sstep
    -- 12: lea edi, [arg+16]
    cont; sstep
    -- 13: add ecx, 3
    cont; sstep
    -- 14: shr ecx, 2
    cont; sstep
    intro _ -- af
    intro _ -- of
    -- 15: repe cmpsq!
    have hM_ne : ((((c₁ >>> 1) + 1#32) >>> 1 + 3#32) >>> 2) ≠ 0#32 := by
      revert hc0 hbit; bv_decide
    have hM_pos : 0 < ((((c₁ >>> 1) + 1#32) >>> 1 + 3#32) >>> 2).toNat := by
      apply Nat.pos_of_ne_zero
      intro h; apply hM_ne; apply BitVec.eq_of_toNat_eq; simp [h]
    let m := ((((c₁ >>> 1) + 1#32) >>> 1 + 3#32) >>> 2).toNat - 1
    have hm1 : m + 1 = ((((c₁ >>> 1) + 1#32) >>> 1 + 3#32) >>> 2).toNat := by omega
    cont
    refine cmps_loop str arg ymm hlab H s (s.regs.get64 str) (s.regs.get64 arg) _ hS m 0 _ rfl ?hr rfl hdf ?hrcx ?hrsi ?hrdi ?hk (fun _ hi => by omega)
    case hr =>
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      obtain ⟨hrcx_ne, hrdi_ne, hrsi_ne⟩ := hr_out
      simp only [get64_set64, set_low64, get_low64, hrcx_ne, hrdi_ne, hrsi_ne, ↓reduceIte]
    case hrcx =>
      simp only [get64_set64, set_low64, get_low64, h8, h9, ↓reduceIte]
      rw [test_bv_comp, hm1, ofNat64_toNat32]
    case hrsi =>
      have h_rsi_rdi : Reg64.rsi ≠ Reg64.rdi := Ne.symm h10
      have h_rsi_rcx : Reg64.rsi ≠ Reg64.rcx := Ne.symm h9
      simp only [get64_set64, set_low64, get_low64, h_rsi_rcx, h_rsi_rdi, h2, ↓reduceIte]
      rw [lea32_eq' hA32]
      bv_decide
    case hrdi =>
      have h_rdi_rcx : Reg64.rdi ≠ Reg64.rcx := Ne.symm h8
      simp only [get64_set64, set_low64, get_low64, h_rdi_rcx, h5, h7, ↓reduceIte]
      rw [lea32_eq' hB32]
      bv_decide
    case hk =>
      have hn_pos : 0 < (c₁ >>> 1).toNat := by
        have : (c₁ >>> 1) ≠ 0#32 := by revert hc0 hbit; bv_decide
        apply Nat.pos_of_ne_zero
        intro h; apply this; apply BitVec.eq_of_toNat_eq; simp [h]
      rw [Nat.zero_add, hm1, compressed_toNat_div]
      have heq := compressed_qwords_eq (c₁ >>> 1).toNat hn_pos
      rw [strByteLen]
      simp only [hbit, Bool.false_eq_true, ite_false]
      exact heq

end

end
