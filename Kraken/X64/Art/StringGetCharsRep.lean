module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
import Kraken.X64.Sep
import Kraken.X64.Parser
public import Kraken.X64.WP.Rep
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
public import Kraken.X64.Art.StringGetCharsSpec

open Std
open Std.WP
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/-- Instruction subtracting `srcBegin` (register or 32-bit immediate) from `%ecx`, matching ART's
    baseline `VisitStringGetCharsNoCheck` codegen (which always emits `subl`, even for `0`). -/
@[expose] def subSrcBeginInstr (srcBegin : RegOrImm) : _root_.Directive :=
  .instr (.regular .W32 .W32 (.sub (.reg (.low .rcx .W32))
    (match srcBegin with
    | .reg r => .reg (.low r .W32)
    | .imm v => .imm (.int64 (Int64.ofNat v.toNat)))))

/-- Parameterized assembly template for the baseline (non-AVX2) `String.getCharsNoCheck` lowering
    in ART: scalar `movzbl`/`movw` loop for compressed Latin-1 strings, `rep movsw` for
    uncompressed UTF-16 strings. Fixed temps are `%rcx`, `%rsi`, `%rdi`, `%r11`. -/
@[expose] def stringGetCharsRepProg
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst dstBegin : Reg64) : _root_.Program :=
  parse("
    movl %❰.low srcEnd .W32❱, %ecx
  ") ++
  [ subSrcBeginInstr srcBegin ] ++
  parse("
    testl $1, 8(%❰obj❱)
    jnz copy_uncompressed
    ❰.instr (.regular .W64 .W64 (.lea (.low .rsi .W64) (arrayAddr obj srcBegin .W8 16)))❱
    leaq 12(%❰dst❱, %❰dstBegin❱, 2), %rdi
  copy_loop:
    jrcxz done
    movzbl (%rsi), %r11d
    movw %r11w, (%rdi)
    leaq 2(%rdi), %rdi
    leaq 1(%rsi), %rsi
    subl $1, %ecx
    jmp copy_loop
  copy_uncompressed:
    ❰.instr (.regular .W64 .W64 (.lea (.low .rsi .W64) (arrayAddr obj srcBegin .W16 16)))❱
    leaq 12(%❰dst❱, %❰dstBegin❱, 2), %rdi
    rep movsw
  done:
  ")

namespace GetCharsRepProof

open Proof (addr_base_disp addr_base_disp' get_low32 get_low64 set_low32 set_low64
  get64_set64 reg64s_ext sw32_64 sw32_ofNat)
open GetCharsProof

/-- Step one directive in `Program.Loop` leaving `MachineData.load`/`MachineData.store` unexpanded
    so separation-logic rules (`load_sep`, `store_sep`) rewrite cleanly. -/
macro "sstep" : tactic => `(tactic| (
  refine Program.loop_of_interp rfl ?_
  simp only [subSrcBeginInstr, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set,
    MachineData.setReg, Effects.All, addr_base_disp, addr_base_disp',
    get_low32, get_low64, set_low32, set_low64, get64_set64, CondCode.interp,
    StatusFlags.from_result, Nat.add_assoc, Nat.reduceAdd, Nat.reduceBEq, Nat.reduceLT,
    Int64.toBitVec_ofNat, Int64.toBitVec_ofNat_grind, Int64.toBitVec_neg,
    BitVec.truncate, Width.bits, Width.bytes, BitVec.ofNat_eq_ofNat,
    BitVec.zero_eq, BitVec.setWidth_eq, sw32_64, sw32_ofNat,
    Bool.false_eq_true, Bool.and_false, Bool.not_false, Bool.not_true, Bool.false_and,
    ↓reduceIte]))

macro "cont" : tactic =>
  `(tactic| refine Program.loopCont_of_le (by simp [stringGetCharsRepProg]) ?_)

/-- Frame invariant preserved across baseline execution (`%rcx`, `%rsi`, `%rdi`, `%r11` are temps;
    `zmms` and `DF` are untouched). -/
def RepFrame (s₀ t : MachineData) : Prop :=
  (∀ r, r ∉ [Reg64.rcx, Reg64.rsi, Reg64.rdi, Reg64.r11] → t.regs.get64 r = s₀.regs.get64 r) ∧
  t.zmms = s₀.zmms ∧
  t.status.df = s₀.status.df

theorem repFrame_refl (s₀ : MachineData) : RepFrame s₀ s₀ :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem sub32_ofNat_ze64 {e b : Nat} (hb : b ≤ e) (he : e < 2 ^ 32) :
    (BitVec.ofNat 32 e - BitVec.ofNat 32 b).zeroExtend 64 = BitVec.ofNat 64 (e - b) := by
  have hb' : b < 2 ^ 32 := by omega
  have heqb : BitVec.ofNat 32 e - BitVec.ofNat 32 b = BitVec.ofNat 32 (e - b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt (by omega : e - b < 2 ^ 32)]
    omega
  rw [heqb]
  apply BitVec.eq_of_toNat_eq
  change ((BitVec.ofNat 32 (e - b)).setWidth 64).toNat = (BitVec.ofNat 64 (e - b)).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rcx_sub1_ofNat64 (m : Nat) (hm : m + 1 < 2 ^ 32) :
    ((BitVec.ofNat 64 (m + 1)).setWidth 32 - 1#32).zeroExtend 64 = BitVec.ofNat 64 m := by
  rw [show (BitVec.ofNat 64 (m + 1)).setWidth 32 = BitVec.ofNat 32 (m + 1) from by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt hm]]
  exact sub32_ofNat_ze64 (by omega) hm

theorem bv8_ze32_ze64_sw16 (x : BitVec 8) :
    ((x.zeroExtend 32).zeroExtend 64).setWidth 16 = x.zeroExtend 16 := by
  bv_decide

theorem drop0_take16_ze32_ze64 (x : BitVec 8) :
    (((x.zeroExtend 32).zeroExtend 64).drop 0).take 16 = x.zeroExtend 16 := by
  dsimp only [BitVec.drop, BitVec.take]
  bv_decide

theorem ofInt8_ofBytes_singleton (b : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
  have hof : Int.ofBytes [b] = (b.toNat : Int) := by simp [Int.ofBytes]
  rw [hof]
  apply BitVec.eq_of_toNat_eq
  have hlt : b.toNat < 2 ^ 8 := b.toBitVec.isLt
  rw [BitVec.toNat_ofInt, UInt8.toNat_toBitVec,
    Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem bufReplace_prefix_extend {target old chunk : List UInt8}
    (ht : target.length = old.length) {off len : Nat} (hle : off + len ≤ target.length)
    (hchunk : chunk = (target.drop off).take len) :
    bufReplace (target.take off ++ old.drop off) off len chunk =
      target.take (off + len) ++ old.drop (off + len) := by
  have htake_len : (target.take off).length = off := by simp [List.length_take]; omega
  unfold bufReplace
  rw [List.take_append_of_le_length (Nat.le_of_eq htake_len.symm), List.take_take, Nat.min_self,
    List.drop_append, List.drop_eq_nil_of_le (by rw [htake_len]; omega), List.nil_append,
    htake_len, show off + len - off = len by omega, List.drop_drop, hchunk]
  congr 1
  apply List.ext_getElem
  · simp [List.length_take]; omega
  · intro i hi1 hi2
    simp only [List.length_take] at hi1 hi2
    by_cases h1 : i < off
    · rw [List.getElem_append_left (by rw [htake_len]; omega), List.getElem_take,
        List.getElem_take]
    · rw [List.getElem_append_right (by rw [htake_len]; omega), List.getElem_take,
        List.getElem_drop, List.getElem_take]
      congr 1
      rw [htake_len]
      omega

theorem drop_take2_eq {xs : List UInt8} {k : Nat} (hk : k + 1 < xs.length) :
    (xs.drop k).take 2 = [xs[k], xs[k + 1]] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi1 _
    simp only [List.length_take, List.length_drop] at hi1
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [List.getElem_take, List.getElem_drop]

theorem load_string_count_at {regs : Reg64s} {zmms : RegZmms} {status : StatusFlags}
    {mem : DataMem} {A : BitVec 64} {c : BitVec 32}
    {d old : List UInt8} {dstAddr : BitVec 64} {R : DataMem → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) mem)
    (ret : Width.W32.type → MachineData → Effects) :
    MachineData.load ⟨regs, zmms, status, mem⟩ (A + 8#64) .W32 ret =
      require_access require_read_access (A + 8#64) (UInt64.ofNat Width.W32.bytes)
        (fun _ => ret (.ofInt 32 (Int.ofBytes (Int.toBytes 4 c.toInt))) ⟨regs, zmms, status, mem⟩) := by
  unfold StringAt at hmem
  rw [sep_assoc, sep_assoc] at hmem
  exact load_sep ⟨regs, zmms, status, mem⟩ (A + 8#64) .W32 ret (Int.toBytes 4 c.toInt) _ hmem
    (Int.toBytes_length 4 c.toInt)

/-- Finish at `done:` (index 18) when memory already matches `s₀.dmem.storeBytes dstAddr (getCharsBytes c d b e)`. -/
theorem done_at [Host]
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst dstBegin : Reg64)
    (H : Embedding (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin))
    (c : BitVec 32) (d : List UInt8) (s₀ t : MachineData)
    (ht : RepFrame s₀ t)
    (hmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst (.reg dstBegin) s₀.regs)
      (getCharsBytes c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat)) :
    Program.Loop (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin) H
      (StringGetCharsPost srcBegin srcEnd dst (.reg dstBegin) [.rcx, .rsi, .rdi, .r11] [] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 18)⟩ := by
  sstep; cont
  exact Program.loop_done ⟨hmem, ht.1, Or.inl ht.2.1⟩

/-- Inductive invariant proof for the compressed scalar loop at `copy_loop:` (index 6). -/
theorem compressed_loop_ind [Host]
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst dstBegin : Reg64)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (H : Embedding (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin))
    (c : BitVec 32) (d : List UInt8) (old : List UInt8) (R : Mem 64 → Prop) (s₀ : MachineData)
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆
      Eq (old.At (getCharsDstAddr dst (.reg dstBegin) s₀.regs)) ⋆ R) s₀.dmem)
    (m k : Nat) (t : MachineData)
    (ht : RepFrame s₀ t)
    (hkm : k + m = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrcx : t.regs.get64 .rcx = BitVec.ofNat 64 m)
    (hrsi : t.regs.get64 .rsi = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + k))
    (hrdi : t.regs.get64 .rdi = getCharsDstAddr dst (.reg dstBegin) s₀.regs + BitVec.ofNat 64 (2 * k))
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst (.reg dstBegin) s₀.regs)
      ((getCharsBytes c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat).take (2 * k) ++
        old.drop (2 * k))) :
    Program.Loop (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin) H
      (StringGetCharsPost srcBegin srcEnd dst (.reg dstBegin) [.rcx, .rsi, .rdi, .r11] [] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 6)⟩ := by
  induction m generalizing k t with
  | zero =>
    let b := srcBegin.toNat s₀.regs
    let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
    let target := getCharsBytes c d b e
    have htar_len : target.length = 2 * (e - b) := getCharsBytes_length c d hb_le he_le
    have hk_eq : k = e - b := by omega
    sstep; cont
    sstep
    simp only [hrcx, beq_self_eq_true, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 18) rfl]
    cont
    refine done_at obj srcBegin srcEnd dst dstBegin H c d s₀ t ht ?_
    rw [hdmem]
    congr 1
    have h1 : target.take (2 * k) = target := List.take_of_length_le (by omega)
    have h2 : old.drop (2 * k) = [] := List.drop_eq_nil_of_le (by omega)
    rw [h1, h2, List.append_nil]
  | succ m' ih =>
    let b := srcBegin.toNat s₀.regs
    let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
    let n := e - b
    let dstAddr := getCharsDstAddr dst (.reg dstBegin) s₀.regs
    let target := getCharsBytes c d b e
    let buf := target.take (2 * k) ++ old.drop (2 * k)
    have htar_len : target.length = 2 * n := getCharsBytes_length c d hb_le he_le
    have hbuf_len : buf.length = 2 * n := by
      simp only [buf, List.length_append, List.length_take, List.length_drop, htar_len, hold]
      omega
    have hn_lt : n < 2 ^ 31 := by
      have hce : (c >>> 1).toNat < 2 ^ 31 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := c.isLt; omega
      omega
    have hm_ne : (BitVec.ofNat 64 (m' + 1) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m' + 1 < 2 ^ 64 by omega)] at this
      omega
    have hbuf_lt : buf.length < 2 ^ 64 := by omega
    have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
    have hbk_lt : b + k < d.length := by rw [hl, strByteLen_compressed hc]; omega
    let srcByte : UInt8 := d[b + k]'hbk_lt
    -- Step 6: label `copy_loop`
    sstep; cont
    -- Step 7: `jrcxz done` (not taken)
    sstep
    simp only [hrcx, hm_ne, Bool.false_eq_true, ↓reduceIte]
    cont
    -- Step 8: `movzbl (%rsi), %r11d`
    sstep
    have hr_src : t.regs.get64 .rsi + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + k) := by
      rw [BitVec.add_zero]; exact hrsi
    have hsrc_slice := mem_expose_src_slice hmem0 hl (hold.trans hbuf_len.symm) hbuf_lt (off := b + k) (len := 1) (by omega)
    obtain ⟨Rs, hRs⟩ := hsrc_slice
    rw [← hr_src, ← hdmem] at hRs
    have hdrop1 : (d.drop (b + k)).take 1 = [srcByte] := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop]; omega
      · intro i hi1 _
        simp only [List.length_take, List.length_drop] at hi1
        rcases (show i = 0 by omega) with rfl
        simp [List.getElem_take, List.getElem_drop, srcByte]
    rw [hdrop1] at hRs
    rw [load_sep _ _ .W8 _ [srcByte] Rs hRs rfl]
    simp only [Effects.All_require_read_access, ofInt8_ofBytes_singleton]
    cont
    -- Step 9: `movw %r11w, (%rdi)`
    sstep
    let s_movzbl : MachineData :=
      { regs := t.regs.set64 .r11 (BitVec.setWidth 64 (srcByte.toBitVec.zeroExtend 32)),
        zmms := t.zmms, status := t.status, dmem := t.dmem }
    have hr_dst : (if Reg64.rdi = Reg64.r11 then BitVec.setWidth 64 (srcByte.toBitVec.zeroExtend 32)
        else t.regs.get64 .rdi) + 0#64 = dstAddr + BitVec.ofNat 64 (2 * k) := by
      simp [hrdi, dstAddr]
    have hdst_slice := mem_expose_dst_slice hmem0 (hold.trans hbuf_len.symm) hbuf_bound
      (off := 2 * k) (len := 2) (by omega)
    obtain ⟨Rd, hRd⟩ := hdst_slice
    have hdmem_sub : s_movzbl.dmem = s₀.dmem.storeBytes dstAddr buf := hdmem
    rw [hr_dst]
    rw [← hdmem_sub] at hRd
    let old2 := (buf.drop (2 * k)).take 2
    have hold2_len : old2.length = 2 := by
      simp only [old2, List.length_take, List.length_drop, hbuf_len]; omega
    rw [store_sep s_movzbl _ .W16 _ _ old2 Rd hRd hold2_len]
    simp only [Effects.All_require_write_access]
    have hval16 : (s_movzbl.regs.get (.low .r11 .W16)) =
        srcByte.toBitVec.zeroExtend 16 := by
      dsimp only [s_movzbl, Reg64s.get, Reg.base, Reg.offset, Width.bits]
      rw [get64_set64]
      simp only [↓reduceIte]
      exact drop0_take16_ze32_ze64 srcByte.toBitVec
    rw [hval16]
    have hdmem_next : (t.dmem.storeInt (dstAddr + BitVec.ofNat 64 (2 * k)) 2
        (srcByte.toBitVec.zeroExtend 16).toInt) =
        s₀.dmem.storeBytes dstAddr (target.take (2 * (k + 1)) ++ old.drop (2 * (k + 1))) := by
      rw [hdmem]
      change (s₀.dmem.storeBytes dstAddr buf).storeInt (dstAddr + BitVec.ofNat 64 (2 * k)) 2
          (srcByte.toBitVec.zeroExtend 16).toInt = _
      rw [storeInt_bufReplace (by omega) hbuf_bound, toBytes_zeroExtend16_byte srcByte]
      congr 1
      have hchunk : [srcByte, 0] = (target.drop (2 * k)).take 2 := by
        rw [drop_take2_eq (by rw [htar_len]; omega)]
        have he0 := getCharsBytes_compressed_getElem hc hl hb_le he_le (2 * k) (by omega)
        have he1 := getCharsBytes_compressed_getElem hc hl hb_le he_le (2 * k + 1) (by omega)
        simp only [Nat.mul_mod_right, ↓reduceIte, show 2 * k / 2 = k by omega,
          show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega] at he0 he1
        change [srcByte, 0] = [target[2 * k], target[2 * k + 1]]
        rw [he0, he1]; rfl
      simpa only [buf, show 2 * k + 2 = 2 * (k + 1) by omega] using
        bufReplace_prefix_extend (htar_len.trans hold.symm) (by omega) hchunk
    cont
    -- Step 10: `leaq 2(%rdi), %rdi`
    sstep; cont
    -- Step 11: `leaq 1(%rsi), %rsi`
    sstep; cont
    -- Step 12: `subl $1, %ecx`
    sstep; cont
    -- Step 13: `jmp copy_loop`
    sstep
    simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 6) rfl]
    rw [Int64.add_comm, Int64.sub_add_cancel]
    cont
    refine ih (k + 1) _ ?_ (by omega) ?_ ?_ ?_ hdmem_next
    · refine ⟨fun r hr' => ?_, ht.2.1, ht.2.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      dsimp only [s_movzbl]
      simp only [get64_set64, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2, ↓reduceIte]
      exact ht.1 r (by simp [hr'])
    · dsimp only [s_movzbl]
      simp only [get64_set64,
        show (Reg64.rcx = Reg64.rsi) ↔ False by decide,
        show (Reg64.rcx = Reg64.rdi) ↔ False by decide,
        show (Reg64.rcx = Reg64.r11) ↔ False by decide, ↓reduceIte]
      rw [hrcx]
      exact rcx_sub1_ofNat64 m' (by omega)
    · dsimp only [s_movzbl]
      simp only [get64_set64,
        show (Reg64.rsi = Reg64.rcx) ↔ False by decide,
        show (Reg64.rsi = Reg64.rdi) ↔ False by decide,
        show (Reg64.rsi = Reg64.r11) ↔ False by decide, ↓reduceIte, hrsi]
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · dsimp only [s_movzbl]
      simp only [get64_set64,
        show (Reg64.rdi = Reg64.rcx) ↔ False by decide,
        show (Reg64.rdi = Reg64.rsi) ↔ False by decide,
        show (Reg64.rdi = Reg64.r11) ↔ False by decide, ↓reduceIte, hrdi]
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.mul_add, Nat.mul_one]

/-- Execute the uncompressed `rep movsw` path starting at `copy_uncompressed:` (index 14). -/
theorem uncompressed_at [Host]
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst dstBegin : Reg64)
    (H : Embedding (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin))
    (c : BitVec 32) (d : List UInt8) (old : List UInt8) (R : Mem 64 → Prop) (s₀ t : MachineData)
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hsrc_hi : srcBegin.hi32Zero s₀.regs)
    (hdst_hi : RegOrImm.hi32Zero (.reg dstBegin) s₀.regs)
    (h_disj : ∀ r, r ∈ [obj, srcEnd, dst, dstBegin] ++ srcBegin.regs →
      r ∉ [Reg64.rcx, Reg64.rsi, Reg64.rdi, Reg64.r11])
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆
      Eq (old.At (getCharsDstAddr dst (.reg dstBegin) s₀.regs)) ⋆ R) s₀.dmem)
    (hdf : s₀.status.df = false)
    (ht : RepFrame s₀ t)
    (hdmem : t.dmem = s₀.dmem)
    (hrcx : t.regs.get64 .rcx = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin) H
      (StringGetCharsPost srcBegin srcEnd dst (.reg dstBegin) [.rcx, .rsi, .rdi, .r11] [] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 14)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let A := s₀.regs.get64 obj
  let dstAddr := getCharsDstAddr dst (.reg dstBegin) s₀.regs
  let target := getCharsBytes c d b e
  have htar_len : target.length = 2 * n := getCharsBytes_length c d hb_le he_le
  have hobj_eq : t.regs.get64 obj = s₀.regs.get64 obj := ht.1 obj (h_disj obj (by simp))
  have hdst_eq : t.regs.get64 dst = s₀.regs.get64 dst := ht.1 dst (h_disj dst (by simp))
  have hdb_eq : t.regs.get64 dstBegin = s₀.regs.get64 dstBegin := ht.1 dstBegin (h_disj dstBegin (by simp))
  have hsrc_hi' : srcBegin.hi32Zero t.regs := by
    cases srcBegin with
    | imm _ => trivial
    | reg r =>
      dsimp only [RegOrImm.hi32Zero] at hsrc_hi ⊢
      rw [ht.1 r (h_disj r (by simp [RegOrImm.regs]))]
      exact hsrc_hi
  have hsrc_b : srcBegin.eval64 t.regs = BitVec.ofNat 64 b := by
    cases srcBegin with
    | imm _ => rfl
    | reg r =>
      simp only [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32,
        ht.1 r (h_disj r (by simp [RegOrImm.regs]))]
      rfl
  have hdst_hi' : RegOrImm.hi32Zero (.reg dstBegin) t.regs := by
    dsimp only [RegOrImm.hi32Zero] at hdst_hi ⊢
    rw [ht.1 dstBegin (h_disj dstBegin (by simp))]
    exact hdst_hi
  -- Step 14: `.label "copy_uncompressed"`
  sstep; cont
  -- Step 15: `leaq arrayAddr(obj, srcBegin, .W16, 16), %rsi`
  sstep
  rw [addr_arrayAddr t.regs obj srcBegin .W16 16 _ hsrc_hi', hobj_eq, hsrc_b]
  simp only [Width.bytes, ← BitVec.ofNat_mul]
  cont
  -- Step 16: `leaq 12(%dst, %dstBegin, 2), %rdi`
  sstep
  have hdst_ne : dst ≠ .rsi := fun h => h_disj dst (by simp) (by simp [h])
  have hdb_ne : dstBegin ≠ .rsi := fun h => h_disj dstBegin (by simp) (by simp [h])
  have haddr16 : @AddrExpr.interp _ ⟨.W64⟩
      { base := some (.reg dst), idx := some ⟨dstBegin, .W16⟩, disp := .int64 12 }
      (t.regs.set64 .rsi (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b)))
      (Host.addrOf (H.start + 16)...Host.addrOf (H.start + 17)) = dstAddr := by
    have ha := addr_arrayAddr (t.regs.set64 .rsi (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b)))
      dst (.reg dstBegin) .W16 12 (Host.addrOf (H.start + 16)...Host.addrOf (H.start + 17)) (by
        dsimp only [RegOrImm.hi32Zero]
        simp only [get64_set64, hdb_ne, ↓reduceIte]
        exact hdst_hi')
    change (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr dst (.reg dstBegin) .W16 12) _ _) = _
    rw [ha]
    simp only [get64_set64, hdst_ne, hdb_ne, ↓reduceIte,
      RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32,
      hdst_eq, hdb_eq, Width.bytes, dstAddr, getCharsDstAddr, BitVec.ofNat_mul]
  rw [haddr16]
  cont
  -- Step 17: `rep movsw`
  let r2 := (t.regs.set64 .rsi (A + 16#64 + BitVec.ofNat 64 (2 * b))).set64 .rdi dstAddr
  have hrsi1 : r2.get64 .rsi = A + 16#64 + BitVec.ofNat 64 (2 * b) := by
    simp [r2, get64_set64, show (Reg64.rsi = Reg64.rdi) ↔ False by decide]
  have hrdi1 : r2.get64 .rdi = dstAddr := by
    simp [r2, get64_set64]
  have hrcx1 : r2.get64 .rcx = BitVec.ofNat 64 n := by
    simp [r2, get64_set64, hrcx, n, e, b]
  by_cases hn0 : n = 0
  · refine Program.loop_rep_movsw_zero rfl ?_ ?_
    · simpa [hn0] using hrcx1
    · simp only [Nat.add_assoc, Nat.reduceAdd]
      cont
      refine done_at obj srcBegin srcEnd dst dstBegin H c d s₀ _ ?_ ?_
      · refine ⟨fun r hr' => ?_, ht.2.1, ht.2.2⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        dsimp only [r2]
        simp only [get64_set64, hr'.2.1, hr'.2.2.1, ↓reduceIte]
        exact ht.1 r (by simp [hr'])
      · rw [hdmem]
        have heq0 : target = [] := List.eq_nil_of_length_eq_zero (by rw [htar_len, hn0])
        rw [show getCharsBytes c d b e = [] from heq0]
        have hold0 : old = [] := List.eq_nil_of_length_eq_zero (by rw [hold]; dsimp only [n] at hn0; omega)
        have hmem_dst : (Eq (([ ] : List UInt8).At dstAddr) ⋆ (StringAt A c d ⋆ R)) s₀.dmem := by
          rw [← hold0]
          rw [sep_comm (StringAt A c d) (Eq (old.At dstAddr)), sep_assoc] at hmem0
          exact hmem0
        exact (Mem.storeBytes_eq_of_sep [] dstAddr (StringAt A c d ⋆ R) s₀.dmem hmem_dst).symm
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn_lt64 : n < 2 ^ 64 := by
      have : e < 2 ^ 32 := ((s₀.regs.get64 srcEnd).setWidth 32).isLt
      omega
    have hdf1 : ({ regs := r2, zmms := t.zmms, status := t.status, dmem := t.dmem } : MachineData).status.df = false :=
      ht.2.2.trans hdf
    let f : Nat → BitVec 16 := fun k =>
      BitVec.ofInt 16 (Int.ofBytes
        [d.getD (2 * b + 2 * k) 0, d.getD (2 * b + 2 * k + 1) 0])
    let Inv : Nat → DataMem → Prop := fun k mem =>
      mem = s₀.dmem.storeBytes dstAddr (target.take (2 * k) ++ old.drop (2 * k))
    refine Program.loop_rep_movsw (s := { regs := r2, zmms := t.zmms, status := t.status, dmem := t.dmem })
      rfl hn_pos hn_lt64 hdf1 hrcx1
      (A + 16#64 + BitVec.ofNat 64 (2 * b)) dstAddr hrsi1 hrdi1 f Inv ?_ ?_ ?_
    · change t.dmem = s₀.dmem.storeBytes dstAddr (target.take 0 ++ old.drop 0)
      rw [List.take_zero, List.drop_zero, List.nil_append, hdmem]
      rw [sep_comm (StringAt A c d) (Eq (old.At dstAddr)), sep_assoc] at hmem0
      exact (Mem.storeBytes_eq_of_sep old dstAddr (StringAt A c d ⋆ R) s₀.dmem hmem0).symm
    · intro k mem hk hinv
      let buf := target.take (2 * k) ++ old.drop (2 * k)
      have hbuf_len : buf.length = 2 * n := by
        simp only [buf, List.length_append, List.length_take, List.length_drop, htar_len, hold]
        omega
      have hbuf_lt : buf.length < 2 ^ 64 := by omega
      have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
      have h2bk_lt : 2 * b + 2 * k < d.length := by rw [hl, strByteLen_uncompressed hc]; omega
      have h2bk1_lt : 2 * b + 2 * k + 1 < d.length := by rw [hl, strByteLen_uncompressed hc]; omega
      have hsrc_addr : A + 16#64 + BitVec.ofNat 64 (2 * b) + BitVec.ofNat 64 (2 * k) =
          A + 16#64 + BitVec.ofNat 64 (2 * b + 2 * k) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hload_src := mem_loadInt_src_slice hmem0 hl (hold.trans hbuf_len.symm) hbuf_lt
        (off := 2 * b + 2 * k) (len := 2) (by omega) (by decide)
      have hsrc_list : (d.drop (2 * b + 2 * k)).take 2 = [d[2 * b + 2 * k]'h2bk_lt, d[2 * b + 2 * k + 1]'h2bk1_lt] :=
        drop_take2_eq h2bk1_lt
      have hd0 : d.getD (2 * b + 2 * k) 0 = d[2 * b + 2 * k]'h2bk_lt := by
        change d[2 * b + 2 * k]?.getD 0 = _; rw [List.getElem?_eq_getElem h2bk_lt]; rfl
      have hd1 : d.getD (2 * b + 2 * k + 1) 0 = d[2 * b + 2 * k + 1]'h2bk1_lt := by
        change d[2 * b + 2 * k + 1]?.getD 0 = _; rw [List.getElem?_eq_getElem h2bk1_lt]; rfl
      obtain ⟨Rd, hRd⟩ := mem_expose_dst_slice hmem0 (hold.trans hbuf_len.symm) hbuf_bound
        (off := 2 * k) (len := 2) (by omega)
      have hload_dst : (s₀.dmem.storeBytes dstAddr buf).loadInt (dstAddr + BitVec.ofNat 64 (2 * k)) 2 =
          some (Int.ofBytes ((buf.drop (2 * k)).take 2)) :=
        Mem.loadInt_sep _ _ 2 Rd _ hRd (by simp [List.length_take, List.length_drop, hbuf_len]; omega) (by decide)
      refine ⟨Int.ofBytes [d[2 * b + 2 * k]'h2bk_lt, d[2 * b + 2 * k + 1]'h2bk1_lt],
        Int.ofBytes ((buf.drop (2 * k)).take 2), ?_, ?_, ?_, ?_⟩
      · rw [hinv, hsrc_addr]; simpa only [hsrc_list] using hload_src
      · simp only [f, hd0, hd1]
      · rw [hinv]; exact hload_dst
      · rw [hinv]
        change (s₀.dmem.storeBytes dstAddr buf).storeInt (dstAddr + BitVec.ofNat 64 (2 * k)) 2 (f k).toInt = _
        rw [storeInt_bufReplace (by omega) hbuf_bound]
        have hf_bytes : Int.toBytes 2 (f k).toInt = [d[2 * b + 2 * k]'h2bk_lt, d[2 * b + 2 * k + 1]'h2bk1_lt] := by
          simp only [f, hd0, hd1]
          exact toBytes_ofInt_ofBytes 2 _ rfl
        rw [hf_bytes]
        congr 1
        have hchunk : [d[2 * b + 2 * k]'h2bk_lt, d[2 * b + 2 * k + 1]'h2bk1_lt] = (target.drop (2 * k)).take 2 := by
          rw [drop_take2_eq (by rw [htar_len]; omega)]
          have he0 := getCharsBytes_uncompressed_getElem hc hl hb_le he_le (2 * k) (by omega)
          have he1 := getCharsBytes_uncompressed_getElem hc hl hb_le he_le (2 * k + 1) (by omega)
          change [d[2 * b + 2 * k]'h2bk_lt, d[2 * b + 2 * k + 1]'h2bk1_lt] = [target[2 * k], target[2 * k + 1]]
          rw [he0, he1]; rfl
        simpa only [buf, show 2 * k + 2 = 2 * (k + 1) by omega] using
          bufReplace_prefix_extend (htar_len.trans hold.symm) (by omega) hchunk
    · intro t' hinv' hzmms' hst' _ _ _ hregs'
      simp only [Nat.add_assoc, Nat.reduceAdd]
      cont
      refine done_at obj srcBegin srcEnd dst dstBegin H c d s₀ t' ?_ ?_
      · refine ⟨fun r hr' => ?_, ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          rw [hregs' r (by simp [hr'.1, hr'.2.1, hr'.2.2.1])]
          dsimp only [r2]
          simp only [get64_set64, hr'.2.1, hr'.2.2.1, ↓reduceIte]
          exact ht.1 r (by simp [hr'])
        · exact hzmms'.trans ht.2.1
        · exact hst' ▸ ht.2.2
      · rw [hinv']
        congr 1
        rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

end GetCharsRepProof

open GetCharsRepProof GetCharsProof
open Proof (get_low32 get_low64 set_low32 set_low64 get64_set64 sw32_64 sw32_ofNat)

/-- Correctness of ART's baseline `String.getCharsNoCheck` lowering (`stringGetCharsRepProg`),
    proved against the shared specification predicates `StringGetCharsPre` and `StringGetCharsPost`
    plus the x86_64 SysV ABI precondition `s.status.df = false`. -/
theorem stringGetCharsRep_correct [Host]
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst dstBegin : Reg64)
    (h_disj : ∀ r, r ∈ [obj, srcEnd, dst, dstBegin] ++ srcBegin.regs →
      r ∉ [Reg64.rcx, Reg64.rsi, Reg64.rdi, Reg64.r11])
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ s.status.df = false ∧
        StringGetCharsPre obj srcBegin srcEnd dst (.reg dstBegin) c d s ⦄
      stringGetCharsRepProg obj srcBegin srcEnd dst dstBegin
    ⦃ fun _ => StringGetCharsPost srcBegin srcEnd dst (.reg dstBegin)
        [.rcx, .rsi, .rdi, .r11] [] c d s₀; fun _ _ => False ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hdf, hl, hb_le, he_le, hsrc_hi, hdst_hi, _hdst_even, _hfit1, _hfit2, ⟨old, R, hold, hmem⟩⟩
  apply Program.wp_of_loop
  intro H
  let b := srcBegin.toNat s.regs
  let e := ((s.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  have he32 : e < 2 ^ 32 := ((s.regs.get64 srcEnd).setWidth 32).isLt
  have hb32 : b < 2 ^ 32 := RegOrImm.toNat_lt
  -- Step 0: `movl %srcEnd32, %ecx`
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  sstep
  have hrcx0 : (((s.regs.get64 srcEnd).setWidth 32).zeroExtend 64) = BitVec.ofNat 64 e := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.setWidth 64 (BitVec.setWidth 32 (s.regs.get64 srcEnd))).toNat = (BitVec.ofNat 64 e).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  cont
  -- Step 1: `subSrcBeginInstr srcBegin`
  have hrcx1_eq : (((s.regs.get64 srcEnd).setWidth 32 -
      srcBegin.eval32 (s.regs.set64 .rcx (BitVec.ofNat 64 e))).zeroExtend 64) =
      BitVec.ofNat 64 n := by
    have hev : srcBegin.eval32 (s.regs.set64 .rcx (BitVec.ofNat 64 e)) = BitVec.ofNat 32 b := by
      cases srcBegin with
      | imm v =>
        apply BitVec.eq_of_toNat_eq; simp [b, RegOrImm.toNat, RegOrImm.eval32]
      | reg r =>
        have hr_rcx : r ≠ .rcx := fun h => h_disj r (by simp [RegOrImm.regs]) (by simp [h])
        simp only [RegOrImm.eval32, get64_set64, hr_rcx, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        simp [b, RegOrImm.toNat, RegOrImm.eval32]
    have hes : (s.regs.get64 srcEnd).setWidth 32 = BitVec.ofNat 32 e := by
      apply BitVec.eq_of_toNat_eq; simp [e]
    rw [hev, hes]
    exact sub32_ofNat_ze64 hb_le he32
  cases srcBegin with
  | reg r =>
    have hr_rcx : r ≠ .rcx := fun h => h_disj r (by simp [RegOrImm.regs]) (by simp [h])
    sstep; cont
    -- Step 2: `testl $1, 8(%obj)`
    sstep
    have hobj_ne : obj ≠ .rcx := fun h => h_disj obj (by simp) (by simp [h])
    simp only [hobj_ne, ↓reduceIte]
    rw [load_string_count_at hmem]
    simp only [Effects.All, Effects.All_require_read_access, test_and1_of_count]
    intro _af
    cont
    -- Step 3: `jnz copy_uncompressed`
    sstep
    by_cases hc : c.getLsbD 0 = true
    · simp only [hc, Bool.not_true, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 14) rfl]
      cont
      refine uncompressed_at obj (.reg r) srcEnd dst dstBegin H c d old R s _ hc hl hb_le he_le hold
        hsrc_hi hdst_hi h_disj hmem hdf ?_ rfl ?_
      · refine ⟨fun rx hrx => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.1, ↓reduceIte]
      · simp only [hrcx0, get64_set64, ↓reduceIte]
        simpa [RegOrImm.eval32, get64_set64, hr_rcx, ↓reduceIte, b, e, n] using hrcx1_eq
    · have hcf : c.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      -- Step 4: `leaq arrayAddr(obj, .reg r, .W8, 16), %rsi`
      sstep; cont
      -- Step 5: `leaq 12(%dst, %dstBegin, 2), %rdi`
      sstep; cont
      -- Step 6: `copy_loop:`
      refine compressed_loop_ind obj (.reg r) srcEnd dst dstBegin hlab H c d old R s
        hcf hl hb_le he_le hold hmem n 0 _ ?_ (Nat.zero_add n) ?_ ?_ ?_ ?_
      · refine ⟨fun rx hrx => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.1, hrx.2.1, hrx.2.2.1, ↓reduceIte]
      · simp only [get64_set64, ↓reduceIte, hrcx0]
        simpa [RegOrImm.eval32, get64_set64, hr_rcx, ↓reduceIte] using hrcx1_eq
      · simp only [get64_set64, show (Reg64.rsi = Reg64.rdi) ↔ False by decide, ↓reduceIte]
        have hobj_s := h_disj obj (by simp)
        have hr_s := h_disj r (by simp [RegOrImm.regs])
        have h_r_rcx : r ≠ .rcx := fun h => hr_s (by simp [h])
        have h_obj_rcx : obj ≠ .rcx := fun h => hobj_s (by simp [h])
        change (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr obj (.reg r) .W8 16) _ _) = _
        rw [addr_arrayAddr _ obj (.reg r) .W8 16 _ (by
          simp only [RegOrImm.hi32Zero, get64_set64, h_r_rcx, ite_false]
          exact hsrc_hi)]
        simp only [get64_set64, RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, Width.bytes,
          h_obj_rcx, h_r_rcx, ite_false, Nat.add_zero, BitVec.one_mul]
      · simp only [get64_set64, ↓reduceIte]
        have hdst_s := h_disj dst (by simp)
        have hdb_s := h_disj dstBegin (by simp)
        have hdb_rsi : dstBegin ≠ .rsi := fun h => hdb_s (by simp [h])
        have hdb_rcx : dstBegin ≠ .rcx := fun h => hdb_s (by simp [h])
        have hdst_rsi : dst ≠ .rsi := fun h => hdst_s (by simp [h])
        have hdst_rcx : dst ≠ .rcx := fun h => hdst_s (by simp [h])
        change (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr dst (.reg dstBegin) .W16 12) _ _) = _
        rw [addr_arrayAddr _ dst (.reg dstBegin) .W16 12 _ (by
          simp only [RegOrImm.hi32Zero, get64_set64, hdb_rsi, hdb_rcx, ite_false]
          exact hdst_hi)]
        simp [get64_set64, RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, Width.bytes,
          hdst_rsi, hdst_rcx, hdb_rsi, hdb_rcx, getCharsDstAddr, BitVec.add_zero]
      · rw [sep_comm (StringAt (s.regs.get64 obj) c d) (Eq (old.At _)), sep_assoc] at hmem
        exact (Mem.storeBytes_eq_of_sep old _ _ s.dmem hmem).symm
  | imm v =>
    sstep; cont
    -- Step 2: `testl $1, 8(%obj)`
    sstep
    have hobj_ne : obj ≠ .rcx := fun h => h_disj obj (by simp) (by simp [h])
    simp only [hobj_ne, ↓reduceIte]
    rw [load_string_count_at hmem]
    simp only [Effects.All, Effects.All_require_read_access, test_and1_of_count]
    intro _af
    cont
    -- Step 3: `jnz copy_uncompressed`
    sstep
    by_cases hc : c.getLsbD 0 = true
    · simp only [hc, Bool.not_true, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 14) rfl]
      cont
      refine uncompressed_at obj (.imm v) srcEnd dst dstBegin H c d old R s _ hc hl hb_le he_le hold
        hsrc_hi hdst_hi h_disj hmem hdf ?_ rfl ?_
      · refine ⟨fun rx hrx => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.1, ↓reduceIte]
      · simp only [hrcx0, get64_set64, ↓reduceIte]
        simpa [RegOrImm.eval32, b, e, n] using hrcx1_eq
    · have hcf : c.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      -- Step 4: `leaq arrayAddr(obj, .imm v, .W8, 16), %rsi`
      sstep; cont
      -- Step 5: `leaq 12(%dst, %dstBegin, 2), %rdi`
      sstep; cont
      -- Step 6: `copy_loop:`
      refine compressed_loop_ind obj (.imm v) srcEnd dst dstBegin hlab H c d old R s
        hcf hl hb_le he_le hold hmem n 0 _ ?_ (Nat.zero_add n) ?_ ?_ ?_ ?_
      · refine ⟨fun rx hrx => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.1, hrx.2.1, hrx.2.2.1, ↓reduceIte]
      · simp only [get64_set64, ↓reduceIte, hrcx0]
        simpa [RegOrImm.eval32] using hrcx1_eq
      · simp only [get64_set64, show (Reg64.rsi = Reg64.rdi) ↔ False by decide, ↓reduceIte]
        have hobj_s := h_disj obj (by simp)
        have h_obj_rcx : obj ≠ .rcx := fun h => hobj_s (by simp [h])
        change (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr obj (.imm v) .W8 16) _ _) = _
        rw [addr_arrayAddr _ obj (.imm v) .W8 16 _ trivial]
        simp only [get64_set64, RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, Width.bytes,
          h_obj_rcx, ite_false, Nat.add_zero, BitVec.one_mul]
      · simp only [get64_set64, ↓reduceIte]
        have hdst_s := h_disj dst (by simp)
        have hdb_s := h_disj dstBegin (by simp)
        have hdb_rsi : dstBegin ≠ .rsi := fun h => hdb_s (by simp [h])
        have hdb_rcx : dstBegin ≠ .rcx := fun h => hdb_s (by simp [h])
        have hdst_rsi : dst ≠ .rsi := fun h => hdst_s (by simp [h])
        have hdst_rcx : dst ≠ .rcx := fun h => hdst_s (by simp [h])
        change (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr dst (.reg dstBegin) .W16 12) _ _) = _
        rw [addr_arrayAddr _ dst (.reg dstBegin) .W16 12 _ (by
          simp only [RegOrImm.hi32Zero, get64_set64, hdb_rsi, hdb_rcx, ite_false]
          exact hdst_hi)]
        simp [get64_set64, RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, Width.bytes,
          hdst_rsi, hdst_rcx, hdb_rsi, hdb_rcx, getCharsDstAddr, BitVec.add_zero]
      · rw [sep_comm (StringAt (s.regs.get64 obj) c d) (Eq (old.At _)), sep_assoc] at hmem
        exact (Mem.storeBytes_eq_of_sep old _ _ s.dmem hmem).symm

end

end Kraken.X64.Art
