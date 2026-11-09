module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
public import Kraken.X64.Sep
import Kraken.X64.Parser
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

/-- Instruction subtracting `srcBegin` (register or non-zero 32-bit immediate) from `%cnt32`. -/
@[expose] def subCntSrcBeginInstr (cnt : Reg64) (srcBegin : RegOrImm) : _root_.Directive :=
  .instr (.regular .W32 .W32 (.sub (.reg (.low cnt .W32))
    (match srcBegin with
    | .reg r => .reg (.low r .W32)
    | .imm v => .imm (.int64 (Int64.ofNat v.toNat)))))

/--
Body of the AVX2 `String.getCharsNoCheck` intrinsic starting at the compression flag test
`testl $1, 8(%obj)`. Parameterized so its directive indices are fixed independently of whether
`subl $srcBegin, %cnt32` was elided for constant `srcBegin = 0`.
-/
@[expose] def stringGetCharsBody
    (obj : Reg64) (srcBegin : RegOrImm) (dst : Reg64) (dstBegin : RegOrImm)
    (src dst_ptr cnt tmp : Reg64) (ymm0 ymm1 : AvxReg .W256) : _root_.Program :=
  let xmm0 : AvxReg .W128 := .xmm ymm0.base
  let vmovd_tmp_xmm0 : _root_.Directive :=
    .instr (.avx .W64 .W128 (.vmovIn .W32 xmm0 (.reg (.low tmp .W32))))
  let vmovq_xmm0_tmp : _root_.Directive :=
    .instr (.avx .W64 .W128 (.vmovOut .W64 (.reg (.low tmp .W64)) xmm0))
  parse("
    testl $1, 8(%❰obj❱)
    jnz copy_uncompressed
    ❰.instr (.regular .W64 .W64 (.lea (.low src .W64) (arrayAddr obj srcBegin .W8 16)))❱
    ❰.instr (.regular .W64 .W64 (.lea (.low dst_ptr .W64) (arrayAddr dst dstBegin .W16 12)))❱
    cmpl $16, %❰.low cnt .W32❱
    jb compressed_small
    cmpl $32, %❰.low cnt .W32❱
    ja compressed_gt32
  compressed_le32:
    vpmovzxbw 0(%❰src❱), %❰ymm0❱
    vpmovzxbw -16(%❰src❱, %❰cnt❱, 1), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  compressed_gt32:
    cmpl $64, %❰.low cnt .W32❱
    jbe compressed_lt64
    cmpl $192, %❰.low cnt .W32❱
    jb compressed_pre_loop
    vpmovzxbw 0(%❰src❱), %❰ymm0❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    movl %❰.low dst_ptr .W32❱, %❰.low tmp .W32❱
    andl $31, %❰.low tmp .W32❱
    subl $32, %❰.low tmp .W32❱
    negl %❰.low tmp .W32❱
    addq %❰.low tmp .W64❱, %❰.low dst_ptr .W64❱
    shrl $1, %❰.low tmp .W32❱
    addq %❰.low tmp .W64❱, %❰.low src .W64❱
    subl %❰.low tmp .W32❱, %❰.low cnt .W32❱
  compressed_pre_loop:
    subl $64, %❰.low cnt .W32❱
  compressed_avx4_loop:
    vpmovzxbw 0(%❰src❱), %❰ymm0❱
    vpmovzxbw 16(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 32(%❰dst_ptr❱)
    vpmovzxbw 32(%❰src❱), %❰ymm0❱
    vpmovzxbw 48(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 64(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 96(%❰dst_ptr❱)
    addq $64, %❰.low src .W64❱
    addq $128, %❰.low dst_ptr .W64❱
    subl $64, %❰.low cnt .W32❱
    jae compressed_avx4_loop
    addl $64, %❰.low cnt .W32❱
    je done_vzero
    cmpl $16, %❰.low cnt .W32❱
    jbe compressed_tail
    cmpl $32, %❰.low cnt .W32❱
    jbe compressed_le32
  compressed_lt64:
    vpmovzxbw 0(%❰src❱), %❰ymm0❱
    vpmovzxbw 16(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 32(%❰dst_ptr❱)
    vpmovzxbw -32(%❰src❱, %❰cnt❱, 1), %❰ymm0❱
    vpmovzxbw -16(%❰src❱, %❰cnt❱, 1), %❰ymm1❱
    vmovdqu %❰ymm0❱, -64(%❰dst_ptr❱, %❰cnt❱, 2)
    vmovdqu %❰ymm1❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  compressed_tail:
    vpmovzxbw -16(%❰src❱, %❰cnt❱, 1), %❰ymm0❱
    vmovdqu %❰ymm0❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  compressed_small:
    cmpl $4, %❰.low cnt .W32❱
    jb compressed_lt4
    cmpl $8, %❰.low cnt .W32❱
    jb compressed_4_7
    vpmovzxbw 0(%❰src❱), %❰xmm0❱
    vmovdqu %❰xmm0❱, 0(%❰dst_ptr❱)
    vpmovzxbw -8(%❰src❱, %❰cnt❱, 1), %❰xmm0❱
    vmovdqu %❰xmm0❱, -16(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  compressed_4_7:
    movl 0(%❰src❱), %❰.low tmp .W32❱
    ❰vmovd_tmp_xmm0❱
    vpmovzxbw %❰xmm0❱, %❰xmm0❱
    ❰vmovq_xmm0_tmp❱
    movq %❰.low tmp .W64❱, 0(%❰dst_ptr❱)
    movl -4(%❰src❱, %❰cnt❱, 1), %❰.low tmp .W32❱
    ❰vmovd_tmp_xmm0❱
    vpmovzxbw %❰xmm0❱, %❰xmm0❱
    ❰vmovq_xmm0_tmp❱
    movq %❰.low tmp .W64❱, -8(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  compressed_lt4:
    cmpl $2, %❰.low cnt .W32❱
    jb compressed_1
    movzbl 0(%❰src❱), %❰.low tmp .W32❱
    movw %❰.low tmp .W16❱, 0(%❰dst_ptr❱)
    movzbl 1(%❰src❱), %❰.low tmp .W32❱
    movw %❰.low tmp .W16❱, 2(%❰dst_ptr❱)
    je done
    movzbl 2(%❰src❱), %❰.low tmp .W32❱
    movw %❰.low tmp .W16❱, 4(%❰dst_ptr❱)
    jmp done
  compressed_1:
    testl %❰.low cnt .W32❱, %❰.low cnt .W32❱
    je done
    movzbl 0(%❰src❱), %❰.low tmp .W32❱
    movw %❰.low tmp .W16❱, 0(%❰dst_ptr❱)
    jmp done
  copy_uncompressed:
    ❰.instr (.regular .W64 .W64 (.lea (.low src .W64) (arrayAddr obj srcBegin .W16 16)))❱
    ❰.instr (.regular .W64 .W64 (.lea (.low dst_ptr .W64) (arrayAddr dst dstBegin .W16 12)))❱
    cmpl $16, %❰.low cnt .W32❱
    jb uncompressed_small
    cmpl $32, %❰.low cnt .W32❱
    ja uncompressed_gt32
  uncompressed_le32:
    vmovdqu 0(%❰src❱), %❰ymm0❱
    vmovdqu -32(%❰src❱, %❰cnt❱, 2), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  uncompressed_gt32:
    cmpl $64, %❰.low cnt .W32❱
    jbe uncompressed_lt64
    cmpl $192, %❰.low cnt .W32❱
    jb uncompressed_pre_loop
    vmovdqu 0(%❰src❱), %❰ymm0❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    movl %❰.low dst_ptr .W32❱, %❰.low tmp .W32❱
    andl $31, %❰.low tmp .W32❱
    subl $32, %❰.low tmp .W32❱
    negl %❰.low tmp .W32❱
    addq %❰.low tmp .W64❱, %❰.low src .W64❱
    addq %❰.low tmp .W64❱, %❰.low dst_ptr .W64❱
    shrl $1, %❰.low tmp .W32❱
    subl %❰.low tmp .W32❱, %❰.low cnt .W32❱
  uncompressed_pre_loop:
    subl $64, %❰.low cnt .W32❱
  uncompressed_avx4_loop:
    vmovdqu 0(%❰src❱), %❰ymm0❱
    vmovdqu 32(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 32(%❰dst_ptr❱)
    vmovdqu 64(%❰src❱), %❰ymm0❱
    vmovdqu 96(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 64(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 96(%❰dst_ptr❱)
    addq $128, %❰.low src .W64❱
    addq $128, %❰.low dst_ptr .W64❱
    subl $64, %❰.low cnt .W32❱
    jae uncompressed_avx4_loop
    addl $64, %❰.low cnt .W32❱
    je done_vzero
    cmpl $16, %❰.low cnt .W32❱
    jbe uncompressed_tail
    cmpl $32, %❰.low cnt .W32❱
    jbe uncompressed_le32
  uncompressed_lt64:
    vmovdqu 0(%❰src❱), %❰ymm0❱
    vmovdqu 32(%❰src❱), %❰ymm1❱
    vmovdqu %❰ymm0❱, 0(%❰dst_ptr❱)
    vmovdqu %❰ymm1❱, 32(%❰dst_ptr❱)
    vmovdqu -64(%❰src❱, %❰cnt❱, 2), %❰ymm0❱
    vmovdqu -32(%❰src❱, %❰cnt❱, 2), %❰ymm1❱
    vmovdqu %❰ymm0❱, -64(%❰dst_ptr❱, %❰cnt❱, 2)
    vmovdqu %❰ymm1❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  uncompressed_small:
    cmpl $8, %❰.low cnt .W32❱
    jae uncompressed_8_15
    cmpl $4, %❰.low cnt .W32❱
    jb uncompressed_lt4
    movq 0(%❰src❱), %❰.low tmp .W64❱
    movq %❰.low tmp .W64❱, 0(%❰dst_ptr❱)
    movq -8(%❰src❱, %❰cnt❱, 2), %❰.low tmp .W64❱
    movq %❰.low tmp .W64❱, -8(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done
  uncompressed_lt4:
    cmpl $2, %❰.low cnt .W32❱
    jb uncompressed_1
    movl 0(%❰src❱), %❰.low tmp .W32❱
    movl %❰.low tmp .W32❱, 0(%❰dst_ptr❱)
    movl -4(%❰src❱, %❰cnt❱, 2), %❰.low tmp .W32❱
    movl %❰.low tmp .W32❱, -4(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done
  uncompressed_1:
    testl %❰.low cnt .W32❱, %❰.low cnt .W32❱
    je done
    movzwl 0(%❰src❱), %❰.low tmp .W32❱
    movw %❰.low tmp .W16❱, 0(%❰dst_ptr❱)
    jmp done
  uncompressed_8_15:
    vmovdqu 0(%❰src❱), %❰xmm0❱
    vmovdqu %❰xmm0❱, 0(%❰dst_ptr❱)
    vmovdqu -16(%❰src❱, %❰cnt❱, 2), %❰xmm0❱
    vmovdqu %❰xmm0❱, -16(%❰dst_ptr❱, %❰cnt❱, 2)
    jmp done_vzero
  uncompressed_tail:
    vmovdqu -32(%❰src❱, %❰cnt❱, 2), %❰ymm0❱
    vmovdqu %❰ymm0❱, -32(%❰dst_ptr❱, %❰cnt❱, 2)
  done_vzero:
    vzeroupper
  done:
  ")

/-- Parameterized assembly template for AVX2 `String.getCharsNoCheck` in ART, matching
    `VisitStringGetCharsNoCheck` in `intrinsics_x86_64.cc`. -/
@[expose] def stringGetCharsProg
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst : Reg64) (dstBegin : RegOrImm)
    (src dst_ptr cnt tmp : Reg64) (ymm0 ymm1 : AvxReg .W256) : _root_.Program :=
  parse("
    movl %❰.low srcEnd .W32❱, %❰.low cnt .W32❱
  ") ++
  (if srcBegin == .imm 0#32 then [] else [subCntSrcBeginInstr cnt srcBegin]) ++
  stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1

set_option maxRecDepth 2048 in
theorem stringGetCharsBody_length
    (obj : Reg64) (srcBegin : RegOrImm) (dst : Reg64) (dstBegin : RegOrImm)
    (src dst_ptr cnt tmp : Reg64) (ymm0 ymm1 : AvxReg .W256) :
    (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1).length = 198 := rfl

namespace GetCharsAvxProof

open Proof (addr_base_disp addr_sib1_disp addr_base_disp' addr_sib1_disp'
  i64_add_sub sub_beq_zero cf_ofNat32 ofNat32_eq_zero
  sw32_64 sw32_ofNat regZmms_ext lowMm
  get512_zeroUpper_low get512_zeroUpper_high
  zmms_get_set zmms_set_set zeroUpper_set_get
  get64_set64 get512_set512 get_low32 get_low64 set_low32 set_low64
  cnt1)
open GetCharsProof

abbrev LabelsPlaced [Host] : Prop :=
  ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i

theorem wp_append [Host] {a b : _root_.Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (ha : a.wp (fun s' => b.wp Q E s') E s) : (a ++ b).wp Q E s := by
  intro k hk
  obtain ⟨hka, hkb⟩ := List.IsInfixAt.append hk
  refine eventually_trans _ _ _ _ (ha k hka) ?_
  rintro ⟨s', pc'⟩ (⟨hpc, hb⟩ | hE)
  · dsimp only at hpc hb
    subst hpc
    refine eventually_trans _ _ _ _ (hb (k + a.length) hkb) ?_
    rintro st (⟨hend, hq⟩ | hE)
    · exact Eventually.done _ (Or.inl ⟨by rw [hend, List.length_append, Nat.add_assoc], hq⟩)
    · exact Eventually.done _ (Or.inr hE)
  · exact Eventually.done _ (Or.inr hE)

theorem addr_sib2_disp [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W16⟩, disp := .int64 d } regs p).zeroExtend 64 =
      regs.get64 r + 2#64 * regs.get64 i + d.toBitVec := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Width.bits, Width.bytes]
  rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.extractLsb'_eq_self,
    BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.ofInt_natCast,
    ← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  bv_decide

theorem addr_sib2_disp' [Labels] (regs : Reg64s) (r i : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W64⟩ { base := some (.reg r), idx := some ⟨i, .W16⟩, disp := .int64 d } regs p : BitVec 64) =
      regs.get64 r + 2#64 * regs.get64 i + d.toBitVec := by
  have := addr_sib2_disp regs r i d p
  simpa using this

theorem zmms_get_set_xmm (z : RegZmms) (x : AvxReg .W128) (v : BitVec 128) :
    (z.set x v).get x = v := by
  cases x with
  | xmm b =>
    simp only [RegZmms.get, RegZmms.set, AvxReg.base, get512_set512, ↓reduceIte, BitVec.take,
      AvxWidth.bits]
    bv_decide

theorem zmms_set_set_xmm (z : RegZmms) (x : AvxReg .W128) (u v : BitVec 128) :
    (z.set x u).set x v = z.set x v := by
  cases x with
  | xmm b =>
    apply regZmms_ext; intro r
    by_cases hr : r = b
    · subst hr; simp [RegZmms.set, get512_set512]
    · simp [RegZmms.set, get512_set512, hr]

theorem zmms_get_set_ymm_ne {z : RegZmms} {y1 y2 : AvxReg .W256} (v : BitVec 256)
    (h : y1.base ≠ y2.base) :
    (z.set y1 v).get y2 = z.get y2 := by
  cases y1 with
  | ymm r1 =>
    cases y2 with
    | ymm r2 =>
      simp only [AvxReg.base] at h
      simp only [RegZmms.get, RegZmms.set, AvxReg.base, get512_set512, h.symm, ↓reduceIte]

theorem bufReplace_extend_to {buf target chunk : List UInt8} {W off len total : Nat}
    (hbuf : buf.length = total) (htar : target.length = total)
    (hoff_W : off ≤ W) (hle : off + len ≤ total) (hW_le : W ≤ total)
    (hagree : ∀ j (hj : j < W), buf[j]'(by rw [hbuf]; exact Nat.lt_of_lt_of_le hj hW_le) =
        target[j]'(by rw [htar]; exact Nat.lt_of_lt_of_le hj hW_le))
    (hlen : chunk.length = len)
    (hchunk : ∀ i (hi : i < len), chunk[i]'(by omega) =
        target[off + i]'(by rw [htar]; omega)) :
    (bufReplace buf off len chunk).length = total ∧
    ∀ j (hj : j < max W (off + len)),
      (bufReplace buf off len chunk)[j]'(by rw [bufReplace_length (by rw [hbuf]; exact hle) hlen, hbuf]; omega) =
        target[j]'(by rw [htar]; omega) := by
  refine ⟨by rw [bufReplace_length (by rw [hbuf]; exact hle) hlen, hbuf], ?_⟩
  intro j hj
  rw [bufReplace_getElem (by rw [hbuf]; exact hle) hlen (j := j) (by rw [hbuf]; omega)]
  split
  · next h =>
    have := hchunk (j - off) (by omega)
    have hj_eq : off + (j - off) = j := by omega
    simpa [hj_eq] using this
  · next h =>
    have hj_W : j < W := by omega
    exact hagree j hj_W

theorem list_eq_of_pointwise {a b : List UInt8} {total : Nat}
    (ha : a.length = total) (hb : b.length = total)
    (h : ∀ j (hj : j < total), a[j]'(by omega) = b[j]'(by omega)) :
    a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro j hj1 _
  exact h j (by omega)

theorem getCharsDstAddr_even {dstVal idxVal : BitVec 64}
    (hdst : dstVal.getLsbD 0 = false) :
    (dstVal + 12#64 + 2#64 * idxVal).getLsbD 0 = false := by
  bv_decide

theorem bitvec32_ofNat_ze64 (n : Nat) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

theorem bitvec32_toNat_lt_iff_cf (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 32 a - BitVec.ofNat 32 b).unsigned !=
      (BitVec.ofNat 32 a).unsigned - (BitVec.ofNat 32 b).unsigned) = decide (a < b) := by
  change (((BitVec.ofNat 32 a - BitVec.ofNat 32 b).toNat : Int) !=
    ((BitVec.ofNat 32 a).toNat : Int) - ((BitVec.ofNat 32 b).toNat : Int)) = decide (a < b)
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  by_cases hlt : a < b
  · have hmod : (2 ^ 32 - b + a) % 2 ^ 32 = 2 ^ 32 - b + a := by omega
    rw [hmod, decide_eq_true hlt]
    apply bne_iff_ne.mpr
    omega
  · have hmod : (2 ^ 32 - b + a) % 2 ^ 32 = a - b := by
      have : 2 ^ 32 - b + a = (a - b) + 1 * 2 ^ 32 := by omega
      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, decide_eq_false hlt]
    apply Bool.eq_false_iff.mpr
    simp only [bne_iff_ne, ne_eq, Classical.not_not]
    omega

theorem bitvec32_eq_iff_zf (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0#32) = decide (a = b) := by
  by_cases heq : a = b
  · subst heq; simp
  · rw [decide_eq_false heq, beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, BitVec.toNat_ofNat] at this
    simp only [Nat.zero_mod] at this
    omega

theorem bitvec32_and31_props (x : BitVec 32) :
    have t := -((x &&& 31#32) - 32#32)
    t &&& 0xffffffff#32 = t := by bv_decide

theorem bitvec32_sub_ze64 (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b).zeroExtend 64 = BitVec.ofNat 64 (a - b) := by
  have heq : BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 32)]
    have h1 : 2 ^ 32 - b + a = (a - b) + 1 * 2 ^ 32 := by omega
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [heq]
  exact bitvec32_ofNat_ze64 (a - b) (by omega)

theorem setWidth16_ze32_ze64_byte (b : UInt8) :
    (((BitVec.ofInt 8 (Int.ofBytes [b])).zeroExtend 32).zeroExtend 64).setWidth 16 =
      b.toBitVec.zeroExtend 16 := by
  have heq : BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
    simp [Int.ofBytes, BitVec.ofInt_natCast]
  rw [heq]
  bv_decide

theorem setWidth16_ofInt16_ze32_ze64 (bs : List UInt8) (_hbs : bs.length = 2) :
    (((BitVec.ofInt 16 (Int.ofBytes bs)).zeroExtend 32).zeroExtend 64).setWidth 16 =
      BitVec.ofInt 16 (Int.ofBytes bs) := by
  bv_decide

theorem loadInt1_ofBytes_toInt (b : UInt8) :
    Int.toBytes 2 ((b.toBitVec.zeroExtend 16).toInt) = [b, 0] :=
  toBytes_zeroExtend16_byte b

theorem get16_set64_ze32_ze64 (regs : Reg64s) (r : Reg64) (b : UInt8) :
    ((regs.set64 r (((BitVec.ofInt 8 (Int.ofBytes [b])).zeroExtend 32).zeroExtend 64)).get
      (.low r .W16)) = b.toBitVec.zeroExtend 16 := by
  dsimp only [Reg64s.get, Reg.base, Reg.offset, Width.bits]
  rw [get64_set64]
  simp only [↓reduceIte]
  rw [show BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec by simp [Int.ofBytes, BitVec.ofInt_natCast]]
  dsimp only [BitVec.drop, BitVec.take]
  bv_decide

theorem toBytes_pmovzxbw_64_lsb (bs : List UInt8) (hbs : bs.length = 4) :
    Int.toBytes 8
      (BitVec.extractLsb' 0 64
        (BitVec.pmovzxbw 128 ((BitVec.ofInt 32 (Int.ofBytes bs)).zeroExtend 128))).toInt =
      expBytes bs := by
  simpa [BitVec.take] using toBytes_pmovzxbw_64 bs hbs

private theorem add_ofNat_sub_ofNat {base : BitVec 64} {a w : Nat} (hw : w ≤ a) (ha : a < 2 ^ 64) :
    base + BitVec.ofNat 64 a - BitVec.ofNat 64 w = base + BitVec.ofNat 64 (a - w) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : w < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a - w < 2 ^ 64)]
  have h1 : 2 ^ 64 - w + a = (a - w) + 1 * 2 ^ 64 := by omega
  rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem neg_disp_sub {base : BitVec 64} {done rem w : Nat}
    (hw : w ≤ 2 * (done + rem)) (hle : done + rem < 2 ^ 32) :
    base + BitVec.ofNat 64 (2 * done) + 2#64 * BitVec.ofNat 64 rem + -BitVec.ofNat 64 w =
      base + BitVec.ofNat 64 (2 * (done + rem) - w) := by
  rw [← BitVec.sub_eq_add_neg]
  have hadd : base + BitVec.ofNat 64 (2 * done) + 2#64 * BitVec.ofNat 64 rem =
      base + BitVec.ofNat 64 (2 * (done + rem)) := by
    rw [BitVec.add_assoc]
    congr 1
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1; omega
  rw [hadd]
  exact add_ofNat_sub_ofNat hw (by omega)

theorem neg_disp_sub0 {base : BitVec 64} {n w : Nat} (hw : w ≤ 2 * n) (hle : n < 2 ^ 32) :
    base + 2#64 * BitVec.ofNat 64 n + -BitVec.ofNat 64 w = base + BitVec.ofNat 64 (2 * n - w) := by
  have h := neg_disp_sub (base := base) (done := 0) (rem := n) (w := w) (by omega) (by omega)
  simpa [Nat.zero_add, BitVec.add_zero] using h

theorem neg_disp_sub_c {base : BitVec 64} {b done rem w : Nat}
    (hw : w ≤ done + rem) (hle : b + done + rem < 2 ^ 32) :
    base + 16#64 + BitVec.ofNat 64 (b + done) + BitVec.ofNat 64 rem + -BitVec.ofNat 64 w =
      base + 16#64 + BitVec.ofNat 64 (b + (done + rem - w)) := by
  rw [← BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrew : b + (done + rem - w) = (b + done + rem) - w := by omega
  rw [hrew]
  exact add_ofNat_sub_ofNat (by omega) (by omega)

theorem neg_disp_sub_c0 {base : BitVec 64} {b n w : Nat} (hw : w ≤ n) (hle : b + n < 2 ^ 32) :
    base + 16#64 + BitVec.ofNat 64 b + BitVec.ofNat 64 n + -BitVec.ofNat 64 w =
      base + 16#64 + BitVec.ofNat 64 (b + (n - w)) := by
  have h := neg_disp_sub_c (base := base) (b := b) (done := 0) (rem := n) (w := w)
    (by omega) (by omega)
  simpa [Nat.add_zero, Nat.zero_add] using h

theorem neg_disp_sub_u {base : BitVec 64} {b done rem w : Nat}
    (hw : w ≤ 2 * (done + rem)) (hle : b + done + rem < 2 ^ 32) :
    base + 16#64 + BitVec.ofNat 64 (2 * (b + done)) + 2#64 * BitVec.ofNat 64 rem +
        -BitVec.ofNat 64 w =
      base + 16#64 + BitVec.ofNat 64 (2 * (b + done + rem) - w) := by
  rw [← BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have h1 : BitVec.ofNat 64 (2 * (b + done)) + 2#64 * BitVec.ofNat 64 rem =
      BitVec.ofNat 64 (2 * (b + done + rem)) := by
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1; omega
  rw [h1]
  exact add_ofNat_sub_ofNat (by omega) (by omega)

/-! ## Slice, agreement, and separation memory wrappers -/

theorem drop_take1_eq {xs : List UInt8} {idx : Nat} (h : idx < xs.length) :
    (xs.drop idx).take 1 = [xs[idx]'h] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi1 _
    simp only [List.length_take, List.length_drop] at hi1
    rcases (show i = 0 by omega) with rfl
    simp [List.getElem_take, List.getElem_drop]

theorem expBytes_slice_getElem {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    {b e off len : Nat} (hb_le : b ≤ e) (he_le : e ≤ (c >>> 1).toNat)
    (hlen : off + len ≤ e - b) (i : Nat) (hi : i < 2 * len) :
    (expBytes ((d.drop (b + off)).take len))[i]'(by
        rw [expBytes_length, List.length_take, List.length_drop, hl, strByteLen_compressed hc]; omega) =
      (getCharsBytes c d b e)[2 * off + i]'(by
        rw [getCharsBytes_length c d hb_le he_le]; omega) := by
  have hsub_len : ((d.drop (b + off)).take len).length = len := by
    rw [List.length_take, List.length_drop, hl, strByteLen_compressed hc]; omega
  rw [expBytes_getElem _ i (by rw [hsub_len]; exact hi),
    getCharsBytes_compressed_getElem hc hl hb_le he_le (2 * off + i) (by omega)]
  have hmod : (2 * off + i) % 2 = i % 2 := by omega
  have hdiv : b + (2 * off + i) / 2 = b + off + i / 2 := by omega
  simp only [hmod, hdiv]
  split
  · simp [List.getElem_take, List.getElem_drop, Nat.add_assoc]
  · rfl

theorem pair_byte_zero_getElem {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    {b e k : Nat} (hb_le : b ≤ e) (he_le : e ≤ (c >>> 1).toNat)
    (hk : k < e - b) (i : Nat) (hi : i < 2) :
    ([d[b + k]'(by rw [hl, strByteLen_compressed hc]; omega), (0 : UInt8)])[i]'(by simp; omega) =
      (getCharsBytes c d b e)[2 * k + i]'(by
        rw [getCharsBytes_length c d hb_le he_le]; omega) := by
  rw [getCharsBytes_compressed_getElem hc hl hb_le he_le (2 * k + i) (by omega)]
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  · simp

theorem uncomp_slice_getElem {c : BitVec 32} {d : List UInt8}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    {b e off len : Nat} (hb_le : b ≤ e) (he_le : e ≤ (c >>> 1).toNat)
    (hlen : off + len ≤ 2 * (e - b)) (i : Nat) (hi : i < len) :
    ((d.drop (2 * b + off)).take len)[i]'(by
        rw [List.length_take, List.length_drop, hl, strByteLen_uncompressed hc]; omega) =
      (getCharsBytes c d b e)[off + i]'(by
        rw [getCharsBytes_length c d hb_le he_le]; omega) := by
  simpa [List.getElem_take, List.getElem_drop, Nat.add_assoc] using
    (getCharsBytes_uncompressed_getElem hc hl hb_le he_le (off + i) (by omega)).symm

theorem add_ofNat_eq_add {base : BitVec 64} (x y : Nat) :
    base + BitVec.ofNat 64 x + BitVec.ofNat 64 y = base + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sw32_ze64 (x : BitVec 32) :
    (x.zeroExtend 64).setWidth 32 = x := by bv_decide

theorem sw32_sw64 (x : BitVec 32) :
    (BitVec.setWidth 64 x).setWidth 32 = x := by bv_decide

theorem bitvec32_sub64_add64_ze32 (n : Nat) :
    ((BitVec.ofNat 32 n - 64#32).zeroExtend 64).setWidth 32 + 64#32 = BitVec.ofNat 32 n := by
  rw [sw32_ze64]
  exact sub64_add64_ofNat32 n

theorem setWidth32_ofNat64 (m : Nat) (hm : m < 2 ^ 32) :
    (BitVec.ofNat 64 m).setWidth 32 = BitVec.ofNat 32 m := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hm]

theorem nat_2e_lt64 {c : BitVec 32} {e : Nat} (he : e ≤ (c >>> 1).toNat) :
    2 * e < 2 ^ 32 := by
  have hc : (c >>> 1).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := c.isLt; omega
  omega

theorem load_count_at (t : MachineData) {A : BitVec 64} {c : BitVec 32}
    {d old : List UInt8} {dstAddr : BitVec 64} {R : DataMem → Prop}
    (hmem : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) t.dmem)
    (ret : Width.W32.type → MachineData → Effects) :
    t.load (A + 8#64) .W32 ret =
      require_access require_read_access (A + 8#64) (UInt64.ofNat Width.W32.bytes)
        (fun _ => ret (.ofInt 32 (Int.ofBytes (Int.toBytes 4 c.toInt))) t) := by
  unfold StringAt at hmem
  rw [sep_assoc, sep_assoc] at hmem
  exact load_sep t (A + 8#64) .W32 ret (Int.toBytes 4 c.toInt) _ hmem
    (Int.toBytes_length 4 c.toInt)

theorem load_src_at {s₀ t : MachineData} {A dstAddr addr : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {R : Mem 64 → Prop} (w : Width)
    (ret : w.type → MachineData → Effects) {off : Nat}
    (hmem0 : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hl : d.length = strByteLen c) (hold : old.length = buf.length)
    (hbuf_lt : buf.length < 2 ^ 64)
    (hdmem : t.dmem = s₀.dmem.storeBytes dstAddr buf)
    (haddr : addr = A + 16#64 + BitVec.ofNat 64 off)
    (hle : off + w.bytes ≤ d.length) :
    t.load addr w ret =
      require_access require_read_access addr (UInt64.ofNat w.bytes)
        (fun _ => ret (BitVec.ofInt w.bits (Int.ofBytes ((d.drop off).take w.bytes))) t) := by
  obtain ⟨Rs, hRs⟩ := mem_expose_src_slice hmem0 hl hold hbuf_lt hle
  rw [← haddr, ← hdmem] at hRs
  exact load_sep t addr w ret _ Rs hRs
    (by rw [List.length_take, List.length_drop]; exact Nat.min_eq_left (by omega))

theorem loadAvx_src_at {s₀ t : MachineData} {A dstAddr addr : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {R : Mem 64 → Prop} (w : AvxWidth)
    (ret : w.type → MachineData → Effects) {off : Nat}
    (hmem0 : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hl : d.length = strByteLen c) (hold : old.length = buf.length)
    (hbuf_lt : buf.length < 2 ^ 64)
    (hdmem : t.dmem = s₀.dmem.storeBytes dstAddr buf)
    (haddr : addr = A + 16#64 + BitVec.ofNat 64 off)
    (hle : off + w.bytes ≤ d.length) :
    t.loadAvx addr w ret =
      require_access require_read_access addr (UInt64.ofNat w.bytes)
        (fun _ => ret (BitVec.ofInt w.bits (Int.ofBytes ((d.drop off).take w.bytes))) t) := by
  obtain ⟨Rs, hRs⟩ := mem_expose_src_slice hmem0 hl hold hbuf_lt hle
  rw [← haddr, ← hdmem] at hRs
  exact loadAvx_sep t addr w ret _ Rs hRs
    (by rw [List.length_take, List.length_drop]; exact Nat.min_eq_left (by omega))

theorem store_dst_at {s₀ t : MachineData} {A dstAddr addr : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {R : Mem 64 → Prop} {w : Width} (v : w.type)
    (ret : MachineData → Effects) {off : Nat}
    (hmem0 : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hold : old.length = buf.length) (hbuf_bound : buf.length ≤ 2 ^ 64)
    (hdmem : t.dmem = s₀.dmem.storeBytes dstAddr buf)
    (haddr : addr = dstAddr + BitVec.ofNat 64 off)
    (hle : off + w.bytes ≤ buf.length) :
    t.store addr v ret =
      require_access require_write_access addr (UInt64.ofNat w.bytes) (fun _ =>
        ret { t with
          dmem := s₀.dmem.storeBytes dstAddr
            (bufReplace buf off w.bytes (Int.toBytes w.bytes v.toInt)) }) := by
  obtain ⟨Rd, hRd⟩ := mem_expose_dst_slice hmem0 hold hbuf_bound hle
  rw [← haddr, ← hdmem] at hRd
  have hlen : ((buf.drop off).take w.bytes).length = w.bytes := by
    rw [List.length_take, List.length_drop]; exact Nat.min_eq_left (by omega)
  have hs := store_sep t addr w v ret _ Rd hRd hlen
  dsimp only at hs
  have hdmem_eq : t.dmem.storeInt addr w.bytes v.toInt =
      s₀.dmem.storeBytes dstAddr (bufReplace buf off w.bytes (Int.toBytes w.bytes v.toInt)) := by
    rw [hdmem, haddr, storeInt_bufReplace hle hbuf_bound]
  rw [hdmem_eq] at hs
  exact hs

theorem storeAvx_dst_at {s₀ t : MachineData} {A dstAddr addr : BitVec 64} {c : BitVec 32}
    {d buf old : List UInt8} {R : Mem 64 → Prop} {w : AvxWidth} (v : w.type)
    (ret : MachineData → Effects) {off : Nat}
    (hmem0 : (StringAt A c d ⋆ Eq (old.At dstAddr) ⋆ R) s₀.dmem)
    (hold : old.length = buf.length) (hbuf_bound : buf.length ≤ 2 ^ 64)
    (hdmem : t.dmem = s₀.dmem.storeBytes dstAddr buf)
    (haddr : addr = dstAddr + BitVec.ofNat 64 off)
    (hle : off + w.bytes ≤ buf.length) :
    t.storeAvx addr v ret =
      require_access require_write_access addr (UInt64.ofNat w.bytes) (fun _ =>
        ret { t with
          dmem := s₀.dmem.storeBytes dstAddr
            (bufReplace buf off w.bytes (Int.toBytes w.bytes v.toInt)) }) := by
  obtain ⟨Rd, hRd⟩ := mem_expose_dst_slice hmem0 hold hbuf_bound hle
  rw [← haddr, ← hdmem] at hRd
  have hlen : ((buf.drop off).take w.bytes).length = w.bytes := by
    rw [List.length_take, List.length_drop]; exact Nat.min_eq_left (by omega)
  have hs := storeAvx_sep t addr w v ret _ Rd hRd hlen
  dsimp only at hs
  have hdmem_eq : t.dmem.storeInt addr w.bytes v.toInt =
      s₀.dmem.storeBytes dstAddr (bufReplace buf off w.bytes (Int.toBytes w.bytes v.toInt)) := by
    rw [hdmem, haddr, storeInt_bufReplace hle hbuf_bound]
  rw [hdmem_eq] at hs
  exact hs

structure AgreeTo (c : BitVec 32) (d : List UInt8) (b e W : Nat)
    (hb_le : b ≤ e) (he_le : e ≤ (c >>> 1).toNat) (buf : List UInt8) : Prop where
  len : buf.length = 2 * (e - b)
  bound : W ≤ 2 * (e - b)
  agree : ∀ j (hj : j < W),
    buf[j]'(by have := len; have := bound; omega) =
      (getCharsBytes c d b e)[j]'(by rw [getCharsBytes_length c d hb_le he_le]; have := bound; omega)

theorem agreeTo_bufReplace {c : BitVec 32} {d buf chunk : List UInt8}
    {b e W off len : Nat} {hb_le : b ≤ e} {he_le : e ≤ (c >>> 1).toNat}
    (hag : AgreeTo c d b e W hb_le he_le buf)
    (hoff_W : off ≤ W) (hle : off + len ≤ 2 * (e - b))
    (hlen : chunk.length = len)
    (hchunk : ∀ i (hi : i < len), chunk[i]'(by omega) =
      (getCharsBytes c d b e)[off + i]'(by rw [getCharsBytes_length c d hb_le he_le]; omega)) :
    AgreeTo c d b e (max W (off + len)) hb_le he_le (bufReplace buf off len chunk) := by
  have htar := getCharsBytes_length c d hb_le he_le
  have hres := bufReplace_extend_to hag.len htar hoff_W hle hag.bound hag.agree hlen hchunk
  exact ⟨hres.1, Nat.max_le.mpr ⟨hag.bound, hle⟩, hres.2⟩

theorem agreeTo_eq_target {c : BitVec 32} {d buf : List UInt8}
    {b e W : Nat} {hb_le : b ≤ e} {he_le : e ≤ (c >>> 1).toNat}
    (hag : AgreeTo c d b e W hb_le he_le buf) (hge : 2 * (e - b) ≤ W) :
    buf = getCharsBytes c d b e :=
  list_eq_of_pointwise hag.len (getCharsBytes_length c d hb_le he_le)
    (fun j hj => hag.agree j (Nat.lt_of_lt_of_le hj hge))

def AvxFrame (src dst_ptr cnt tmp : Reg64) (ymm0 ymm1 : AvxReg .W256) (s₀ t : MachineData) : Prop :=
  (∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r) ∧
  ZmmsFrame ymm0 ymm1 s₀ t.zmms

theorem avxFrame_setReg {src dst_ptr cnt tmp r : Reg64} {ymm0 ymm1 : AvxReg .W256}
    {s₀ t : MachineData} (h : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hr : r ∈ [src, dst_ptr, cnt, tmp]) (v : BitVec 64) :
    AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ { t with regs := t.regs.set64 r v } := by
  refine ⟨fun rx hrx => ?_, h.2⟩
  have hne : rx ≠ r := fun heq => hrx (heq ▸ hr)
  simp [get64_set64, hne, h.1 rx hrx]

theorem avxFrame_setYmm0 {src dst_ptr cnt tmp : Reg64} {ymm0 ymm1 : AvxReg .W256}
    {s₀ t : MachineData} (h : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t) (v : BitVec 256) :
    AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ (t.setAvxReg ymm0 v) :=
  ⟨h.1, zmmsFrame_set_ymm0 h.2 v⟩

theorem avxFrame_setYmm1 {src dst_ptr cnt tmp : Reg64} {ymm0 ymm1 : AvxReg .W256}
    {s₀ t : MachineData} (h : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t) (v : BitVec 256) :
    AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ (t.setAvxReg ymm1 v) :=
  ⟨h.1, zmmsFrame_set_ymm1 h.2 v⟩

theorem avxFrame_setXmm0 {src dst_ptr cnt tmp : Reg64} {ymm0 ymm1 : AvxReg .W256}
    {s₀ t : MachineData} (h : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t) (v : BitVec 128) :
    AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ (t.setAvxReg (.xmm ymm0.base) v) :=
  ⟨h.1, zmmsFrame_set_xmm0 h.2 v⟩

theorem avxFrame_setDmem {src dst_ptr cnt tmp : Reg64} {ymm0 ymm1 : AvxReg .W256}
    {s₀ t : MachineData} (h : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t) (m : DataMem) :
    AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ { t with dmem := m } := h

macro "sstep" : tactic => `(tactic| (
  refine Program.loop_of_interp rfl ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, AvxOperation.interp,
    Operand.interp, AvxOperand.interp, RegOrMem.interp, AvxRegOrMem.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.set, MachineData.setReg, MachineData.setAvx,
    MachineData.setAvxReg, Effects.All, addr_base_disp, addr_sib1_disp, addr_sib2_disp,
    addr_base_disp', addr_sib1_disp', addr_sib2_disp', get_low32, get_low64, set_low32,
    set_low64, get64_set64, CondCode.interp, StatusFlags.from_result, Nat.add_assoc,
    Nat.reduceAdd, Nat.reduceBEq, Nat.reduceLT, Int64.toBitVec_ofNat,
    Int64.toBitVec_ofNat_grind, Int64.toBitVec_neg, BitVec.truncate, Width.bits,
    AvxWidth.bits, Width.bytes, AvxWidth.bytes, BitVec.ofNat_eq_ofNat,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take, sw32_64, sw32_ofNat,
    zmms_get_set, zmms_set_set, zmms_get_set_xmm, zmms_set_set_xmm, cnt1, Bool.false_eq_true,
    Bool.and_false, Bool.not_false, Bool.not_true, Bool.false_and, BitVec.zero_eq,
    BitVec.setWidth_eq, ↓reduceIte]))

macro "cont" : tactic =>
  `(tactic| refine Program.loopCont_of_le (by rw [stringGetCharsBody_length]; omega) ?_)

theorem neg_disp_sub_u0 {base : BitVec 64} {b n w : Nat}
    (hw : w ≤ 2 * n) (hle : b + n < 2 ^ 32) :
    base + 16#64 + BitVec.ofNat 64 (2 * b) + 2#64 * BitVec.ofNat 64 n + -BitVec.ofNat 64 w =
      base + 16#64 + BitVec.ofNat 64 (2 * (b + n) - w) := by
  have h := neg_disp_sub_u (base := base) (b := b) (done := 0) (rem := n) (w := w)
    (by omega) (by omega)
  simpa [Nat.add_zero] using h

theorem get16_set64_ofInt16_ze32_ze64 (regs : Reg64s) (r : Reg64) (bs : List UInt8) :
    ((regs.set64 r (((BitVec.ofInt 16 (Int.ofBytes bs)).zeroExtend 32).zeroExtend 64)).get
      (.low r .W16)) = BitVec.ofInt 16 (Int.ofBytes bs) := by
  dsimp only [Reg64s.get, Reg.base, Reg.offset, Width.bits]
  rw [get64_set64]
  simp only [↓reduceIte, BitVec.drop, BitVec.take]
  bv_decide

section Branches

variable [Host]
  {obj : Reg64} {srcBegin : RegOrImm} {srcEnd dst : Reg64} {dstBegin : RegOrImm}
  {src dst_ptr cnt tmp : Reg64} {ymm0 ymm1 : AvxReg .W256}

theorem done_at
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (c : BitVec 32) (d : List UInt8) (s₀ t : MachineData)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms ∨ ∃ vs, t.zmms = (s₀.zmms.setAll [ymm0, ymm1] vs).zeroUpper)
    (hmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs)
      (getCharsBytes c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 197)⟩ := by
  sstep; cont
  exact Program.loop_done ⟨hmem, hregs, hz⟩

theorem done_vzero_at
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (c : BitVec 32) (d : List UInt8) (s₀ t : MachineData)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs)
      (getCharsBytes c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 195)⟩ := by
  sstep; cont
  sstep; cont
  exact done_at H c d s₀ _ hf.1 (Or.inr (zmmsFrame_zeroUpper ymm0 ymm1 hy0 hy1 hy01 hf.2)) hmem

theorem compressed_le32_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (_hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 16 ≤ rem) (hrem_hi : rem ≤ 32) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + done))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 8)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  -- 8: label `compressed_le32`
  sstep; cont
  -- 9: `vpmovzxbw 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + done) := by
    rw [BitVec.add_zero]; exact hsrc
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 10: `vpmovzxbw -16(%src, %cnt, 1), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + t.regs.get64 cnt + -16#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + rem - 16)) := by
    rw [hsrc, hcnt]
    exact neg_disp_sub_c (by omega) (by omega)
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 11: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 (expBytes ((d.drop (b + done)).take 16))
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 12: `vmovdqu %ymm1, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * n - 32) 32 (expBytes ((d.drop (b + (done + rem - 16))).take 16))
  have hrew : b + (done + rem - 16) = b + (n - 16) := by omega
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * n - 32 + 32)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [hrew, show 2 * n - 32 = 2 * (n - 16) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
  cont
  -- 13: `jmp done_vzero`
  sstep
  simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
  rw [Int64.add_comm, Int64.sub_add_cancel]
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _⟩
    (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])

theorem compressed_tail_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hdone_lo : 16 ≤ done) (hrem_lo : 1 ≤ rem) (hrem_hi : rem ≤ 16) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + done))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 60)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  -- 60: label `compressed_tail`
  sstep; cont
  -- 61: `vpmovzxbw -16(%src, %cnt, 1), %ymm0`
  sstep
  have haddr : t.regs.get64 src + t.regs.get64 cnt + -16#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + rem - 16)) := by
    rw [hsrc, hcnt]
    exact neg_disp_sub_c (by omega) (by omega)
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 62: `vmovdqu %ymm0, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * n - 32) 32 (expBytes ((d.drop (b + (done + rem - 16))).take 16))
  have hrew : b + (done + rem - 16) = b + (n - 16) := by omega
  have hag1 : AgreeTo c d b e (max W (2 * n - 32 + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace (len := 32) hag (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [hrew, show 2 * n - 32 = 2 * (n - 16) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf1_eq : buf1 = getCharsBytes c d b e := agreeTo_eq_target hag1 (by omega)
  cont
  -- 63: `jmp done_vzero`
  sstep
  simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
  rw [Int64.add_comm, Int64.sub_add_cancel]
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm0 hf.2 _⟩
    (by change s₀.dmem.storeBytes dstAddr buf1 = _; rw [hbuf1_eq])

theorem compressed_lt64_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 32 < rem) (hrem_hi : rem ≤ 64) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + done))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 50)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  -- 50: label `compressed_lt64`
  sstep; cont
  -- 51: `vpmovzxbw 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + done) := by
    rw [BitVec.add_zero]; exact hsrc
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 52: `vpmovzxbw 16(%src), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + 16#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 16)) := by
    rw [hsrc, add_ofNat_eq_add, Nat.add_assoc]
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 53: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 (expBytes ((d.drop (b + done)).take 16))
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 54: `vmovdqu %ymm1, 32(%dst_ptr)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 32#64 = dstAddr + BitVec.ofNat 64 (2 * done + 32) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * done + 32) 32 (expBytes ((d.drop (b + (done + 16))).take 16))
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * done + 64)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [show 2 * done + 32 = 2 * (done + 16) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 55: `vpmovzxbw -32(%src, %cnt, 1), %ymm0`
  sstep
  have haddr2 : t.regs.get64 src + t.regs.get64 cnt + -32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + rem - 32)) := by
    rw [hsrc, hcnt]
    exact neg_disp_sub_c (by omega) (by omega)
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr2 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 56: `vpmovzxbw -16(%src, %cnt, 1), %ymm1`
  sstep
  have haddr3 : t.regs.get64 src + t.regs.get64 cnt + -16#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + rem - 16)) := by
    rw [hsrc, hcnt]
    exact neg_disp_sub_c (by omega) (by omega)
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr3 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 57: `vmovdqu %ymm0, -64(%dst_ptr, %cnt, 2)`
  sstep
  have hdst2 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -64#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 64) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) hdst2 (by dsimp [AvxWidth.bytes]; rw [hag2.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf3 := bufReplace buf2 (2 * n - 64) 32 (expBytes ((d.drop (b + (done + rem - 32))).take 16))
  have hrew2 : b + (done + rem - 32) = b + (n - 32) := by omega
  have hag3 : AgreeTo c d b e
      (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * n - 64 + 32)) hb_le he_le buf3 :=
    agreeTo_bufReplace (len := 32) hag2 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [hrew2, show 2 * n - 64 = 2 * (n - 32) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 58: `vmovdqu %ymm1, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst3 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag3.len.symm) (by rw [hag3.len]; omega)
    (by rfl) hdst3 (by dsimp [AvxWidth.bytes]; rw [hag3.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf4 := bufReplace buf3 (2 * n - 32) 32 (expBytes ((d.drop (b + (done + rem - 16))).take 16))
  have hrew3 : b + (done + rem - 16) = b + (n - 16) := by omega
  have hag4 : AgreeTo c d b e
      (max (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * n - 64 + 32)) (2 * n - 32 + 32))
      hb_le he_le buf4 :=
    agreeTo_bufReplace (len := 32) hag3 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [hrew3, show 2 * n - 32 = 2 * (n - 16) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf4_eq : buf4 = getCharsBytes c d b e := agreeTo_eq_target hag4 (by omega)
  cont
  -- 59: `jmp done_vzero`
  sstep
  simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
  rw [Int64.add_comm, Int64.sub_add_cancel]
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
    (by change s₀.dmem.storeBytes dstAddr buf4 = _; rw [hbuf4_eq])

theorem compressed_avx4_loop_ind
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem_sub W : Nat) (buf : List UInt8) (t : MachineData)
    (hdone_rem : done + 64 + rem_sub = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + done))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem_sub) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 31)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have h_src_dst : src ≠ dst_ptr := fun h => hnd1.1 (by simp [h])
  have h_src_cnt : src ≠ cnt := fun h => hnd1.1 (by simp [h])
  have h_dst_src : dst_ptr ≠ src := h_src_dst.symm
  have h_dst_cnt : dst_ptr ≠ cnt := fun h => hnd2.1 (by simp [h])
  have h_cnt_src : cnt ≠ src := h_src_cnt.symm
  have h_cnt_dst : cnt ≠ dst_ptr := h_dst_cnt.symm
  -- 31: label `compressed_avx4_loop`
  sstep; cont
  -- 32: `vpmovzxbw 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + done) := by
    rw [BitVec.add_zero]; exact hsrc
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 33: `vpmovzxbw 16(%src), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + 16#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 16)) := by
    rw [hsrc, add_ofNat_eq_add, Nat.add_assoc]
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 34: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 (expBytes ((d.drop (b + done)).take 16))
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 35: `vmovdqu %ymm1, 32(%dst_ptr)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 32#64 = dstAddr + BitVec.ofNat 64 (2 * done + 32) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * done + 32) 32 (expBytes ((d.drop (b + (done + 16))).take 16))
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * done + 64)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [show 2 * done + 32 = 2 * (done + 16) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 36: `vpmovzxbw 32(%src), %ymm0`
  sstep
  have haddr2 : t.regs.get64 src + 32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 32)) := by
    rw [hsrc, add_ofNat_eq_add, Nat.add_assoc]
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr2 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 37: `vpmovzxbw 48(%src), %ymm1`
  sstep
  have haddr3 : t.regs.get64 src + 48#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 48)) := by
    rw [hsrc, add_ofNat_eq_add, Nat.add_assoc]
  rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr3 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 38: `vmovdqu %ymm0, 64(%dst_ptr)`
  sstep
  have hdst2 : t.regs.get64 dst_ptr + 64#64 = dstAddr + BitVec.ofNat 64 (2 * done + 64) := by
    rw [hdst, add_ofNat_eq_add]
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) hdst2 (by dsimp [AvxWidth.bytes]; rw [hag2.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf3 := bufReplace buf2 (2 * done + 64) 32 (expBytes ((d.drop (b + (done + 32))).take 16))
  have hag3 : AgreeTo c d b e
      (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * done + 96)) hb_le he_le buf3 :=
    agreeTo_bufReplace (len := 32) hag2 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [show 2 * done + 64 = 2 * (done + 32) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 39: `vmovdqu %ymm1, 96(%dst_ptr)`
  sstep
  have hdst3 : t.regs.get64 dst_ptr + 96#64 = dstAddr + BitVec.ofNat 64 (2 * done + 96) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag3.len.symm) (by rw [hag3.len]; omega)
    (by rfl) hdst3 (by dsimp [AvxWidth.bytes]; rw [hag3.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf4 := bufReplace buf3 (2 * done + 96) 32 (expBytes ((d.drop (b + (done + 48))).take 16))
  let W4 := max (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * done + 96)) (2 * done + 128)
  have hag4 : AgreeTo c d b e W4 hb_le he_le buf4 :=
    agreeTo_bufReplace (len := 32) hag3 (by omega) (by omega)
      (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
      (fun i hi => by
        simp only [show 2 * done + 96 = 2 * (done + 48) by omega]
        exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 40: `addq $64, %src64`
  sstep; cont
  -- 41: `addq $128, %dst_ptr64`
  sstep
  simp only [h_dst_src, ↓reduceIte]
  cont
  -- 42: `subl $64, %cnt32`
  sstep
  simp only [h_cnt_src, h_cnt_dst, ↓reduceIte, hcnt]
  have hcnt32 : (BitVec.ofNat 64 rem_sub).setWidth 32 = BitVec.ofNat 32 rem_sub := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : rem_sub < 2 ^ 32)]
  rw [hcnt32]
  have hcf_sub : ((BitVec.ofNat 32 rem_sub - 64#32).unsigned !=
      (BitVec.ofNat 32 rem_sub).unsigned - (64#32).unsigned) = decide (rem_sub < 64) :=
    bitvec32_toNat_lt_iff_cf rem_sub 64 (by omega) (by decide)
  cont
  -- 43: `jae compressed_avx4_loop`
  sstep
  rw [hcf_sub]
  have hsrc_next : t.regs.get64 src + 64#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 64)) := by
    rw [hsrc, add_ofNat_eq_add, Nat.add_assoc]
  have hdst_next : t.regs.get64 dst_ptr + 128#64 =
      dstAddr + BitVec.ofNat 64 (2 * (done + 64)) := by
    rw [hdst, add_ofNat_eq_add]; congr 2
  by_cases hrem_ge : 64 ≤ rem_sub
  · have hcf_f : decide (rem_sub < 64) = false := decide_eq_false (by omega)
    simp only [hcf_f, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 31) rfl]
    cont
    refine compressed_avx4_loop_ind hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
      (done + 64) (rem_sub - 64) W4 buf4 _ (by omega) (by omega) hag4
      ⟨fun r hr => by
        simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
          show r ≠ dst_ptr from fun h => hr (by simp [h]),
          show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
        exact hf.1 r hr,
        zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
      rfl ?_ ?_ ?_
    · simp only [get64_set64, h_src_cnt, h_src_dst, ↓reduceIte]; rw [BitVec.add_comm]; exact hsrc_next
    · simp only [get64_set64, h_dst_cnt, ↓reduceIte]; rw [BitVec.add_comm]; exact hdst_next
    · simp only [get64_set64, ↓reduceIte]
      exact bitvec32_sub_ze64 rem_sub 64 hrem_ge (by omega)
  · have hrem_lt : rem_sub < 64 := by omega
    have hcf_t : decide (rem_sub < 64) = true := decide_eq_true hrem_lt
    simp only [hcf_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 44: `addl $64, %cnt32`
    sstep
    simp only [BitVec.add_comm 64#32, sub64_add64_ofNat32 rem_sub]
    have hcnt_after : (BitVec.ofNat 32 rem_sub).zeroExtend 64 = BitVec.ofNat 64 rem_sub :=
      bitvec32_ofNat_ze64 rem_sub (by omega)
    cont
    -- 45: `je done_vzero`
    sstep
    have hzf0 : (BitVec.ofNat 32 rem_sub == 0#32) = (rem_sub == 0) :=
      ofNat32_eq_zero (by omega)
    rw [hzf0]
    by_cases hrem0 : rem_sub = 0
    · subst hrem0
      simp only [beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 195) rfl]
      cont
      have hbuf4_eq : buf4 = getCharsBytes c d b e := agreeTo_eq_target hag4 (by omega)
      exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
        ⟨fun r hr => by
          simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
            show r ≠ dst_ptr from fun h => hr (by simp [h]),
            show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
          exact hf.1 r hr,
          zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
        (by change s₀.dmem.storeBytes dstAddr buf4 = _; rw [hbuf4_eq])
    · have hbeq_f : (rem_sub == 0) = false := beq_false_of_ne hrem0
      simp only [hbeq_f, Bool.false_eq_true, ↓reduceIte]
      cont
      have hsrc_exit :
          (((((t.regs.set64 src (64#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 src) =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (done + 64)) := by
        simp only [get64_set64, h_src_cnt, h_src_dst, ↓reduceIte]
        rw [BitVec.add_comm]; exact hsrc_next
      have hdst_exit :
          (((((t.regs.set64 src (64#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 dst_ptr) =
          dstAddr + BitVec.ofNat 64 (2 * (done + 64)) := by
        simp only [get64_set64, h_dst_cnt, ↓reduceIte]
        rw [BitVec.add_comm]; exact hdst_next
      have hcnt_exit :
          (((((t.regs.set64 src (64#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 cnt) =
          BitVec.ofNat 64 rem_sub := by
        simp only [get64_set64, ↓reduceIte]
        exact bitvec32_ofNat_ze64 rem_sub (by omega)
      -- 46: `cmpl $16, %cnt32`
      sstep
      cont
      -- 47: `jbe compressed_tail`
      sstep
      rw [jbe_ofNat32 (by omega) (by decide)]
      by_cases h16 : rem_sub ≤ 16
      · simp only [decide_eq_true h16, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 60) rfl]
        cont
        exact compressed_tail_at hlab H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
          (done + 64) rem_sub W4 buf4 (by omega) (by omega) (by omega) h16 (by omega) hag4
          ⟨fun r hr => by
            simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
              show r ≠ dst_ptr from fun h => hr (by simp [h]),
              show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr,
            zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
          rfl hsrc_exit hdst_exit hcnt_exit
      · simp only [decide_eq_false h16, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 48: `cmpl $32, %cnt32`
        sstep
        cont
        -- 49: `jbe compressed_le32`
        sstep
        rw [jbe_ofNat32 (by omega) (by decide)]
        by_cases h32 : rem_sub ≤ 32
        · simp only [decide_eq_true h32, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 8) rfl]
          cont
          exact compressed_le32_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            (done + 64) rem_sub W4 buf4 (by omega) (by omega) h32 (by omega) hag4
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
            rfl hsrc_exit hdst_exit hcnt_exit
        · simp only [decide_eq_false h32, Bool.false_eq_true, ↓reduceIte]
          cont
          exact compressed_lt64_at hlab H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
            (done + 64) rem_sub W4 buf4 (by omega) (by omega) (by omega) (by omega) hag4
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
            rfl hsrc_exit hdst_exit hcnt_exit
termination_by rem_sub

theorem compressed_pre_loop_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 64 < rem) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs + done))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 29)⟩ := by
  have he32 : 2 * ((s₀.regs.get64 srcEnd).setWidth 32).toNat < 2 ^ 32 := nat_2e_lt64 he_le
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have h_src_cnt : src ≠ cnt := fun h => hnd1.1 (by simp [h])
  have h_dst_cnt : dst_ptr ≠ cnt := fun h => hnd2.1 (by simp [h])
  -- 29: label `compressed_pre_loop`
  sstep; cont
  -- 30: `subl $64, %cnt32`
  sstep; cont
  refine compressed_avx4_loop_ind hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
    done (rem - 64) W buf _ (by omega) hd_W hag (avxFrame_setReg hf (by simp) _) hdmem ?_ ?_ ?_
  · simp only [get64_set64, h_src_cnt, ↓reduceIte]; exact hsrc
  · simp only [get64_set64, h_dst_cnt, ↓reduceIte]; exact hdst
  · simp only [get64_set64, ↓reduceIte, hcnt, setWidth32_ofNat64 rem (by omega)]
    exact bitvec32_sub_ze64 rem 64 (by omega) (by omega)

theorem compressed_small_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (hn_lt : ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs < 16)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) old)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (srcBegin.toNat s₀.regs))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs)
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 64)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : old.length < 2 ^ 64 := by omega
  have hbuf_bound : old.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  have hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t :=
    ⟨hregs, hz ▸ zmmsFrame_refl ymm0 ymm1 s₀⟩
  have hag0 : AgreeTo c d b e 0 hb_le he_le old :=
    ⟨hold, Nat.zero_le _, fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have h_src_tmp : src ≠ tmp := fun h => hnd1.1 (by simp [h])
  have h_dst_tmp : dst_ptr ≠ tmp := fun h => hnd2.1 (by simp [h])
  have h_cnt_tmp : cnt ≠ tmp := fun h => hnd3.1 (by simp [h])
  have hcnt32 : (t.regs.get64 cnt).setWidth 32 = BitVec.ofNat 32 n := by
    rw [hcnt, setWidth32_ofNat64 n (by omega)]
  -- 64: label `compressed_small`
  sstep; cont
  -- 65: `cmpl $4, %cnt32`
  sstep; rw [hcnt32]; cont
  -- 66: `jb compressed_lt4`
  sstep
  rw [cf_ofNat32 (by omega) (by decide)]
  by_cases hn4 : n < 4
  · simp only [decide_eq_true hn4, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 86) rfl]
    cont
    -- 86: label `compressed_lt4`
    sstep; cont
    -- 87: `cmpl $2, %cnt32`
    sstep; rw [hcnt32]; cont
    -- 88: `jb compressed_1`
    sstep
    rw [cf_ofNat32 (by omega) (by decide)]
    by_cases hn2 : n < 2
    · simp only [decide_eq_true hn2, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 97) rfl]
      cont
      -- 97: label `compressed_1`
      sstep; cont
      -- 98: `testl %cnt32, %cnt32`
      sstep; rw [hcnt32]
      intro _af
      have hself : BitVec.ofNat 32 n &&& BitVec.ofNat 32 n = BitVec.ofNat 32 n := by bv_decide
      rw [hself, ofNat32_eq_zero (by omega)]
      cont
      -- 99: `je done`
      sstep
      by_cases hn0 : n = 0
      · simp only [hn0, beq_self_eq_true, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 197) rfl]
        cont
        have hold_eq : old = getCharsBytes c d b e := agreeTo_eq_target hag0 (by omega)
        exact done_at H c d s₀ _ hregs (Or.inl hz) (by rw [hdmem, hold_eq])
      · have hn1 : n = 1 := by omega
        have hbeq_f : (n == 0) = false := beq_false_of_ne hn0
        simp only [hbeq_f, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 100: `movzbl 0(%src), %tmp32`
        sstep
        have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 0) := by
          rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
        rw [load_src_at .W8 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0 (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_read_access]
        have hdt0 : (d.drop (b + 0)).take 1 = [d[b + 0]'(by omega)] := drop_take1_eq (by omega)
        rw [hdt0]
        cont
        -- 101: `movw %tmp16, 0(%dst_ptr)`
        sstep
        simp only [h_dst_tmp, ↓reduceIte]
        have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
          rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
        rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0 (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_write_access]
        rw [get16_set64_ze32_ze64, loadInt1_ofBytes_toInt]
        let buf1 := bufReplace old 0 2 [d[b + 0]'(by omega), 0]
        have hag1 : AgreeTo c d b e 2 hb_le he_le buf1 := by
          simpa using agreeTo_bufReplace (len := 2) hag0 (Nat.le_refl 0) (by omega) rfl
            (fun i hi => pair_byte_zero_getElem hc hl hb_le he_le (by omega) i hi)
        have hbuf1_eq : buf1 = getCharsBytes c d b e := agreeTo_eq_target hag1 (by omega)
        cont
        -- 102: `jmp done`
        sstep
        simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 197) rfl]
        rw [Int64.add_comm, Int64.sub_add_cancel]
        cont
        exact done_at H c d s₀ _
          (fun r hr => by
            simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr)
          (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf1 = _; rw [hbuf1_eq])
    · have hcf_f : decide (n < 2) = false := decide_eq_false hn2
      simp only [hcf_f, Bool.false_eq_true, ↓reduceIte]
      cont
      -- 89: `movzbl 0(%src), %tmp32`
      sstep
      have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 0) := by
        rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
      rw [load_src_at .W8 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      have hdt0 : (d.drop (b + 0)).take 1 = [d[b + 0]'(by omega)] := drop_take1_eq (by omega)
      rw [hdt0]
      cont
      -- 90: `movw %tmp16, 0(%dst_ptr)`
      sstep
      simp only [h_dst_tmp, ↓reduceIte]
      have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
        rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
      rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_write_access]
      rw [get16_set64_ze32_ze64, loadInt1_ofBytes_toInt]
      let buf1 := bufReplace old 0 2 [d[b + 0]'(by omega), 0]
      have hag1 : AgreeTo c d b e 2 hb_le he_le buf1 := by
        simpa using agreeTo_bufReplace (len := 2) hag0 (Nat.le_refl 0) (by omega) rfl
          (fun i hi => pair_byte_zero_getElem hc hl hb_le he_le (by omega) i hi)
      cont
      -- 91: `movzbl 1(%src), %tmp32`
      sstep
      simp only [h_src_tmp, ↓reduceIte]
      have haddr1 : t.regs.get64 src + 1#64 =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 1) := by
        rw [hsrc, add_ofNat_eq_add]
      rw [load_src_at .W8 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) haddr1 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      have hdt1 : (d.drop (b + 1)).take 1 = [d[b + 1]'(by omega)] := drop_take1_eq (by omega)
      rw [hdt1]
      cont
      -- 92: `movw %tmp16, 2(%dst_ptr)`
      sstep
      simp only [h_dst_tmp, ↓reduceIte]
      have hdst1 : t.regs.get64 dst_ptr + 2#64 = dstAddr + BitVec.ofNat 64 2 := by
        rw [hdst]
      rw [store_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) hdst1 (by dsimp [Width.bytes]; rw [hag1.len]; omega)]
      simp only [Effects.All_require_write_access]
      rw [get16_set64_ze32_ze64, loadInt1_ofBytes_toInt]
      let buf2 := bufReplace buf1 2 2 [d[b + 1]'(by omega), 0]
      have hag2 : AgreeTo c d b e 4 hb_le he_le buf2 := by
        simpa using agreeTo_bufReplace (len := 2) hag1 (by omega) (by omega) rfl
          (fun i hi => pair_byte_zero_getElem hc hl hb_le he_le (by omega) i hi)
      cont
      -- 93: `je done` (flags still from `87: cmpl $2, %cnt32`)
      sstep
      rw [ofNat32_sub_eq_zero (by omega) (by decide)]
      by_cases hn2eq : n = 2
      · simp only [decide_eq_true hn2eq, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 197) rfl]
        cont
        have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
        exact done_at H c d s₀ _
          (fun r hr => by
            simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr)
          (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])
      · have hn3 : n = 3 := by omega
        simp only [decide_eq_false hn2eq, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 94: `movzbl 2(%src), %tmp32`
        sstep
        simp only [h_src_tmp, ↓reduceIte]
        have haddr2 : t.regs.get64 src + 2#64 =
            s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 2) := by
          rw [hsrc, add_ofNat_eq_add]
        rw [load_src_at .W8 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
          (by rfl) haddr2 (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_read_access]
        have hdt2 : (d.drop (b + 2)).take 1 = [d[b + 2]'(by omega)] := drop_take1_eq (by omega)
        rw [hdt2]
        cont
        -- 95: `movw %tmp16, 4(%dst_ptr)`
        sstep
        simp only [h_dst_tmp, ↓reduceIte]
        have hdst2 : t.regs.get64 dst_ptr + 4#64 = dstAddr + BitVec.ofNat 64 4 := by
          rw [hdst]
        rw [store_dst_at _ _ hmem0 (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
          (by rfl) hdst2 (by dsimp [Width.bytes]; rw [hag2.len]; omega)]
        simp only [Effects.All_require_write_access]
        rw [get16_set64_ze32_ze64, loadInt1_ofBytes_toInt]
        let buf3 := bufReplace buf2 4 2 [d[b + 2]'(by omega), 0]
        have hag3 : AgreeTo c d b e 6 hb_le he_le buf3 := by
          simpa using agreeTo_bufReplace (off := 4) (len := 2) hag2 (by omega) (by omega) rfl
            (fun i hi => pair_byte_zero_getElem (k := 2) hc hl hb_le he_le (by omega) i hi)
        have hbuf3_eq : buf3 = getCharsBytes c d b e := agreeTo_eq_target hag3 (by omega)
        cont
        -- 96: `jmp done`
        sstep
        simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 197) rfl]
        rw [Int64.add_comm, Int64.sub_add_cancel]
        cont
        exact done_at H c d s₀ _
          (fun r hr => by
            simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr)
          (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf3 = _; rw [hbuf3_eq])
  · have hcf_f : decide (n < 4) = false := decide_eq_false hn4
    simp only [hcf_f, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 67: `cmpl $8, %cnt32`
    sstep; rw [hcnt32]; cont
    -- 68: `jb compressed_4_7`
    sstep
    rw [cf_ofNat32 (by omega) (by decide)]
    by_cases hn8 : n < 8
    · simp only [decide_eq_true hn8, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 74) rfl]
      cont
      -- 74: label `compressed_4_7`
      sstep; cont
      -- 75: `movl 0(%src), %tmp32`
      sstep
      have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 0) := by
        rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
      rw [load_src_at .W32 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 76: `vmovd %tmp32, %xmm0`
      sstep
      cont
      -- 77: `vpmovzxbw %xmm0, %xmm0`
      sstep; cont
      -- 78: `vmovq %xmm0, %tmp64`
      sstep; cont
      -- 79: `movq %tmp64, 0(%dst_ptr)`
      sstep
      simp only [h_dst_tmp, ↓reduceIte]
      have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
        rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
      rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_pmovzxbw_64_lsb _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf1 := bufReplace old 0 8 (expBytes ((d.drop (b + 0)).take 4))
      have hag1 : AgreeTo c d b e 8 hb_le he_le buf1 := by
        simpa using agreeTo_bufReplace (len := 8) hag0 (Nat.le_refl 0) (by omega)
          (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
          (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
      cont
      -- 80: `movl -4(%src, %cnt, 1), %tmp32`
      sstep
      simp only [h_src_tmp, h_cnt_tmp, ↓reduceIte]
      have haddr1 : t.regs.get64 src + t.regs.get64 cnt + -4#64 =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (n - 4)) := by
        rw [hsrc, hcnt]
        exact neg_disp_sub_c0 (by omega) (by omega)
      rw [load_src_at .W32 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) haddr1 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 81: `vmovd %tmp32, %xmm0`
      sstep
      cont
      -- 82: `vpmovzxbw %xmm0, %xmm0`
      sstep; cont
      -- 83: `vmovq %xmm0, %tmp64`
      sstep; cont
      -- 84: `movq %tmp64, -8(%dst_ptr, %cnt, 2)`
      sstep
      simp only [h_dst_tmp, h_cnt_tmp, ↓reduceIte]
      have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -8#64 =
          dstAddr + BitVec.ofNat 64 (2 * n - 8) := by
        rw [hdst, hcnt]
        exact neg_disp_sub0 (by omega) (by omega)
      rw [store_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) hdst1 (by dsimp [Width.bytes]; rw [hag1.len]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_pmovzxbw_64_lsb _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf2 := bufReplace buf1 (2 * n - 8) 8 (expBytes ((d.drop (b + (n - 4))).take 4))
      have hag2 : AgreeTo c d b e (max 8 (2 * n - 8 + 8)) hb_le he_le buf2 :=
        agreeTo_bufReplace (len := 8) hag1 (by omega) (by omega)
          (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
          (fun i hi => by
            simp only [show 2 * n - 8 = 2 * (n - 4) by omega]
            exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
      have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
      cont
      -- 85: `jmp done_vzero`
      sstep
      simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
      rw [Int64.add_comm, Int64.sub_add_cancel]
      cont
      exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
        ⟨fun r hr => by simp [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), hf.1 r hr],
          zmmsFrame_set_xmm0 hf.2 _⟩
        (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])
    · have hcf_f8 : decide (n < 8) = false := decide_eq_false hn8
      simp only [hcf_f8, Bool.false_eq_true, ↓reduceIte]
      cont
      -- 69: `vpmovzxbw 0(%src), %xmm0` (loads 8 bytes!)
      sstep
      have haddr0 : t.regs.get64 src + 0#64 = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 0) := by
        rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
      rw [load_src_at .W64 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 70: `vmovdqu %xmm0, 0(%dst_ptr)`
      sstep
      have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
        rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
      rw [storeAvx_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0 (by dsimp [AvxWidth.bytes]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_pmovzxbw_128 _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf1 := bufReplace old 0 16 (expBytes ((d.drop (b + 0)).take 8))
      have hag1 : AgreeTo c d b e 16 hb_le he_le buf1 := by
        simpa using agreeTo_bufReplace (len := 16) hag0 (Nat.le_refl 0) (by omega)
          (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
          (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
      cont
      -- 71: `vpmovzxbw -8(%src, %cnt, 1), %xmm0`
      sstep
      have haddr1 : t.regs.get64 src + t.regs.get64 cnt + -8#64 =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + (n - 8)) := by
        rw [hsrc, hcnt]
        exact neg_disp_sub_c0 (by omega) (by omega)
      rw [load_src_at .W64 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) haddr1 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 72: `vmovdqu %xmm0, -16(%dst_ptr, %cnt, 2)`
      sstep
      have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -16#64 =
          dstAddr + BitVec.ofNat 64 (2 * n - 16) := by
        rw [hdst, hcnt]
        exact neg_disp_sub0 (by omega) (by omega)
      rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_pmovzxbw_128 _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf2 := bufReplace buf1 (2 * n - 16) 16 (expBytes ((d.drop (b + (n - 8))).take 8))
      have hag2 : AgreeTo c d b e (max 16 (2 * n - 16 + 16)) hb_le he_le buf2 :=
        agreeTo_bufReplace (len := 16) hag1 (by omega) (by omega)
          (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
          (fun i hi => by
            simp only [show 2 * n - 16 = 2 * (n - 8) by omega]
            exact expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
      have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
      cont
      -- 73: `jmp done_vzero`
      sstep
      simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
      rw [Int64.add_comm, Int64.sub_add_cancel]
      cont
      exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
        ⟨hf.1, zmmsFrame_set_xmm0 hf.2 _⟩
        (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])

theorem compressed_entry_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    (hdisj : ∀ r, r ∈ [obj, srcEnd, dst] ++ srcBegin.regs ++ dstBegin.regs →
      r ∉ [src, dst_ptr, cnt, tmp])
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = false) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hsrc_hi : srcBegin.hi32Zero s₀.regs) (hdst_hi : dstBegin.hi32Zero s₀.regs)
    (hdst_even : (s₀.regs.get64 dst).getLsbD 0 = false)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms) (hdmem : t.dmem = s₀.dmem)
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 2)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hd_len : d.length = (c >>> 1).toNat := hl.trans (strByteLen_compressed hc)
  have he_d : e ≤ d.length := by rw [hd_len]; exact he_le
  have hbuf_lt : old.length < 2 ^ 64 := by omega
  have hbuf_bound : old.length ≤ 2 ^ 64 := by omega
  have hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t :=
    ⟨hregs, hz ▸ zmmsFrame_refl ymm0 ymm1 s₀⟩
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have h_dst_src : dst_ptr ≠ src := fun h => hnd1.1 (by simp [h])
  have h_cnt_src : cnt ≠ src := fun h => hnd1.1 (by simp [h])
  have h_cnt_dst : cnt ≠ dst_ptr := fun h => hnd2.1 (by simp [h])
  have h_tmp_src : tmp ≠ src := fun h => hnd1.1 (by simp [h])
  have h_tmp_dst : tmp ≠ dst_ptr := fun h => hnd2.1 (by simp [h])
  have h_tmp_cnt : tmp ≠ cnt := fun h => hnd3.1 (by simp [h])
  have h_cnt_tmp : cnt ≠ tmp := h_tmp_cnt.symm
  have h_src_tmp : src ≠ tmp := h_tmp_src.symm
  have h_dst_tmp : dst_ptr ≠ tmp := h_tmp_dst.symm
  have h_cnt_tmp : cnt ≠ tmp := h_tmp_cnt.symm
  have h_src_dst : src ≠ dst_ptr := h_dst_src.symm
  have h_src_cnt : src ≠ cnt := h_cnt_src.symm
  have h_dst_cnt : dst_ptr ≠ cnt := h_cnt_dst.symm
  have hdmem_store : t.dmem = s₀.dmem.storeBytes dstAddr old := by
    rw [hdmem]
    have hmem' := hmem0
    rw [sep_comm (StringAt (s₀.regs.get64 obj) c d) (Eq (old.At dstAddr)), sep_assoc] at hmem'
    exact (Mem.storeBytes_eq_of_sep old _ _ s₀.dmem hmem').symm
  have hag0 : AgreeTo c d b e 0 hb_le he_le old :=
    ⟨hold, Nat.zero_le _, fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
  have hobj_eq : t.regs.get64 obj = s₀.regs.get64 obj := hregs obj (hdisj obj (by simp))
  have hdst_eq : t.regs.get64 dst = s₀.regs.get64 dst := hregs dst (hdisj dst (by simp))
  -- 2: `leaq arrayAddr(obj, srcBegin, .W8, 16), %src`
  have hsrc_lea (p : Std.Rco Int64) :
      (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr obj srcBegin .W8 16) t.regs p : BitVec 64) =
        s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b := by
    have hhi_t : srcBegin.hi32Zero t.regs := by
      cases srcBegin with
      | imm _ => trivial
      | reg r => simpa [RegOrImm.hi32Zero, hregs r (hdisj r (by simp [RegOrImm.regs]))] using hsrc_hi
    rw [addr_arrayAddr t.regs obj srcBegin .W8 16 _ hhi_t, hobj_eq]
    have heval : srcBegin.eval64 t.regs = BitVec.ofNat 64 b := by
      cases srcBegin with
      | imm _ => rfl
      | reg r => simp [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, b,
          hregs r (hdisj r (by simp [RegOrImm.regs]))]
    rw [heval]; simp [Width.bytes]
  sstep
  rw [hsrc_lea]
  cont
  -- 3: `leaq arrayAddr(dst, dstBegin, .W16, 12), %dst_ptr`
  have hdst_lea (p : Std.Rco Int64) :
      (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr dst dstBegin .W16 12)
        (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b)) p : BitVec 64) =
        dstAddr := by
    have hhi_t : dstBegin.hi32Zero (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b)) := by
      cases dstBegin with
      | imm _ => trivial
      | reg r =>
        have hr : r ≠ src := fun h => hdisj r (by simp [RegOrImm.regs]) (by simp [h])
        simpa [RegOrImm.hi32Zero, get64_set64, hr, hregs r (hdisj r (by simp [RegOrImm.regs]))] using hdst_hi
    rw [addr_arrayAddr _ dst dstBegin .W16 12 _ hhi_t]
    have hdst_s : (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b)).get64 dst =
        s₀.regs.get64 dst := by
      have hd : dst ≠ src := fun h => hdisj dst (by simp) (by simp [h])
      simp only [get64_set64, hd, ↓reduceIte, hdst_eq]
    have heval : dstBegin.eval64 (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b)) =
        dstBegin.eval64 s₀.regs := by
      cases dstBegin with
      | imm _ => rfl
      | reg r =>
        have hr : r ≠ src := fun h => hdisj r (by simp [RegOrImm.regs]) (by simp [h])
        simp [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, get64_set64, hr,
          hregs r (hdisj r (by simp [RegOrImm.regs]))]
    rw [hdst_s, heval]; rfl
  sstep
  rw [hdst_lea]
  cont
  let regs_lea := (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b)).set64 dst_ptr dstAddr
  have hsrc_after : regs_lea.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b := by
    simp only [regs_lea, get64_set64, h_src_dst, ↓reduceIte]
  have hdst_after : regs_lea.get64 dst_ptr = dstAddr := by
    simp only [regs_lea, get64_set64, ↓reduceIte]
  have hcnt_after : regs_lea.get64 cnt = BitVec.ofNat 64 n := by
    simp only [regs_lea, get64_set64, h_cnt_dst, h_cnt_src, ↓reduceIte]; exact hcnt
  have hcnt32 : (regs_lea.get64 cnt).setWidth 32 = BitVec.ofNat 32 n := by
    rw [hcnt_after, setWidth32_ofNat64 n (by omega)]
  have hf_lea : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀
      { regs := regs_lea, zmms := t.zmms, status := t.status, dmem := t.dmem } :=
    avxFrame_setReg (avxFrame_setReg hf (by simp) _) (by simp) _
  -- 4: `cmpl $16, %cnt32`
  sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
  -- 5: `jb compressed_small`
  sstep
  rw [cf_ofNat32 (by omega) (by decide)]
  by_cases hn16 : n < 16
  · simp only [decide_eq_true hn16, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 64) rfl]
    cont
    exact compressed_small_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0 hn16
      hf_lea.1 hz hdmem_store hsrc_after hdst_after hcnt_after
  · have hcf_16 : decide (n < 16) = false := decide_eq_false hn16
    simp only [hcf_16, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 6: `cmpl $32, %cnt32`
    sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
    -- 7: `ja compressed_gt32`
    sstep
    rw [ja_ofNat32 (by omega) (by decide)]
    by_cases hn32 : n ≤ 32
    · have hja_f : decide (32 < n) = false := decide_eq_false (by omega)
      simp only [hja_f, Bool.false_eq_true, ↓reduceIte]
      cont
      exact compressed_le32_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
        0 n 0 old (Nat.zero_add n) (by omega) hn32 (Nat.le_refl 0) hag0 hf_lea hdmem_store
        (by simpa [Nat.add_zero] using hsrc_after) (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after)
        hcnt_after
    · have hja_t : decide (32 < n) = true := decide_eq_true (by omega)
      simp only [hja_t, ↓reduceIte, addrOf_label hlab (H := H) (i := 14) rfl]
      cont
      -- 14: label `compressed_gt32`
      sstep; cont
      -- 15: `cmpl $64, %cnt32`
      sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
      -- 16: `jbe compressed_lt64`
      sstep
      rw [jbe_ofNat32 (by omega) (by decide)]
      by_cases hn64 : n ≤ 64
      · simp only [decide_eq_true hn64, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 50) rfl]
        cont
        exact compressed_lt64_at hlab H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
          0 n 0 old (Nat.zero_add n) (by omega) hn64 (Nat.le_refl 0) hag0 hf_lea hdmem_store
          (by simpa [Nat.add_zero] using hsrc_after) (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after)
          hcnt_after
      · have hjbe_f : decide (n ≤ 64) = false := decide_eq_false hn64
        simp only [hjbe_f, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 17: `cmpl $192, %cnt32`
        sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
        -- 18: `jb compressed_pre_loop`
        sstep
        rw [cf_ofNat32 (by omega) (by decide)]
        by_cases hn192 : n < 192
        · simp only [decide_eq_true hn192, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 29) rfl]
          cont
          exact compressed_pre_loop_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            0 n 0 old (Nat.zero_add n) (by omega) (Nat.le_refl 0) hag0 hf_lea hdmem_store
            (by simpa [Nat.add_zero] using hsrc_after)
            (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after) hcnt_after
        · have hcf_f192 : decide (n < 192) = false := decide_eq_false hn192
          simp only [hcf_f192, Bool.false_eq_true, ↓reduceIte]
          cont
          -- 19: `vpmovzxbw 0(%src), %ymm0`
          sstep
          simp only [h_src_dst, ↓reduceIte]
          have haddr0 : (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 b) + 0#64 =
              s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (b + 0) := by
            rw [BitVec.add_zero, Nat.add_zero]
          rw [loadAvx_src_at .W128 _ hmem0 hl rfl hbuf_lt (by exact hdmem_store) haddr0
            (by dsimp [AvxWidth.bytes]; omega)]
          simp only [Effects.All_require_read_access]
          cont
          -- 20: `vmovdqu %ymm0, 0(%dst_ptr)`
          sstep
          have hdst0 : dstAddr + 0#64 = dstAddr + BitVec.ofNat 64 0 := rfl
          rw [storeAvx_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem_store) hdst0
            (by dsimp [AvxWidth.bytes]; omega)]
          simp only [Effects.All_require_write_access]
          rw [toBytes_pmovzxbw_256 _ (by simp [List.length_take, List.length_drop]; omega)]
          let buf1 := bufReplace old 0 32 (expBytes ((d.drop (b + 0)).take 16))
          have hag1 : AgreeTo c d b e 32 hb_le he_le buf1 := by
            simpa using agreeTo_bufReplace (len := 32) hag0 (Nat.le_refl 0) (by omega)
              (by rw [expBytes_length, List.length_take, List.length_drop]; omega)
              (fun i hi => expBytes_slice_getElem hc hl hb_le he_le (by omega) i hi)
          cont
          -- 21: `movl %dst_ptr32, %tmp32`
          sstep
          cont
          -- 22: `andl $31, %tmp32`
          sstep
          intro _af1
          cont
          -- 23: `subl $32, %tmp32`
          sstep
          cont
          -- 24: `negl %tmp32`
          sstep
          have hdstAddr_even : dstAddr.getLsbD 0 = false := getCharsDstAddr_even hdst_even
          have ⟨hsh_lo, hsh_hi, ht_eq, hshr_eq⟩ := align32_even_props dstAddr hdstAddr_even
          let t32 := -((dstAddr.setWidth 32 &&& 31#32) - 32#32)
          let sh := (t32 >>> 1).toNat
          have ht64 : t32.zeroExtend 64 = BitVec.ofNat 64 (2 * sh) := by
            change (-((dstAddr.setWidth 32 &&& 31#32) - 32#32)).zeroExtend 64 = _ at *
            rw [ht_eq]
            exact bitvec32_ofNat_ze64 (2 * sh) (by dsimp only [sh, t32] at *; omega)
          cont
          -- 25: `addq %tmp64, %dst_ptr64`
          sstep
          simp only [h_dst_tmp, ↓reduceIte]
          rw [show BitVec.setWidth 64 (-((dstAddr.setWidth 32 &&& 31#32) - 32#32)) =
            BitVec.ofNat 64 (2 * sh) from ht64]
          cont
          -- 26: `shrl $1, %tmp32`
          sstep
          simp only [h_tmp_dst, ↓reduceIte,
            setWidth32_ofNat64 (2 * sh) (by dsimp only [sh, t32] at *; omega)]
          intro _af2
          have hsh_hi' : sh ≤ 16 := by dsimp only [sh, t32]; exact hsh_hi
          have hshr32 : (BitVec.ofNat 32 (2 * sh)).ushiftRight 1 = BitVec.ofNat 32 sh := by
            apply BitVec.eq_of_toNat_eq
            change ((BitVec.ofNat 32 (2 * sh)) >>> 1).toNat = (BitVec.ofNat 32 sh).toNat
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : 2 * sh < 2 ^ 32),
              Nat.mod_eq_of_lt (by omega : sh < 2 ^ 32), Nat.shiftRight_eq_div_pow]
            omega
          have hshr64 : BitVec.setWidth 64 ((BitVec.ofNat 32 (2 * sh)).ushiftRight 1) =
              BitVec.ofNat 64 sh := by
            rw [hshr32]
            exact bitvec32_ofNat_ze64 sh (by omega)
          rw [hshr64]
          cont
          -- 27: `addq %tmp64, %src64`
          sstep
          simp only [h_src_tmp, h_src_dst, ↓reduceIte]
          cont
          -- 28: `subl %tmp32, %cnt32`
          sstep
          simp only [h_tmp_src, h_cnt_tmp, h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]
          rw [setWidth32_ofNat64 n (by omega), setWidth32_ofNat64 sh (by omega)]
          cont
          refine compressed_pre_loop_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            sh (n - sh) 32 buf1 (by dsimp only [sh, t32] at *; omega)
            (by dsimp only [sh, t32] at *; omega) (by dsimp only [sh, t32] at *; omega) hag1
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]),
                show r ≠ tmp from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm0 hf_lea.2 _⟩
            rfl ?_ ?_ ?_
          · simp only [get64_set64, h_src_cnt, ↓reduceIte]
            rw [BitVec.add_comm, add_ofNat_eq_add]
          · simp only [get64_set64, h_dst_cnt, h_dst_src, h_dst_tmp, ↓reduceIte]
            rw [BitVec.add_comm]
          · simp only [get64_set64, ↓reduceIte]
            exact bitvec32_sub_ze64 n sh (by omega) (by omega)

theorem uncompressed_le32_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (_hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 16 ≤ rem) (hrem_hi : rem ≤ 32) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (srcBegin.toNat s₀.regs + done)))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 110)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  -- 110: label `uncompressed_le32`
  sstep; cont
  -- 111: `vmovdqu 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 2 * done) := by
    rw [BitVec.add_zero, show 2 * b + 2 * done = 2 * (b + done) by omega]; exact hsrc
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 112: `vmovdqu -32(%src, %cnt, 2), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 32)) := by
    have hdn : done + rem = n := hdone_rem
    rw [hsrc, hcnt, neg_disp_sub_u (by omega) (by omega)]
    rw [show 2 * (b + done + rem) - 32 = 2 * b + (2 * n - 32) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 113: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 ((d.drop (2 * b + 2 * done)).take 32)
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 114: `vmovdqu %ymm1, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * n - 32) 32 ((d.drop (2 * b + (2 * n - 32))).take 32)
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * n - 32 + 32)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
  cont
  -- 115: `jmp done_vzero`
  sstep
  simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
  rw [Int64.add_comm, Int64.sub_add_cancel]
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _⟩
    (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])

theorem uncompressed_tail_at
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hdone_lo : 16 ≤ done) (hrem_lo : 1 ≤ rem) (hrem_hi : rem ≤ 16) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (srcBegin.toNat s₀.regs + done)))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 192)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  -- 192: label `uncompressed_tail`
  sstep; cont
  -- 193: `vmovdqu -32(%src, %cnt, 2), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 32)) := by
    have hdn : done + rem = n := hdone_rem
    rw [hsrc, hcnt, neg_disp_sub_u (by omega) (by omega)]
    rw [show 2 * (b + done + rem) - 32 = 2 * b + (2 * n - 32) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 194: `vmovdqu %ymm0, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * n - 32) 32 ((d.drop (2 * b + (2 * n - 32))).take 32)
  have hag1 : AgreeTo c d b e (max W (2 * n - 32 + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace (len := 32) hag (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf1_eq : buf1 = getCharsBytes c d b e := agreeTo_eq_target hag1 (by omega)
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm0 hf.2 _⟩
    (by change s₀.dmem.storeBytes dstAddr buf1 = _; rw [hbuf1_eq])

theorem uncompressed_lt64_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 32 < rem) (hrem_hi : rem ≤ 64) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (srcBegin.toNat s₀.regs + done)))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 152)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  -- 152: label `uncompressed_lt64`
  sstep; cont
  -- 153: `vmovdqu 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 2 * done) := by
    rw [BitVec.add_zero, show 2 * b + 2 * done = 2 * (b + done) by omega]; exact hsrc
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 154: `vmovdqu 32(%src), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + 32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * done + 32)) := by
    rw [hsrc, add_ofNat_eq_add, show 2 * (b + done) + 32 = 2 * b + (2 * done + 32) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 155: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 ((d.drop (2 * b + 2 * done)).take 32)
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 156: `vmovdqu %ymm1, 32(%dst_ptr)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 32#64 = dstAddr + BitVec.ofNat 64 (2 * done + 32) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * done + 32) 32 ((d.drop (2 * b + (2 * done + 32))).take 32)
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * done + 64)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 157: `vmovdqu -64(%src, %cnt, 2), %ymm0`
  sstep
  have haddr2 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -64#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 64)) := by
    have hdn : done + rem = n := hdone_rem
    rw [hsrc, hcnt, neg_disp_sub_u (by omega) (by omega)]
    rw [show 2 * (b + done + rem) - 64 = 2 * b + (2 * n - 64) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr2 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 158: `vmovdqu -32(%src, %cnt, 2), %ymm1`
  sstep
  have haddr3 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 32)) := by
    have hdn : done + rem = n := hdone_rem
    rw [hsrc, hcnt, neg_disp_sub_u (by omega) (by omega)]
    rw [show 2 * (b + done + rem) - 32 = 2 * b + (2 * n - 32) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr3 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 159: `vmovdqu %ymm0, -64(%dst_ptr, %cnt, 2)`
  sstep
  have hdst2 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -64#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 64) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) hdst2 (by dsimp [AvxWidth.bytes]; rw [hag2.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf3 := bufReplace buf2 (2 * n - 64) 32 ((d.drop (2 * b + (2 * n - 64))).take 32)
  have hag3 : AgreeTo c d b e
      (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * n - 64 + 32)) hb_le he_le buf3 :=
    agreeTo_bufReplace (len := 32) hag2 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 160: `vmovdqu %ymm1, -32(%dst_ptr, %cnt, 2)`
  sstep
  have hdst3 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -32#64 =
      dstAddr + BitVec.ofNat 64 (2 * n - 32) := by
    have hdn : done + rem = n := hdone_rem
    rw [hdst, hcnt, ← hdn]
    exact neg_disp_sub (by omega) (by omega)
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag3.len.symm) (by rw [hag3.len]; omega)
    (by rfl) hdst3 (by dsimp [AvxWidth.bytes]; rw [hag3.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf4 := bufReplace buf3 (2 * n - 32) 32 ((d.drop (2 * b + (2 * n - 32))).take 32)
  have hag4 : AgreeTo c d b e
      (max (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * n - 64 + 32))
        (2 * n - 32 + 32)) hb_le he_le buf4 :=
    agreeTo_bufReplace (len := 32) hag3 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  have hbuf4_eq : buf4 = getCharsBytes c d b e := agreeTo_eq_target hag4 (by omega)
  cont
  -- 161: `jmp done_vzero`
  sstep
  simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
  rw [Int64.add_comm, Int64.sub_add_cancel]
  cont
  exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
    ⟨hf.1, zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
    (by change s₀.dmem.storeBytes dstAddr buf4 = _; rw [hbuf4_eq])

theorem uncompressed_avx4_loop_ind
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem_sub W : Nat) (buf : List UInt8) (t : MachineData)
    (hdone_rem : done + 64 + rem_sub = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (srcBegin.toNat s₀.regs + done)))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem_sub) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 133)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : buf.length < 2 ^ 64 := by rw [hag.len]; omega
  have hbuf_bound : buf.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have h_src_dst : src ≠ dst_ptr := fun h => hnd1.1 (by simp [h])
  have h_src_cnt : src ≠ cnt := fun h => hnd1.1 (by simp [h])
  have h_dst_src : dst_ptr ≠ src := h_src_dst.symm
  have h_dst_cnt : dst_ptr ≠ cnt := fun h => hnd2.1 (by simp [h])
  have h_cnt_src : cnt ≠ src := h_src_cnt.symm
  have h_cnt_dst : cnt ≠ dst_ptr := h_dst_cnt.symm
  -- 133: label `uncompressed_avx4_loop`
  sstep; cont
  -- 134: `vmovdqu 0(%src), %ymm0`
  sstep
  have haddr0 : t.regs.get64 src + 0#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 2 * done) := by
    rw [BitVec.add_zero, show 2 * b + 2 * done = 2 * (b + done) by omega]; exact hsrc
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt hdmem haddr0
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 135: `vmovdqu 32(%src), %ymm1`
  sstep
  have haddr1 : t.regs.get64 src + 32#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * done + 32)) := by
    rw [hsrc, add_ofNat_eq_add, show 2 * (b + done) + 32 = 2 * b + (2 * done + 32) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag.len.symm) hbuf_lt (by exact hdmem) haddr1
    (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 136: `vmovdqu %ymm0, 0(%dst_ptr)`
  sstep
  have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 (2 * done) := by
    rw [BitVec.add_zero]; exact hdst
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag.len.symm) hbuf_bound (by exact hdmem) hdst0
    (by dsimp [AvxWidth.bytes]; rw [hag.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf1 := bufReplace buf (2 * done) 32 ((d.drop (2 * b + 2 * done)).take 32)
  have hag1 : AgreeTo c d b e (max W (2 * done + 32)) hb_le he_le buf1 :=
    agreeTo_bufReplace hag hd_W (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 137: `vmovdqu %ymm1, 32(%dst_ptr)`
  sstep
  have hdst1 : t.regs.get64 dst_ptr + 32#64 = dstAddr + BitVec.ofNat 64 (2 * done + 32) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
    (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf2 := bufReplace buf1 (2 * done + 32) 32 ((d.drop (2 * b + (2 * done + 32))).take 32)
  have hag2 : AgreeTo c d b e (max (max W (2 * done + 32)) (2 * done + 64)) hb_le he_le buf2 :=
    agreeTo_bufReplace (len := 32) hag1 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 138: `vmovdqu 64(%src), %ymm0`
  sstep
  have haddr2 : t.regs.get64 src + 64#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * done + 64)) := by
    rw [hsrc, add_ofNat_eq_add, show 2 * (b + done) + 64 = 2 * b + (2 * done + 64) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr2 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 139: `vmovdqu 96(%src), %ymm1`
  sstep
  have haddr3 : t.regs.get64 src + 96#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * done + 96)) := by
    rw [hsrc, add_ofNat_eq_add, show 2 * (b + done) + 96 = 2 * b + (2 * done + 96) by omega]
  rw [loadAvx_src_at .W256 _ hmem0 hl (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) haddr3 (by dsimp [AvxWidth.bytes]; omega)]
  simp only [Effects.All_require_read_access]
  cont
  -- 140: `vmovdqu %ymm0, 64(%dst_ptr)`
  sstep
  have hdst2 : t.regs.get64 dst_ptr + 64#64 = dstAddr + BitVec.ofNat 64 (2 * done + 64) := by
    rw [hdst, add_ofNat_eq_add]
  rw [zmms_get_set_ymm_ne _ hy01.symm, zmms_get_set]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag2.len.symm) (by rw [hag2.len]; omega)
    (by rfl) hdst2 (by dsimp [AvxWidth.bytes]; rw [hag2.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf3 := bufReplace buf2 (2 * done + 64) 32 ((d.drop (2 * b + (2 * done + 64))).take 32)
  have hag3 : AgreeTo c d b e
      (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * done + 96)) hb_le he_le buf3 :=
    agreeTo_bufReplace (len := 32) hag2 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 141: `vmovdqu %ymm1, 96(%dst_ptr)`
  sstep
  have hdst3 : t.regs.get64 dst_ptr + 96#64 = dstAddr + BitVec.ofNat 64 (2 * done + 96) := by
    rw [hdst, add_ofNat_eq_add]
  rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag3.len.symm) (by rw [hag3.len]; omega)
    (by rfl) hdst3 (by dsimp [AvxWidth.bytes]; rw [hag3.len]; omega)]
  simp only [Effects.All_require_write_access]
  rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
  let buf4 := bufReplace buf3 (2 * done + 96) 32 ((d.drop (2 * b + (2 * done + 96))).take 32)
  let W4 := max (max (max (max W (2 * done + 32)) (2 * done + 64)) (2 * done + 96)) (2 * done + 128)
  have hag4 : AgreeTo c d b e W4 hb_le he_le buf4 :=
    agreeTo_bufReplace (len := 32) hag3 (by omega) (by omega)
      (by simp [List.length_take, List.length_drop]; omega)
      (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
  cont
  -- 142: `addq $128, %src64`
  sstep; cont
  -- 143: `addq $128, %dst_ptr64`
  sstep
  simp only [h_dst_src, ↓reduceIte]
  cont
  -- 144: `subl $64, %cnt32`
  sstep
  simp only [h_cnt_src, h_cnt_dst, ↓reduceIte, hcnt]
  have hcnt32 : (BitVec.ofNat 64 rem_sub).setWidth 32 = BitVec.ofNat 32 rem_sub := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : rem_sub < 2 ^ 32)]
  rw [hcnt32]
  have hcf_sub : ((BitVec.ofNat 32 rem_sub - 64#32).unsigned !=
      (BitVec.ofNat 32 rem_sub).unsigned - (64#32).unsigned) = decide (rem_sub < 64) :=
    bitvec32_toNat_lt_iff_cf rem_sub 64 (by omega) (by decide)
  cont
  -- 145: `jae uncompressed_avx4_loop`
  sstep
  rw [hcf_sub]
  have hsrc_next : t.regs.get64 src + 128#64 =
      s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (b + (done + 64))) := by
    rw [hsrc, add_ofNat_eq_add, show 2 * (b + done) + 128 = 2 * (b + (done + 64)) by omega]
  have hdst_next : t.regs.get64 dst_ptr + 128#64 =
      dstAddr + BitVec.ofNat 64 (2 * (done + 64)) := by
    rw [hdst, add_ofNat_eq_add]; congr 2
  by_cases hrem_ge : 64 ≤ rem_sub
  · have hcf_f : decide (rem_sub < 64) = false := decide_eq_false (by omega)
    simp only [hcf_f, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 133) rfl]
    cont
    refine uncompressed_avx4_loop_ind hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
      (done + 64) (rem_sub - 64) W4 buf4 _ (by omega) (by omega) hag4
      ⟨fun r hr => by
        simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
          show r ≠ dst_ptr from fun h => hr (by simp [h]),
          show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
        exact hf.1 r hr,
        zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
      rfl ?_ ?_ ?_
    · simp only [get64_set64, h_src_cnt, h_src_dst, ↓reduceIte]; rw [BitVec.add_comm]; exact hsrc_next
    · simp only [get64_set64, h_dst_cnt, ↓reduceIte]; rw [BitVec.add_comm]; exact hdst_next
    · simp only [get64_set64, ↓reduceIte]
      exact bitvec32_sub_ze64 rem_sub 64 hrem_ge (by omega)
  · have hrem_lt : rem_sub < 64 := by omega
    have hcf_t : decide (rem_sub < 64) = true := decide_eq_true hrem_lt
    simp only [hcf_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 146: `addl $64, %cnt32`
    sstep
    simp only [BitVec.add_comm 64#32, sub64_add64_ofNat32 rem_sub]
    cont
    -- 147: `je done_vzero`
    sstep
    have hzf0 : (BitVec.ofNat 32 rem_sub == 0#32) = (rem_sub == 0) :=
      ofNat32_eq_zero (by omega)
    rw [hzf0]
    by_cases hrem0 : rem_sub = 0
    · subst hrem0
      simp only [beq_self_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 195) rfl]
      cont
      have hbuf4_eq : buf4 = getCharsBytes c d b e := agreeTo_eq_target hag4 (by omega)
      exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
        ⟨fun r hr => by
          simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
            show r ≠ dst_ptr from fun h => hr (by simp [h]),
            show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
          exact hf.1 r hr,
          zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
        (by change s₀.dmem.storeBytes dstAddr buf4 = _; rw [hbuf4_eq])
    · have hbeq_f : (rem_sub == 0) = false := beq_false_of_ne hrem0
      simp only [hbeq_f, Bool.false_eq_true, ↓reduceIte]
      cont
      have hsrc_exit :
          (((((t.regs.set64 src (128#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 src) =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (b + (done + 64))) := by
        simp only [get64_set64, h_src_cnt, h_src_dst, ↓reduceIte]
        rw [BitVec.add_comm]; exact hsrc_next
      have hdst_exit :
          (((((t.regs.set64 src (128#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 dst_ptr) =
          dstAddr + BitVec.ofNat 64 (2 * (done + 64)) := by
        simp only [get64_set64, h_dst_cnt, ↓reduceIte]
        rw [BitVec.add_comm]; exact hdst_next
      have hcnt_exit :
          (((((t.regs.set64 src (128#64 + t.regs.get64 src)).set64 dst_ptr
            (128#64 + t.regs.get64 dst_ptr)).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub - 64#32))).set64 cnt
            (BitVec.setWidth 64 (BitVec.ofNat 32 rem_sub))).get64 cnt) =
          BitVec.ofNat 64 rem_sub := by
        simp only [get64_set64, ↓reduceIte]
        exact bitvec32_ofNat_ze64 rem_sub (by omega)
      -- 148: `cmpl $16, %cnt32`
      sstep
      cont
      -- 149: `jbe uncompressed_tail`
      sstep
      rw [jbe_ofNat32 (by omega) (by decide)]
      by_cases h16 : rem_sub ≤ 16
      · simp only [decide_eq_true h16, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 192) rfl]
        cont
        exact uncompressed_tail_at H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
          (done + 64) rem_sub W4 buf4 (by omega) (by omega) (by omega) h16 (by omega) hag4
          ⟨fun r hr => by
            simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
              show r ≠ dst_ptr from fun h => hr (by simp [h]),
              show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr,
            zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
          rfl hsrc_exit hdst_exit hcnt_exit
      · simp only [decide_eq_false h16, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 150: `cmpl $32, %cnt32`
        sstep
        cont
        -- 151: `jbe uncompressed_le32`
        sstep
        rw [jbe_ofNat32 (by omega) (by decide)]
        by_cases h32 : rem_sub ≤ 32
        · simp only [decide_eq_true h32, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 110) rfl]
          cont
          exact uncompressed_le32_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            (done + 64) rem_sub W4 buf4 (by omega) (by omega) h32 (by omega) hag4
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
            rfl hsrc_exit hdst_exit hcnt_exit
        · simp only [decide_eq_false h32, Bool.false_eq_true, ↓reduceIte]
          cont
          exact uncompressed_lt64_at hlab H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
            (done + 64) rem_sub W4 buf4 (by omega) (by omega) (by omega) (by omega) hag4
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 (zmmsFrame_set_ymm1 (zmmsFrame_set_ymm0 hf.2 _) _) _) _⟩
            rfl hsrc_exit hdst_exit hcnt_exit
termination_by rem_sub

theorem uncompressed_pre_loop_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (done rem W : Nat) (buf : List UInt8)
    (hdone_rem : done + rem = ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)
    (hrem_lo : 64 < rem) (hd_W : 2 * done ≤ W)
    (hag : AgreeTo c d (srcBegin.toNat s₀.regs) ((s₀.regs.get64 srcEnd).setWidth 32).toNat W hb_le he_le buf)
    (hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) buf)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * (srcBegin.toNat s₀.regs + done)))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs + BitVec.ofNat 64 (2 * done))
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 rem) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 131)⟩ := by
  have he32 : 2 * ((s₀.regs.get64 srcEnd).setWidth 32).toNat < 2 ^ 32 := nat_2e_lt64 he_le
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have h_src_cnt : src ≠ cnt := fun h => hnd1.1 (by simp [h])
  have h_dst_cnt : dst_ptr ≠ cnt := fun h => hnd2.1 (by simp [h])
  -- 131: label `uncompressed_pre_loop`
  sstep; cont
  -- 132: `subl $64, %cnt32`
  sstep; cont
  refine uncompressed_avx4_loop_ind hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
    done (rem - 64) W buf _ (by omega) hd_W hag
    (avxFrame_setReg hf (by simp) _)
    hdmem
    (by simp only [get64_set64, h_src_cnt, ↓reduceIte]; exact hsrc)
    (by simp only [get64_set64, h_dst_cnt, ↓reduceIte]; exact hdst)
    (by
      simp only [get64_set64, hcnt, ↓reduceIte]
      rw [setWidth32_ofNat64 rem (by omega)]
      exact bitvec32_sub_ze64 rem 64 (by omega) (by omega))

theorem uncompressed_small_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (hn16 : ((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs < 16)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms)
    (hdmem : t.dmem = s₀.dmem.storeBytes (getCharsDstAddr dst dstBegin s₀.regs) old)
    (hsrc : t.regs.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * srcBegin.toNat s₀.regs))
    (hdst : t.regs.get64 dst_ptr = getCharsDstAddr dst dstBegin s₀.regs)
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 162)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hbuf_lt : old.length < 2 ^ 64 := by omega
  have hbuf_bound : old.length ≤ 2 ^ 64 := by omega
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  have hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t :=
    ⟨hregs, hz ▸ zmmsFrame_refl ymm0 ymm1 s₀⟩
  have hag0 : AgreeTo c d b e 0 hb_le he_le old :=
    ⟨hold, Nat.zero_le _, fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have h_src_tmp : src ≠ tmp := fun h => hnd1.1 (by simp [h])
  have h_dst_tmp : dst_ptr ≠ tmp := fun h => hnd2.1 (by simp [h])
  have h_cnt_tmp : cnt ≠ tmp := fun h => hnd3.1 (by simp [h])
  have hcnt32 : (t.regs.get64 cnt).setWidth 32 = BitVec.ofNat 32 n := by
    rw [hcnt]; exact setWidth32_ofNat64 n (by omega)
  -- 162: label `uncompressed_small`
  sstep; cont
  -- 163: `cmpl $8, %cnt32`
  sstep; rw [hcnt32]; cont
  -- 164: `jae uncompressed_8_15`
  sstep
  rw [cf_ofNat32 (by omega) (by decide)]
  by_cases hn8 : 8 ≤ n
  · have hcf_f : decide (n < 8) = false := decide_eq_false (by omega)
    simp only [hcf_f, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 186) rfl]
    cont
    -- 186: label `uncompressed_8_15`
    sstep; cont
    -- 187: `vmovdqu 0(%src), %xmm0`
    sstep
    have haddr0 : t.regs.get64 src + 0#64 =
        s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 0) := by
      rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
    rw [loadAvx_src_at .W128 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0
      (by dsimp [AvxWidth.bytes]; omega)]
    simp only [Effects.All_require_read_access]
    cont
    -- 188: `vmovdqu %xmm0, 0(%dst_ptr)`
    sstep
    have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
      rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
    rw [storeAvx_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0
      (by dsimp [AvxWidth.bytes]; omega)]
    simp only [Effects.All_require_write_access]
    rw [toBytes_ofInt_ofBytes 16 _ (by simp [List.length_take, List.length_drop]; omega)]
    let buf1 := bufReplace old 0 16 ((d.drop (2 * b + 0)).take 16)
    have hag1 : AgreeTo c d b e 16 hb_le he_le buf1 :=
      agreeTo_bufReplace (len := 16) hag0 (Nat.le_refl 0) (by omega)
        (by simp [List.length_take, List.length_drop]; omega)
        (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
    cont
    -- 189: `vmovdqu -16(%src, %cnt, 2), %xmm0`
    sstep
    have haddr1 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -16#64 =
        s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 16)) := by
      rw [hsrc, hcnt, neg_disp_sub_u0 (by omega) (by omega)]
      rw [show 2 * (b + n) - 16 = 2 * b + (2 * n - 16) by omega]
    rw [loadAvx_src_at .W128 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
      (by rfl) haddr1 (by dsimp [AvxWidth.bytes]; omega)]
    simp only [Effects.All_require_read_access]
    cont
    -- 190: `vmovdqu %xmm0, -16(%dst_ptr, %cnt, 2)`
    sstep
    have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -16#64 =
        dstAddr + BitVec.ofNat 64 (2 * n - 16) := by
      rw [hdst, hcnt]
      exact neg_disp_sub0 (by omega) (by omega)
    rw [storeAvx_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
      (by rfl) hdst1 (by dsimp [AvxWidth.bytes]; rw [hag1.len]; omega)]
    simp only [Effects.All_require_write_access]
    rw [toBytes_ofInt_ofBytes 16 _ (by simp [List.length_take, List.length_drop]; omega)]
    let buf2 := bufReplace buf1 (2 * n - 16) 16 ((d.drop (2 * b + (2 * n - 16))).take 16)
    have hag2 : AgreeTo c d b e (max 16 (2 * n - 16 + 16)) hb_le he_le buf2 :=
      agreeTo_bufReplace (len := 16) hag1 (by omega) (by omega)
        (by simp [List.length_take, List.length_drop]; omega)
        (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
    have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
    cont
    -- 191: `jmp done_vzero`
    sstep
    simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 195) rfl]
    rw [Int64.add_comm, Int64.sub_add_cancel]
    cont
    exact done_vzero_at H hy0 hy1 hy01 c d s₀ _
      ⟨hf.1, zmmsFrame_set_xmm0 hf.2 _⟩
      (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])
  · have hn_lt8 : n < 8 := by omega
    have hcf_t8 : decide (n < 8) = true := decide_eq_true hn_lt8
    simp only [hcf_t8, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 165: `cmpl $4, %cnt32`
    sstep; rw [hcnt32]; cont
    -- 166: `jb uncompressed_lt4`
    sstep
    rw [cf_ofNat32 (by omega) (by decide)]
    by_cases hn4 : n < 4
    · simp only [decide_eq_true hn4, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 172) rfl]
      cont
      -- 172: label `uncompressed_lt4`
      sstep; cont
      -- 173: `cmpl $2, %cnt32`
      sstep; rw [hcnt32]; cont
      -- 174: `jb uncompressed_1`
      sstep
      rw [cf_ofNat32 (by omega) (by decide)]
      by_cases hn2 : n < 2
      · simp only [decide_eq_true hn2, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 180) rfl]
        cont
        -- 180: label `uncompressed_1`
        sstep; cont
        -- 181: `testl %cnt32, %cnt32`
        sstep; rw [hcnt32]
        intro _af
        have hself : BitVec.ofNat 32 n &&& BitVec.ofNat 32 n = BitVec.ofNat 32 n := by bv_decide
        rw [hself, ofNat32_eq_zero (by omega)]
        cont
        -- 182: `je done`
        sstep
        by_cases hn0 : n = 0
        · simp only [hn0, beq_self_eq_true, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 197) rfl]
          cont
          have hold_eq : old = getCharsBytes c d b e := agreeTo_eq_target hag0 (by omega)
          exact done_at H c d s₀ _ hregs (Or.inl hz) (by rw [hdmem, hold_eq])
        · have hn1 : n = 1 := by omega
          have hbeq_f : (n == 0) = false := beq_false_of_ne hn0
          simp only [hbeq_f, Bool.false_eq_true, ↓reduceIte]
          cont
          -- 183: `movzwl 0(%src), %tmp32`
          sstep
          have haddr0 : t.regs.get64 src + 0#64 =
              s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 0) := by
            rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
          rw [load_src_at .W16 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0
            (by dsimp [Width.bytes]; omega)]
          simp only [Effects.All_require_read_access]
          cont
          -- 184: `movw %tmp16, 0(%dst_ptr)`
          sstep
          simp only [h_dst_tmp, ↓reduceIte]
          have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
            rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
          rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0
            (by dsimp [Width.bytes]; omega)]
          simp only [Effects.All_require_write_access]
          rw [get16_set64_ofInt16_ze32_ze64,
            toBytes_ofInt_ofBytes 2 _ (by simp [List.length_take, List.length_drop]; omega)]
          let buf1 := bufReplace old 0 2 ((d.drop (2 * b + 0)).take 2)
          have hag1 : AgreeTo c d b e 2 hb_le he_le buf1 :=
            agreeTo_bufReplace (len := 2) hag0 (Nat.le_refl 0) (by omega)
              (by simp [List.length_take, List.length_drop]; omega)
              (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
          have hbuf1_eq : buf1 = getCharsBytes c d b e := agreeTo_eq_target hag1 (by omega)
          cont
          -- 185: `jmp done`
          sstep
          simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 197) rfl]
          rw [Int64.add_comm, Int64.sub_add_cancel]
          cont
          exact done_at H c d s₀ _
            (fun r hr => by
              simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr)
            (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf1 = _; rw [hbuf1_eq])
      · have hn_ge2 : 2 ≤ n := by omega
        have hcf_f2 : decide (n < 2) = false := decide_eq_false (by omega)
        simp only [hcf_f2, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 175: `movl 0(%src), %tmp32`
        sstep
        have haddr0 : t.regs.get64 src + 0#64 =
            s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 0) := by
          rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
        rw [load_src_at .W32 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0
          (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_read_access]
        cont
        -- 176: `movl %tmp32, 0(%dst_ptr)`
        sstep
        simp only [h_dst_tmp, ↓reduceIte]
        have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
          rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
        rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0
          (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_write_access]
        rw [toBytes_ofInt_ofBytes 4 _ (by simp [List.length_take, List.length_drop]; omega)]
        let buf1 := bufReplace old 0 4 ((d.drop (2 * b + 0)).take 4)
        have hag1 : AgreeTo c d b e 4 hb_le he_le buf1 :=
          agreeTo_bufReplace (len := 4) hag0 (Nat.le_refl 0) (by omega)
            (by simp [List.length_take, List.length_drop]; omega)
            (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
        cont
        -- 177: `movl -4(%src, %cnt, 2), %tmp32`
        sstep
        simp only [h_src_tmp, h_cnt_tmp, ↓reduceIte]
        have haddr1 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -4#64 =
            s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 4)) := by
          rw [hsrc, hcnt, neg_disp_sub_u0 (by omega) (by omega)]
          rw [show 2 * (b + n) - 4 = 2 * b + (2 * n - 4) by omega]
        rw [load_src_at .W32 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
          (by rfl) haddr1 (by dsimp [Width.bytes]; omega)]
        simp only [Effects.All_require_read_access]
        cont
        -- 178: `movl %tmp32, -4(%dst_ptr, %cnt, 2)`
        sstep
        simp only [h_dst_tmp, h_cnt_tmp, ↓reduceIte]
        have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -4#64 =
            dstAddr + BitVec.ofNat 64 (2 * n - 4) := by
          rw [hdst, hcnt]
          exact neg_disp_sub0 (by omega) (by omega)
        rw [store_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
          (by rfl) hdst1 (by dsimp [Width.bytes]; rw [hag1.len]; omega)]
        simp only [Effects.All_require_write_access]
        rw [toBytes_ofInt_ofBytes 4 _ (by simp [List.length_take, List.length_drop]; omega)]
        let buf2 := bufReplace buf1 (2 * n - 4) 4 ((d.drop (2 * b + (2 * n - 4))).take 4)
        have hag2 : AgreeTo c d b e (max 4 (2 * n - 4 + 4)) hb_le he_le buf2 :=
          agreeTo_bufReplace (len := 4) hag1 (by omega) (by omega)
            (by simp [List.length_take, List.length_drop]; omega)
            (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
        have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
        cont
        -- 179: `jmp done`
        sstep
        simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 197) rfl]
        rw [Int64.add_comm, Int64.sub_add_cancel]
        cont
        exact done_at H c d s₀ _
          (fun r hr => by
            simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
            exact hf.1 r hr)
          (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])
    · have hn_ge4 : 4 ≤ n := by omega
      have hcf_f4 : decide (n < 4) = false := decide_eq_false (by omega)
      simp only [hcf_f4, Bool.false_eq_true, ↓reduceIte]
      cont
      -- 167: `movq 0(%src), %tmp64`
      sstep
      have haddr0 : t.regs.get64 src + 0#64 =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 0) := by
        rw [BitVec.add_zero, Nat.add_zero]; exact hsrc
      rw [load_src_at .W64 _ hmem0 hl rfl hbuf_lt (by exact hdmem) haddr0
        (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 168: `movq %tmp64, 0(%dst_ptr)`
      sstep
      simp only [h_dst_tmp, ↓reduceIte]
      have hdst0 : t.regs.get64 dst_ptr + 0#64 = dstAddr + BitVec.ofNat 64 0 := by
        rw [BitVec.add_zero, BitVec.add_zero]; exact hdst
      rw [store_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem) hdst0
        (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_ofInt_ofBytes 8 _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf1 := bufReplace old 0 8 ((d.drop (2 * b + 0)).take 8)
      have hag1 : AgreeTo c d b e 8 hb_le he_le buf1 :=
        agreeTo_bufReplace (len := 8) hag0 (Nat.le_refl 0) (by omega)
          (by simp [List.length_take, List.length_drop]; omega)
          (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
      cont
      -- 169: `movq -8(%src, %cnt, 2), %tmp64`
      sstep
      simp only [h_src_tmp, h_cnt_tmp, ↓reduceIte]
      have haddr1 : t.regs.get64 src + 2#64 * t.regs.get64 cnt + -8#64 =
          s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + (2 * n - 8)) := by
        rw [hsrc, hcnt, neg_disp_sub_u0 (by omega) (by omega)]
        rw [show 2 * (b + n) - 8 = 2 * b + (2 * n - 8) by omega]
      rw [load_src_at .W64 _ hmem0 hl (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) haddr1 (by dsimp [Width.bytes]; omega)]
      simp only [Effects.All_require_read_access]
      cont
      -- 170: `movq %tmp64, -8(%dst_ptr, %cnt, 2)`
      sstep
      simp only [h_dst_tmp, h_cnt_tmp, ↓reduceIte]
      have hdst1 : t.regs.get64 dst_ptr + 2#64 * t.regs.get64 cnt + -8#64 =
          dstAddr + BitVec.ofNat 64 (2 * n - 8) := by
        rw [hdst, hcnt]
        exact neg_disp_sub0 (by omega) (by omega)
      rw [store_dst_at _ _ hmem0 (hold.trans hag1.len.symm) (by rw [hag1.len]; omega)
        (by rfl) hdst1 (by dsimp [Width.bytes]; rw [hag1.len]; omega)]
      simp only [Effects.All_require_write_access]
      rw [toBytes_ofInt_ofBytes 8 _ (by simp [List.length_take, List.length_drop]; omega)]
      let buf2 := bufReplace buf1 (2 * n - 8) 8 ((d.drop (2 * b + (2 * n - 8))).take 8)
      have hag2 : AgreeTo c d b e (max 8 (2 * n - 8 + 8)) hb_le he_le buf2 :=
        agreeTo_bufReplace (len := 8) hag1 (by omega) (by omega)
          (by simp [List.length_take, List.length_drop]; omega)
          (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
      have hbuf2_eq : buf2 = getCharsBytes c d b e := agreeTo_eq_target hag2 (by omega)
      cont
      -- 171: `jmp done`
      sstep
      simp only [Int64.ofBitVec_toBitVec, addrOf_label hlab (H := H) (i := 197) rfl]
      rw [Int64.add_comm, Int64.sub_add_cancel]
      cont
      exact done_at H c d s₀ _
        (fun r hr => by
          simp only [get64_set64, show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
          exact hf.1 r hr)
        (Or.inl hz) (by change s₀.dmem.storeBytes dstAddr buf2 = _; rw [hbuf2_eq])

theorem uncompressed_entry_at
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    (hdisj : ∀ r, r ∈ [obj, srcEnd, dst] ++ srcBegin.regs ++ dstBegin.regs →
      r ∉ [src, dst_ptr, cnt, tmp])
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hc : c.getLsbD 0 = true) (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hsrc_hi : srcBegin.hi32Zero s₀.regs) (hdst_hi : dstBegin.hi32Zero s₀.regs)
    (hdst_even : (s₀.regs.get64 dst).getLsbD 0 = false)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms) (hdmem : t.dmem = s₀.dmem)
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 103)⟩ := by
  let b := srcBegin.toNat s₀.regs
  let e := ((s₀.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  let dstAddr := getCharsDstAddr dst dstBegin s₀.regs
  have he32 : 2 * e < 2 ^ 32 := nat_2e_lt64 he_le
  have hd_len : d.length = 2 * (c >>> 1).toNat := hl.trans (strByteLen_uncompressed hc)
  have he_d : 2 * e ≤ d.length := by rw [hd_len]; omega
  have hbuf_lt : old.length < 2 ^ 64 := by omega
  have hbuf_bound : old.length ≤ 2 ^ 64 := by omega
  have hf : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀ t :=
    ⟨hregs, hz ▸ zmmsFrame_refl ymm0 ymm1 s₀⟩
  have hnd1 := List.nodup_cons.mp hnd
  have hnd2 := List.nodup_cons.mp hnd1.2
  have hnd3 := List.nodup_cons.mp hnd2.2
  have h_dst_src : dst_ptr ≠ src := fun h => hnd1.1 (by simp [h])
  have h_cnt_src : cnt ≠ src := fun h => hnd1.1 (by simp [h])
  have h_cnt_dst : cnt ≠ dst_ptr := fun h => hnd2.1 (by simp [h])
  have h_tmp_src : tmp ≠ src := fun h => hnd1.1 (by simp [h])
  have h_tmp_dst : tmp ≠ dst_ptr := fun h => hnd2.1 (by simp [h])
  have h_tmp_cnt : tmp ≠ cnt := fun h => hnd3.1 (by simp [h])
  have h_cnt_tmp : cnt ≠ tmp := h_tmp_cnt.symm
  have h_src_tmp : src ≠ tmp := h_tmp_src.symm
  have h_dst_tmp : dst_ptr ≠ tmp := h_tmp_dst.symm
  have h_src_dst : src ≠ dst_ptr := h_dst_src.symm
  have h_src_cnt : src ≠ cnt := h_cnt_src.symm
  have h_dst_cnt : dst_ptr ≠ cnt := h_cnt_dst.symm
  have hdmem_store : t.dmem = s₀.dmem.storeBytes dstAddr old := by
    rw [hdmem]
    have hmem' := hmem0
    rw [sep_comm (StringAt (s₀.regs.get64 obj) c d) (Eq (old.At dstAddr)), sep_assoc] at hmem'
    exact (Mem.storeBytes_eq_of_sep old _ _ s₀.dmem hmem').symm
  have hag0 : AgreeTo c d b e 0 hb_le he_le old :=
    ⟨hold, Nat.zero_le _, fun j hj => False.elim (Nat.not_lt_zero j hj)⟩
  have hobj_eq : t.regs.get64 obj = s₀.regs.get64 obj := hregs obj (hdisj obj (by simp))
  have hdst_eq : t.regs.get64 dst = s₀.regs.get64 dst := hregs dst (hdisj dst (by simp))
  -- 103: label `copy_uncompressed`
  sstep; cont
  -- 104: `leaq arrayAddr(obj, srcBegin, .W16, 16), %src`
  have hsrc_lea (p : Std.Rco Int64) :
      (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr obj srcBegin .W16 16) t.regs p : BitVec 64) =
        s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b) := by
    have hhi_t : srcBegin.hi32Zero t.regs := by
      cases srcBegin with
      | imm _ => trivial
      | reg r => simpa [RegOrImm.hi32Zero, hregs r (hdisj r (by simp [RegOrImm.regs]))] using hsrc_hi
    rw [addr_arrayAddr t.regs obj srcBegin .W16 16 _ hhi_t, hobj_eq]
    have heval : srcBegin.eval64 t.regs = BitVec.ofNat 64 b := by
      cases srcBegin with
      | imm _ => rfl
      | reg r => simp [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, b,
          hregs r (hdisj r (by simp [RegOrImm.regs]))]
    rw [heval]
    simp [Width.bytes, ← BitVec.ofNat_mul]
  sstep
  rw [hsrc_lea]
  cont
  -- 105: `leaq arrayAddr(dst, dstBegin, .W16, 12), %dst_ptr`
  have hdst_lea (p : Std.Rco Int64) :
      (@AddrExpr.interp _ ⟨.W64⟩ (arrayAddr dst dstBegin .W16 12)
        (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b))) p : BitVec 64) =
        dstAddr := by
    have hhi_t : dstBegin.hi32Zero (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b))) := by
      cases dstBegin with
      | imm _ => trivial
      | reg r =>
        have hr : r ≠ src := fun h => hdisj r (by simp [RegOrImm.regs]) (by simp [h])
        simpa [RegOrImm.hi32Zero, get64_set64, hr, hregs r (hdisj r (by simp [RegOrImm.regs]))] using hdst_hi
    rw [addr_arrayAddr _ dst dstBegin .W16 12 _ hhi_t]
    have hdst_s : (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b))).get64 dst =
        s₀.regs.get64 dst := by
      have hd : dst ≠ src := fun h => hdisj dst (by simp) (by simp [h])
      simp only [get64_set64, hd, ↓reduceIte, hdst_eq]
    have heval : dstBegin.eval64 (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b))) =
        dstBegin.eval64 s₀.regs := by
      cases dstBegin with
      | imm _ => rfl
      | reg r =>
        have hr : r ≠ src := fun h => hdisj r (by simp [RegOrImm.regs]) (by simp [h])
        simp [RegOrImm.eval64, RegOrImm.toNat, RegOrImm.eval32, get64_set64, hr,
          hregs r (hdisj r (by simp [RegOrImm.regs]))]
    rw [hdst_s, heval]; rfl
  sstep
  rw [hdst_lea]
  cont
  let regs_lea := (t.regs.set64 src (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b))).set64 dst_ptr dstAddr
  have hsrc_after : regs_lea.get64 src = s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b) := by
    simp only [regs_lea, get64_set64, h_src_dst, ↓reduceIte]
  have hdst_after : regs_lea.get64 dst_ptr = dstAddr := by
    simp only [regs_lea, get64_set64, ↓reduceIte]
  have hcnt_after : regs_lea.get64 cnt = BitVec.ofNat 64 n := by
    simp only [regs_lea, get64_set64, h_cnt_dst, h_cnt_src, ↓reduceIte]; exact hcnt
  have hcnt32 : (regs_lea.get64 cnt).setWidth 32 = BitVec.ofNat 32 n := by
    rw [hcnt_after, setWidth32_ofNat64 n (by omega)]
  have hf_lea : AvxFrame src dst_ptr cnt tmp ymm0 ymm1 s₀
      { regs := regs_lea, zmms := t.zmms, status := t.status, dmem := t.dmem } :=
    avxFrame_setReg (avxFrame_setReg hf (by simp) _) (by simp) _
  -- 106: `cmpl $16, %cnt32`
  sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
  -- 107: `jb uncompressed_small`
  sstep
  rw [cf_ofNat32 (by omega) (by decide)]
  by_cases hn16 : n < 16
  · simp only [decide_eq_true hn16, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 162) rfl]
    cont
    exact uncompressed_small_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0 hn16
      hf_lea.1 hz hdmem_store hsrc_after hdst_after hcnt_after
  · have hcf_16 : decide (n < 16) = false := decide_eq_false hn16
    simp only [hcf_16, Bool.false_eq_true, ↓reduceIte]
    cont
    -- 108: `cmpl $32, %cnt32`
    sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
    -- 109: `ja uncompressed_gt32`
    sstep
    rw [ja_ofNat32 (by omega) (by decide)]
    by_cases hn32 : n ≤ 32
    · have hja_f : decide (32 < n) = false := decide_eq_false (by omega)
      simp only [hja_f, Bool.false_eq_true, ↓reduceIte]
      cont
      exact uncompressed_le32_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
        0 n 0 old (Nat.zero_add n) (by omega) hn32 (Nat.le_refl 0) hag0 hf_lea hdmem_store
        (by simpa [Nat.add_zero] using hsrc_after) (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after)
        hcnt_after
    · have hja_t : decide (32 < n) = true := decide_eq_true (by omega)
      simp only [hja_t, ↓reduceIte, addrOf_label hlab (H := H) (i := 116) rfl]
      cont
      -- 116: label `uncompressed_gt32`
      sstep; cont
      -- 117: `cmpl $64, %cnt32`
      sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
      -- 118: `jbe uncompressed_lt64`
      sstep
      rw [jbe_ofNat32 (by omega) (by decide)]
      by_cases hn64 : n ≤ 64
      · simp only [decide_eq_true hn64, ↓reduceIte,
          addrOf_label hlab (H := H) (i := 152) rfl]
        cont
        exact uncompressed_lt64_at hlab H hy0 hy1 hy01 hc hl hb_le he_le hold hmem0
          0 n 0 old (Nat.zero_add n) (by omega) hn64 (Nat.le_refl 0) hag0 hf_lea hdmem_store
          (by simpa [Nat.add_zero] using hsrc_after) (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after)
          hcnt_after
      · have hjbe64_f : decide (n ≤ 64) = false := decide_eq_false hn64
        simp only [hjbe64_f, Bool.false_eq_true, ↓reduceIte]
        cont
        -- 119: `cmpl $192, %cnt32`
        sstep; simp only [h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]; rw [setWidth32_ofNat64 n (by omega)]; cont
        -- 120: `jb uncompressed_pre_loop`
        sstep
        rw [cf_ofNat32 (by omega) (by decide)]
        by_cases hn192 : n < 192
        · simp only [decide_eq_true hn192, ↓reduceIte,
            addrOf_label hlab (H := H) (i := 131) rfl]
          cont
          exact uncompressed_pre_loop_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            0 n 0 old (Nat.zero_add n) (by omega) (Nat.le_refl 0) hag0 hf_lea hdmem_store
            (by simpa [Nat.add_zero] using hsrc_after) (by simpa [Nat.mul_zero, BitVec.add_zero] using hdst_after)
            hcnt_after
        · have hcf192_f : decide (n < 192) = false := decide_eq_false hn192
          simp only [hcf192_f, Bool.false_eq_true, ↓reduceIte]
          cont
          -- 121: `vmovdqu 0(%src), %ymm0`
          sstep
          simp only [h_src_dst, ↓reduceIte]
          have haddr0 : (s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b)) + 0#64 =
              s₀.regs.get64 obj + 16#64 + BitVec.ofNat 64 (2 * b + 0) := by
            rw [BitVec.add_zero, Nat.add_zero]
          rw [loadAvx_src_at .W256 _ hmem0 hl rfl hbuf_lt (by exact hdmem_store) haddr0
            (by dsimp [AvxWidth.bytes]; omega)]
          simp only [Effects.All_require_read_access]
          cont
          -- 122: `vmovdqu %ymm0, 0(%dst_ptr)`
          sstep
          have hdst0 : dstAddr + 0#64 = dstAddr + BitVec.ofNat 64 0 := rfl
          rw [storeAvx_dst_at _ _ hmem0 rfl hbuf_bound (by exact hdmem_store) hdst0
            (by dsimp [AvxWidth.bytes]; omega)]
          simp only [Effects.All_require_write_access]
          rw [toBytes_ofInt_ofBytes 32 _ (by simp [List.length_take, List.length_drop]; omega)]
          let buf1 := bufReplace old 0 32 ((d.drop (2 * b + 0)).take 32)
          have hag1 : AgreeTo c d b e 32 hb_le he_le buf1 :=
            agreeTo_bufReplace (len := 32) hag0 (Nat.le_refl 0) (by omega)
              (by simp [List.length_take, List.length_drop]; omega)
              (fun i hi => uncomp_slice_getElem hc hl hb_le he_le (by omega) i hi)
          cont
          -- 123: `movl %dst_ptr32, %tmp32`
          sstep
          cont
          -- 124: `andl $31, %tmp32`
          sstep
          intro _af1
          cont
          -- 125: `subl $32, %tmp32`
          sstep
          cont
          -- 126: `negl %tmp32`
          sstep
          have hdstAddr_even : dstAddr.getLsbD 0 = false := getCharsDstAddr_even hdst_even
          have ⟨hsh_lo, hsh_hi, ht_eq, hshr_eq⟩ := align32_even_props dstAddr hdstAddr_even
          let t32 := -((dstAddr.setWidth 32 &&& 31#32) - 32#32)
          let sh := (t32 >>> 1).toNat
          have ht64 : t32.zeroExtend 64 = BitVec.ofNat 64 (2 * sh) := by
            change (-((dstAddr.setWidth 32 &&& 31#32) - 32#32)).zeroExtend 64 = _ at *
            rw [ht_eq]
            exact bitvec32_ofNat_ze64 (2 * sh) (by dsimp only [sh, t32] at *; omega)
          cont
          -- 127: `addq %tmp64, %src64`
          sstep
          simp only [h_src_tmp, h_src_dst, ↓reduceIte]
          rw [show BitVec.setWidth 64 (-((dstAddr.setWidth 32 &&& 31#32) - 32#32)) =
            BitVec.ofNat 64 (2 * sh) from ht64]
          cont
          -- 128: `addq %tmp64, %dst_ptr64`
          sstep
          simp only [h_dst_tmp, h_dst_src, ↓reduceIte]
          cont
          -- 129: `shrl $1, %tmp32`
          sstep
          simp only [h_tmp_dst, h_tmp_src, ↓reduceIte,
            setWidth32_ofNat64 (2 * sh) (by dsimp only [sh, t32] at *; omega)]
          intro _af2
          have hsh_hi' : sh ≤ 16 := by dsimp only [sh, t32]; exact hsh_hi
          have hshr32 : (BitVec.ofNat 32 (2 * sh)).ushiftRight 1 = BitVec.ofNat 32 sh := by
            apply BitVec.eq_of_toNat_eq
            change ((BitVec.ofNat 32 (2 * sh)) >>> 1).toNat = (BitVec.ofNat 32 sh).toNat
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : 2 * sh < 2 ^ 32),
              Nat.mod_eq_of_lt (by omega : sh < 2 ^ 32), Nat.shiftRight_eq_div_pow]
            omega
          have hshr64 : BitVec.setWidth 64 ((BitVec.ofNat 32 (2 * sh)).ushiftRight 1) =
              BitVec.ofNat 64 sh := by
            rw [hshr32]
            exact bitvec32_ofNat_ze64 sh (by omega)
          rw [hshr64]
          cont
          -- 130: `subl %tmp32, %cnt32`
          sstep
          simp only [h_cnt_tmp, h_cnt_dst, h_cnt_src, ↓reduceIte, hcnt]
          rw [setWidth32_ofNat64 n (by omega)]
          cont
          refine uncompressed_pre_loop_at hlab H hy0 hy1 hy01 hnd hc hl hb_le he_le hold hmem0
            sh (n - sh) 32 buf1 (by dsimp only [sh, t32] at *; omega)
            (by dsimp only [sh, t32] at *; omega) (by dsimp only [sh, t32] at *; omega) hag1
            ⟨fun r hr => by
              simp only [get64_set64, show r ≠ cnt from fun h => hr (by simp [h]),
                show r ≠ dst_ptr from fun h => hr (by simp [h]),
                show r ≠ src from fun h => hr (by simp [h]),
                show r ≠ tmp from fun h => hr (by simp [h]), ↓reduceIte]
              exact hf.1 r hr,
              zmmsFrame_set_ymm0 hf_lea.2 _⟩
            rfl ?_ ?_ ?_
          · simp only [get64_set64, h_src_cnt, h_src_tmp, h_src_dst, ↓reduceIte]
            rw [BitVec.add_comm, add_ofNat_eq_add, show 2 * b + 2 * sh = 2 * (b + sh) by omega]
          · simp only [get64_set64, h_dst_cnt, h_dst_tmp, ↓reduceIte]
            rw [BitVec.add_comm]
          · simp only [get64_set64, ↓reduceIte]
            exact bitvec32_sub_ze64 n sh (by omega) (by omega)

theorem stringGetCharsBody_wp
    (hlab : LabelsPlaced)
    (H : Embedding (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1))
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    (hdisj : ∀ r, r ∈ [obj, srcEnd, dst] ++ srcBegin.regs ++ dstBegin.regs →
      r ∉ [src, dst_ptr, cnt, tmp])
    {c : BitVec 32} {d old : List UInt8} {R : Mem 64 → Prop} {s₀ t : MachineData}
    (hl : d.length = strByteLen c)
    (hb_le : srcBegin.toNat s₀.regs ≤ ((s₀.regs.get64 srcEnd).setWidth 32).toNat)
    (he_le : ((s₀.regs.get64 srcEnd).setWidth 32).toNat ≤ (c >>> 1).toNat)
    (hsrc_hi : srcBegin.hi32Zero s₀.regs) (hdst_hi : dstBegin.hi32Zero s₀.regs)
    (hdst_even : (s₀.regs.get64 dst).getLsbD 0 = false)
    (hold : old.length = 2 * (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs))
    (hmem0 : (StringAt (s₀.regs.get64 obj) c d ⋆ Eq (old.At (getCharsDstAddr dst dstBegin s₀.regs)) ⋆ R) s₀.dmem)
    (hregs : ∀ r, r ∉ [src, dst_ptr, cnt, tmp] → t.regs.get64 r = s₀.regs.get64 r)
    (hz : t.zmms = s₀.zmms) (hdmem : t.dmem = s₀.dmem)
    (hcnt : t.regs.get64 cnt = BitVec.ofNat 64 (((s₀.regs.get64 srcEnd).setWidth 32).toNat - srcBegin.toNat s₀.regs)) :
    Program.Loop (stringGetCharsBody obj srcBegin dst dstBegin src dst_ptr cnt tmp ymm0 ymm1) H
      (StringGetCharsPost srcBegin srcEnd dst dstBegin [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀)
      (fun _ _ => False) ⟨t, Host.addrOf (H.start + 0)⟩ := by
  have hobj_eq : t.regs.get64 obj = s₀.regs.get64 obj := hregs obj (hdisj obj (by simp))
  -- 0: `testl $1, 8(%obj)`
  sstep
  rw [hobj_eq, load_count_at t (A := s₀.regs.get64 obj) (hdmem ▸ hmem0)]
  simp only [Effects.All, Effects.All_require_read_access, test_and1_of_count]
  intro _af
  cont
  -- 1: `jnz copy_uncompressed`
  sstep
  by_cases hc : c.getLsbD 0 = true
  · simp only [hc, Bool.not_true, Bool.not_false, ↓reduceIte,
      addrOf_label hlab (H := H) (i := 103) rfl]
    cont
    exact uncompressed_entry_at hlab H hy0 hy1 hy01 hnd hdisj hc hl hb_le he_le
      hsrc_hi hdst_hi hdst_even hold hmem0 hregs hz hdmem hcnt
  · have hcf : c.getLsbD 0 = false := Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont
    exact compressed_entry_at hlab H hy0 hy1 hy01 hnd hdisj hcf hl hb_le he_le
      hsrc_hi hdst_hi hdst_even hold hmem0 hregs hz hdmem hcnt

end Branches

end GetCharsAvxProof

open GetCharsAvxProof GetCharsProof
open Proof (get_low32 get_low64 set_low32 set_low64 get64_set64 sw32_64 sw32_ofNat lowMm)

/-- Correctness of ART's AVX2 `String.getCharsNoCheck` lowering (`stringGetCharsProg`),
    proved against the shared specification predicates `StringGetCharsPre` and `StringGetCharsPost`. -/
theorem stringGetChars_correct [Host]
    (obj : Reg64) (srcBegin : RegOrImm) (srcEnd dst : Reg64) (dstBegin : RegOrImm)
    (src dst_ptr cnt tmp : Reg64) (ymm0 ymm1 : AvxReg .W256)
    (hnd : [src, dst_ptr, cnt, tmp].Nodup)
    (hdisj : ∀ r, r ∈ [obj, srcEnd, dst] ++ srcBegin.regs ++ dstBegin.regs →
      r ∉ [src, dst_ptr, cnt, tmp])
    (hy0 : ymm0.base ∈ lowMm) (hy1 : ymm1.base ∈ lowMm) (hy01 : ymm0.base ≠ ymm1.base)
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ StringGetCharsPre obj srcBegin srcEnd dst dstBegin c d s ⦄
      stringGetCharsProg obj srcBegin srcEnd dst dstBegin src dst_ptr cnt tmp ymm0 ymm1
    ⦃ fun _ => StringGetCharsPost srcBegin srcEnd dst dstBegin
        [src, dst_ptr, cnt, tmp] [ymm0, ymm1] c d s₀; fun _ _ => False ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hl, hb_le, he_le, hsrc_hi, hdst_hi, hdst_even, _hfit1, _hfit2, ⟨old, R, hold, hmem⟩⟩
  let b := srcBegin.toNat s.regs
  let e := ((s.regs.get64 srcEnd).setWidth 32).toNat
  let n := e - b
  have he32 : e < 2 ^ 32 := ((s.regs.get64 srcEnd).setWidth 32).isLt
  have hrcx0 : (((s.regs.get64 srcEnd).setWidth 32).zeroExtend 64) = BitVec.ofNat 64 e := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.setWidth 64 (BitVec.setWidth 32 (s.regs.get64 srcEnd))).toNat = (BitVec.ofNat 64 e).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold stringGetCharsProg
  cases srcBegin with
  | reg r =>
    have hcond : (RegOrImm.reg r == .imm 0#32) = false :=
      beq_eq_false_iff_ne.mpr (by intro h; cases h)
    simp only [subCntSrcBeginInstr, hcond, Bool.false_eq_true, ↓reduceIte]
    apply wp_append
    apply Program.wp_of_loop
    intro Hpre
    change Program.Loop _ Hpre _ _ ⟨s, Host.addrOf (Hpre.start + 0)⟩
    have hr_cnt : r ≠ cnt := fun h => hdisj r (by simp [RegOrImm.regs]) (by simp [h])
    -- 0: `movl %srcEnd32, %cnt32`
    sstep
    refine Program.loopCont_of_le (by simp) ?_
    -- 1: `subl %r32, %cnt32`
    sstep
    refine Program.loopCont_of_le (by simp) ?_
    refine Program.loop_done ?_
    apply Program.wp_of_loop
    intro H
    refine stringGetCharsBody_wp hlab H hy0 hy1 hy01 hnd hdisj hl hb_le he_le
      hsrc_hi hdst_hi hdst_even hold hmem ?_ rfl rfl ?_
    · intro rx hrx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
      simp only [get64_set64, hrx.2.2.1, ↓reduceIte]
    · simp only [get64_set64, hr_cnt, ↓reduceIte]
      have he32_bv : (s.regs.get64 srcEnd).setWidth 32 = BitVec.ofNat 32 e := by
        apply BitVec.eq_of_toNat_eq; simp [e]
      have hr32 : (s.regs.get64 r).setWidth 32 = BitVec.ofNat 32 b := by
        apply BitVec.eq_of_toNat_eq; simp [b, RegOrImm.toNat, RegOrImm.eval32]
      rw [he32_bv, hr32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he32]
      exact bitvec32_sub_ze64 e b hb_le he32
  | imm v =>
    by_cases hv : v = 0#32
    · subst hv
      have hcond : (RegOrImm.imm 0#32 == .imm 0#32) = true := beq_self_eq_true _
      simp only [hcond, ↓reduceIte, List.append_nil]
      apply wp_append
      apply Program.wp_of_loop
      intro Hpre
      change Program.Loop _ Hpre _ _ ⟨s, Host.addrOf (Hpre.start + 0)⟩
      -- 0: `movl %srcEnd32, %cnt32`
      sstep
      refine Program.loopCont_of_le (by simp) ?_
      refine Program.loop_done ?_
      apply Program.wp_of_loop
      intro H
      refine stringGetCharsBody_wp hlab H hy0 hy1 hy01 hnd hdisj hl hb_le he_le
        hsrc_hi hdst_hi hdst_even hold hmem ?_ rfl rfl ?_
      · intro rx hrx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.2.2.1, ↓reduceIte]
      · simp only [get64_set64, ↓reduceIte, hrcx0]
        have hb0 : b = 0 := by simp [b, RegOrImm.toNat, RegOrImm.eval32]
        change BitVec.ofNat 64 e = BitVec.ofNat 64 (e - b)
        simp [hb0]
    · have hne : (RegOrImm.imm v == .imm 0#32) = false :=
        beq_eq_false_iff_ne.mpr (by intro h; cases h; exact hv rfl)
      simp only [subCntSrcBeginInstr, hne, Bool.false_eq_true, ↓reduceIte]
      apply wp_append
      apply Program.wp_of_loop
      intro Hpre
      change Program.Loop _ Hpre _ _ ⟨s, Host.addrOf (Hpre.start + 0)⟩
      -- 0: `movl %srcEnd32, %cnt32`
      sstep
      refine Program.loopCont_of_le (by simp) ?_
      -- 1: `subl $v.toNat, %cnt32`
      sstep
      refine Program.loopCont_of_le (by simp) ?_
      refine Program.loop_done ?_
      apply Program.wp_of_loop
      intro H
      refine stringGetCharsBody_wp hlab H hy0 hy1 hy01 hnd hdisj hl hb_le he_le
        hsrc_hi hdst_hi hdst_even hold hmem ?_ rfl rfl ?_
      · intro rx hrx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrx
        simp only [get64_set64, hrx.2.2.1, ↓reduceIte]
      · simp only [get64_set64, ↓reduceIte]
        have he32_bv : (s.regs.get64 srcEnd).setWidth 32 = BitVec.ofNat 32 e := by
          apply BitVec.eq_of_toNat_eq; simp [e]
        have hv_eq : BitVec.ofNat 32 v.toNat = BitVec.ofNat 32 b := by
          apply BitVec.eq_of_toNat_eq; simp [b, RegOrImm.toNat, RegOrImm.eval32]
        rw [he32_bv, hv_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he32]
        exact bitvec32_sub_ze64 e b hb_le he32

end

end Kraken.X64.Art
