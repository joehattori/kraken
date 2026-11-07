module

public import Kraken.X64.Art.StringCompareToSpec
public import Kraken.X64.WP.Loop
public import Kraken.X64.WP.Rep
import Kraken.X64.Parser
import all Kraken.Mem
import all Kraken.SeparationMem
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

open Kraken.X64
open Kraken.X64.Art
open Kraken.X64.Art.Proof
open Std.ExtHashMap
open Std.WP

namespace Kraken.X64.Art

public section

/--
Baseline ART runtime stub `art_quick_string_compareto`, copied verbatim from
`art/runtime/arch/x86_64/quick_entrypoints_x86_64.S` (with `MIRROR_STRING_COUNT_OFFSET = 8`,
`MIRROR_STRING_VALUE_OFFSET = 16`), verified against `libart.so` disassembly (`0xec6cc0..0xec6d78`).
-/
@[expose] def stringCompareToStubProg : _root_.Program := parse("
    movl 8(%edi), %r8d
    movl 8(%esi), %r9d
    leal 16(%edi), %edi
    leal 16(%esi), %esi
    shrl $1, %r8d
    jnc .Lstring_compareto_this_is_compressed
    shrl $1, %r9d
    jnc .Lstring_compareto_that_is_compressed
    jmp .Lstring_compareto_both_not_compressed
  .Lstring_compareto_this_is_compressed:
    shrl $1, %r9d
    jnc .Lstring_compareto_both_compressed
    mov %r8d, %eax
    subl %r9d, %eax
    mov %r8d, %ecx
    cmovg %r9d, %ecx
    jecxz .Lstring_compareto_keep_length1
  .Lstring_compareto_loop_comparison_this_compressed:
    movzbl (%edi), %r8d
    movzwl (%esi), %r9d
    addl $1, %edi
    addl $2, %esi
    subl %r9d, %r8d
    loope .Lstring_compareto_loop_comparison_this_compressed
    cmovne %r8d, %eax
  .Lstring_compareto_keep_length1:
    ret
  .Lstring_compareto_that_is_compressed:
    movl %r8d, %eax
    subl %r9d, %eax
    mov %r8d, %ecx
    cmovg %r9d, %ecx
    jecxz .Lstring_compareto_keep_length2
  .Lstring_compareto_loop_comparison_that_compressed:
    movzwl (%edi), %r8d
    movzbl (%esi), %r9d
    addl $2, %edi
    addl $1, %esi
    subl %r9d, %r8d
    loope .Lstring_compareto_loop_comparison_that_compressed
    cmovne %r8d, %eax
  .Lstring_compareto_keep_length2:
    ret
  .Lstring_compareto_both_compressed:
    movl %r8d, %ecx
    movl %r8d, %eax
    subl %r9d, %eax
    cmovg %r9d, %ecx
    jecxz .Lstring_compareto_keep_length3
    repe cmpsb
    je .Lstring_compareto_keep_length3
    movzbl -1(%edi), %eax
    movzbl -1(%esi), %ecx
    jmp .Lstring_compareto_count_difference
  .Lstring_compareto_both_not_compressed:
    movl %r8d, %ecx
    movl %r8d, %eax
    subl %r9d, %eax
    cmovg %r9d, %ecx
    jecxz .Lstring_compareto_keep_length3
    repe cmpsw
    je .Lstring_compareto_keep_length3
    movzwl -2(%edi), %eax
    movzwl -2(%esi), %ecx
  .Lstring_compareto_count_difference:
    subl %ecx, %eax
  .Lstring_compareto_keep_length3:
    ret
")

end

namespace StubProof

private theorem list_getD_eq_getElem {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i]'h := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem addr32_base_disp [Labels] (regs : Reg64s) (r : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W32⟩ { base := some (.reg r), idx := none, disp := .int64 d } regs p).zeroExtend 64 =
      ((regs.get64 r + d.toBitVec).setWidth 32).zeroExtend 64 := by
  simp only [AddrExpr.interp, BitVec.toAddressSize, BitVec.take, BitVec.signed, ConstExpr.interp,
    Width.bits, Int.add_zero]
  rw [BitVec.ofInt_add]
  have h1 : BitVec.ofInt 32 (BitVec.extractLsb' 0 32 (regs.get64 r)).toInt =
      BitVec.setWidth 32 (regs.get64 r) := by
    change BitVec.ofInt 32 (BitVec.setWidth 32 (regs.get64 r)).toInt = _
    rw [BitVec.ofInt_toInt]
  have h2 : BitVec.ofInt 32 d.toInt = d.toBitVec.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth, ← Int64.toInt_toBitVec, BitVec.toInt]
    split <;> simp <;> omega
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_add]
  have hdvd : 2 ^ 32 ∣ 2 ^ 64 := ⟨2 ^ 32, by decide⟩
  rw [← Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd]

theorem addr32_base_disp' [Labels] (regs : Reg64s) (r : Reg64) (d : Int64) (p : Std.Rco Int64) :
    (@AddrExpr.interp _ ⟨.W32⟩ { base := some (.reg r), idx := none, disp := .int64 d } regs p) =
      (regs.get64 r + d.toBitVec).setWidth 32 := by
  have h := addr32_base_disp regs r d p
  have := congrArg (BitVec.setWidth 32) h
  simpa [BitVec.zeroExtend] using this

theorem setWidth32_ze64_of_lt {v : BitVec 64} (hv : v.toNat < 2 ^ 32) :
    (v.setWidth 32).zeroExtend 64 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

theorem setWidth32_sw64_of_lt {v : BitVec 64} (hv : v.toNat < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 v) = v :=
  setWidth32_ze64_of_lt hv

theorem subl_cmovg_cond (x y : BitVec 32) (hx : x.msb = false) (hy : y.msb = false) :
    (!(x - y == 0#32) && ((x - y).msb == ((x - y).signed != x.signed - y.signed))) =
      (y < x) := by
  have hlt1 : x.toNat < 2 ^ 31 := by
    have := BitVec.msb_eq_false_iff_two_mul_lt.mp hx; omega
  have hlt2 : y.toNat < 2 ^ 31 := by
    have := BitVec.msb_eq_false_iff_two_mul_lt.mp hy; omega
  have hxs : x.toInt = (x.toNat : Int) := by rw [BitVec.toInt]; split <;> omega
  have hys : y.toInt = (y.toNat : Int) := by rw [BitVec.toInt]; split <;> omega
  have hs : ((x - y).signed != x.signed - y.signed) = false := by
    simp only [BitVec.signed, BitVec.toInt_sub, hxs, hys, Int.bmod, bne_eq_false_iff_eq]
    have hm : ((x.toNat : Int) - y.toNat) % (2 ^ 32 : Int) =
        if y.toNat ≤ x.toNat then (x.toNat : Int) - y.toNat else (x.toNat : Int) - y.toNat + 2 ^ 32 := by
      split <;> omega
    split <;> split at hm <;> omega
  rw [hs]
  bv_decide

theorem shr1_msb_false (c : BitVec 32) : (c >>> 1).msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  have h := ushiftRight1_lt c
  omega

theorem shr1_cond_cnt :
    (BitVec.extractLsb' 0 8 1#64).toNat &&& 31 = 1 := by decide

theorem shr1_ushiftRight (c : BitVec 32) :
    BitVec.ushiftRight c ((BitVec.extractLsb' 0 8 1#64).toNat &&& 31) = c >>> 1 := by
  rw [shr1_cond_cnt]
  rfl

theorem shr1_ushiftRight' (c : BitVec 32) :
    BitVec.ushiftRight c 1 = c >>> 1 := rfl

theorem ofNat64_toNat32 (x : BitVec 32) :
    BitVec.ofNat 64 x.toNat = BitVec.setWidth 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem minLen_beq_zero (len₁ len₂ : BitVec 32) :
    (BitVec.ofNat 32 (min len₁.toNat len₂.toNat) == 0#32) =
      decide (min len₁.toNat len₂.toNat = 0) := by
  by_cases h : min len₁.toNat len₂.toNat = 0
  · simp [h]
  · have hlt : min len₁.toNat len₂.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) len₁.isLt
    have hne : BitVec.ofNat 32 (min len₁.toNat len₂.toNat) ≠ 0#32 := by
      intro h0
      have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat] at this
      exact h this
    rw [beq_eq_false_iff_ne.mpr hne]
    simp [h]

theorem cmovg_minLen (len₁ len₂ : BitVec 32) (h1 : len₁.msb = false) (h2 : len₂.msb = false) :
    (if (!(len₁ - len₂ == 0#32) &&
          ((len₁ - len₂).msb == ((len₁ - len₂).signed != len₁.signed - len₂.signed))) = true
     then len₂ else len₁) = BitVec.ofNat 32 (min len₁.toNat len₂.toNat) := by
  simp only [subl_cmovg_cond len₁ len₂ h1 h2]
  by_cases hlt : len₂ < len₁
  · have hnat : len₂.toNat < len₁.toNat := BitVec.lt_def.mp hlt
    simp only [hlt, ↓reduceIte, Nat.min_eq_right (Nat.le_of_lt hnat)]
    apply BitVec.eq_of_toNat_eq; simp
  · have hnat : len₁.toNat ≤ len₂.toNat := by
      have : ¬ (len₂.toNat < len₁.toNat) := fun hc => hlt (BitVec.lt_def.mpr hc)
      omega
    simp only [hlt, ↓reduceIte, Nat.min_eq_left hnat]
    apply BitVec.eq_of_toNat_eq; simp

theorem min_zero_spec {c₁ c₂ : BitVec 32} {d₁ d₂ : List UInt8}
    (hmin : min (c₁ >>> 1).toNat (c₂ >>> 1).toNat = 0) :
    compareToSpec (strChars c₁ d₁) (strChars c₂ d₂) = (c₁ >>> 1) - (c₂ >>> 1) := by
  rw [sub_len_eq_compareToSpec_prefix c₁ c₂ d₁ d₂]
  apply compareToSpec_prefix
  intro i hi1 hi2
  rw [strChars_length] at hi1 hi2
  omega

theorem stringAt_load_count {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {m : Mem 64}
    (h : ∃ R', (StringAt p c d ⋆ R') m) :
    m.loadInt (p + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 c.toInt)) := by
  obtain ⟨R', hR'⟩ := h
  exact load_count m p c (fun _ hi => sep_get_l hR' (fun _ hs => stringAt_cnt hi _ hs))

theorem allocatedBytes_eq_padded_length (d : List UInt8) :
    (padded d).length = allocatedBytes d.length := by
  unfold padded allocatedBytes
  simp

theorem stringAt_byteAt {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {m : Mem 64}
    (h : ∃ R', (StringAt p c d ⋆ R') m) (hl : d.length = strByteLen c)
    (hb : p.toNat + 16 + allocatedBytes (strByteLen c) ≤ 2 ^ 32)
    {i : Nat} (hi : i < d.length) :
    m[p + 16#64 + BitVec.ofNat 64 i]? = some d[i] := by
  obtain ⟨R', hR'⟩ := h
  have hplen : (padded d).length = allocatedBytes d.length := allocatedBytes_eq_padded_length d
  have hplen64 : (padded d).length ≤ 2 ^ 64 := by rw [hplen, hl]; omega
  have hi_p : i < (padded d).length := by rw [hplen]; unfold allocatedBytes; omega
  have h1 := sep_get_l hR' (fun _ hs => stringAt_data hi_p hplen64 _ hs)
  rwa [List.getElem_append_left hi] at h1

theorem stringAt_load_byte {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {m : Mem 64}
    (h : ∃ R', (StringAt p c d ⋆ R') m) (hl : d.length = strByteLen c)
    (hb : p.toNat + 16 + allocatedBytes (strByteLen c) ≤ 2 ^ 32)
    {i : Nat} (hi : i < d.length) :
    m.loadInt (p + 16#64 + BitVec.ofNat 64 i) 1 = some (Int.ofBytes [d[i]]) := by
  have hsome : ∀ j < d.length, (m[p + 16#64 + BitVec.ofNat 64 j]?).isSome = true := fun j hj => by
    rw [stringAt_byteAt h hl hb hj]; rfl
  have haddr : p + 16#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 i + 16#64 := by ac_rfl
  rw [haddr, load_chunk m p i 1 d.length hsome (by omega)]
  have hrange : List.range 1 = [0] := rfl
  rw [hrange]
  simp only [List.map_cons, List.map_nil, Nat.add_zero, byteAt]
  rw [stringAt_byteAt h hl hb hi]
  rfl

theorem stringAt_load_word {p : BitVec 64} {c : BitVec 32} {d : List UInt8} {m : Mem 64}
    (h : ∃ R', (StringAt p c d ⋆ R') m) (hl : d.length = strByteLen c)
    (hb : p.toNat + 16 + allocatedBytes (strByteLen c) ≤ 2 ^ 32)
    {i : Nat} (hi : 2 * i + 1 < d.length) :
    m.loadInt (p + 16#64 + BitVec.ofNat 64 (2 * i)) 2 =
      some (Int.ofBytes [d[2 * i], d[2 * i + 1]]) := by
  have hsome : ∀ j < d.length, (m[p + 16#64 + BitVec.ofNat 64 j]?).isSome = true := fun j hj => by
    rw [stringAt_byteAt h hl hb hj]; rfl
  have haddr : p + 16#64 + BitVec.ofNat 64 (2 * i) = p + BitVec.ofNat 64 (2 * i) + 16#64 := by ac_rfl
  rw [haddr, load_chunk m p (2 * i) 2 d.length hsome (by omega)]
  have hrange : List.range 2 = [0, 1] := rfl
  rw [hrange]
  simp only [List.map_cons, List.map_nil, Nat.add_zero, byteAt]
  rw [stringAt_byteAt h hl hb (by omega), stringAt_byteAt h hl hb hi]
  rfl

theorem byte_val_eq_8 (b : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
  have hsingle : Int.ofBytes [b] = b.toNat := by simp [Int.ofBytes]
  have hb : b.toNat < 256 := b.toBitVec.isLt
  rw [hsingle]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  rfl

theorem byte_val_eq_ze32 (b : UInt8) :
    BitVec.ofInt 32 (Int.ofBytes [b]) = b.toBitVec.zeroExtend 32 := by
  rw [byte_ofInt_ze32]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.zeroExtend]

theorem word_val_eq_16 (b0 b1 : UInt8) :
    BitVec.ofInt 16 (Int.ofBytes [b0, b1]) =
      b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8) := by
  have h32 := word_of_bytes_ze32 b0 b1
  have h16 := congrArg (BitVec.setWidth 16) h32
  have h1 : BitVec.setWidth 16 (BitVec.ofInt 32 (Int.ofBytes [b0, b1])) =
      BitVec.ofInt 16 (Int.ofBytes [b0, b1]) := by
    have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
    have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
    have hge : 0 ≤ Int.ofBytes [b0, b1] := Int.ofBytes_ge_zero _
    have hlt : Int.ofBytes [b0, b1] < 2 ^ 16 := by simp [Int.ofBytes]; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt,
      Int.emod_eq_of_lt hge (by omega : Int.ofBytes [b0, b1] < (2 ^ 32 : Nat)),
      Int.emod_eq_of_lt hge (by omega : Int.ofBytes [b0, b1] < (2 ^ 16 : Nat))]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1] at h16
  simpa [BitVec.zeroExtend] using h16

theorem word_val_eq_ze32 (b0 b1 : UInt8) :
    BitVec.ofInt 32 (Int.ofBytes [b0, b1]) =
      (b0.toBitVec.zeroExtend 16 ||| (b1.toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 :=
  word_of_bytes_ze32 b0 b1

theorem char16_sub_eq_zero (x y : BitVec 16) :
    (x.zeroExtend 32 - y.zeroExtend 32 == 0#32) = decide (x = y) := by
  bv_decide

theorem u8_ze32 (b : BitVec 8) :
    (b.zeroExtend 16).zeroExtend 32 = b.zeroExtend 32 := by
  bv_decide

theorem bit_add_sub_cancel_1 (a : BitVec 64) (k : Nat) :
    a + 16#64 + BitVec.ofNat 64 (k + 1) + -1#64 = a + 16#64 + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc (a + 16#64), BitVec.ofNat_add, BitVec.add_assoc (BitVec.ofNat 64 k)]
  simp

theorem bit_add_sub_cancel_2 (a : BitVec 64) (k : Nat) :
    a + 16#64 + BitVec.ofNat 64 (2 * (k + 1)) + -2#64 =
      a + 16#64 + BitVec.ofNat 64 (2 * k) := by
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.add_assoc (a + 16#64),
    BitVec.ofNat_add, BitVec.add_assoc (BitVec.ofNat 64 (2 * k))]
  simp

theorem first_diff_nat (n : Nat) (P : Nat → Prop) :
    (∀ i < n, P i) ∨ ∃ k < n, (∀ i < k, P i) ∧ ¬ P k := by
  induction n with
  | zero => exact Or.inl (fun _ hi => absurd hi (Nat.not_lt_zero _))
  | succ n ih =>
    rcases ih with hall | ⟨k, hk, hpre, hnot⟩
    · by_cases hp : P n
      · exact Or.inl fun i hi => by
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hilt | rfl
          · exact hall i hilt
          · exact hp
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hall, hp⟩
    · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hpre, hnot⟩

section
variable [Host]

set_option hygiene false in
macro "sstep" : tactic => `(tactic| (
  refine Program.loop_of_interp rfl ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp, MachineData.set,
    MachineData.setReg, MachineData.load, Effects.All, Effects.All_require_read_access,
    addr32_base_disp, addr32_base_disp', get_low32, get_low64, set_low32, set_low64,
    get64_set64,
    (by decide : Reg64.rax ≠ .rcx), (by decide : Reg64.rax ≠ .rdi), (by decide : Reg64.rax ≠ .rsi),
    (by decide : Reg64.rax ≠ .r8), (by decide : Reg64.rax ≠ .r9),
    (by decide : Reg64.rcx ≠ .rax), (by decide : Reg64.rcx ≠ .rdi), (by decide : Reg64.rcx ≠ .rsi),
    (by decide : Reg64.rcx ≠ .r8), (by decide : Reg64.rcx ≠ .r9),
    (by decide : Reg64.rdi ≠ .rax), (by decide : Reg64.rdi ≠ .rcx), (by decide : Reg64.rdi ≠ .rsi),
    (by decide : Reg64.rdi ≠ .r8), (by decide : Reg64.rdi ≠ .r9),
    (by decide : Reg64.rsi ≠ .rax), (by decide : Reg64.rsi ≠ .rcx), (by decide : Reg64.rsi ≠ .rdi),
    (by decide : Reg64.rsi ≠ .r8), (by decide : Reg64.rsi ≠ .r9),
    (by decide : Reg64.r8 ≠ .rax), (by decide : Reg64.r8 ≠ .rcx), (by decide : Reg64.r8 ≠ .rdi),
    (by decide : Reg64.r8 ≠ .rsi), (by decide : Reg64.r8 ≠ .r9),
    (by decide : Reg64.r9 ≠ .rax), (by decide : Reg64.r9 ≠ .rcx), (by decide : Reg64.r9 ≠ .rdi),
    (by decide : Reg64.r9 ≠ .rsi), (by decide : Reg64.r9 ≠ .r8),
    CondCode.interp, StatusFlags.from_result,
    Nat.add_assoc, Nat.reduceAdd, Nat.reduceBEq, Nat.reduceLT,
    Int64.toBitVec_ofNat, Int64.toBitVec_neg,
    BitVec.truncate, Width.bits, Width.bytes, BitVec.ofNat_eq_ofNat,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
    shr1_cond_cnt, shr1_ushiftRight, shr1_ushiftRight', sw32_64, sw32_ofNat,
    Bool.false_eq_true, Bool.and_false, Bool.not_false, Bool.not_true,
    BitVec.zero_eq, BitVec.setWidth_eq, ↓reduceIte]))

macro "cont" : tactic => `(tactic| (
  try simp only [Nat.add_assoc, Nat.reduceAdd]
  refine Program.loopCont_of_le (by simp [stringCompareToStubProg]) ?_))

omit [Host] in
theorem p_add_8_lt {p : BitVec 64} {n : Nat} (hb : p.toNat + 16 + n ≤ 2 ^ 32) :
    (p + 8#64).toNat < 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [Host] in
theorem p_add_16_lt {p : BitVec 64} {n : Nat} (hb : p.toNat + 16 + allocatedBytes n ≤ 2 ^ 32) (hn : 0 < n) :
    (p + 16#64).toNat < 2 ^ 32 := by
  have ha : 0 < allocatedBytes n := by unfold allocatedBytes; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [Host] in
theorem p_add_16_k_lt {p : BitVec 64} {len k : Nat} (hb : p.toNat + 16 + allocatedBytes len ≤ 2 ^ 32)
    (hk : k < len) :
    (p + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 := by
  have ha : len ≤ allocatedBytes len := by unfold allocatedBytes; omega
  have h1 : p.toNat + 16 < 2 ^ 64 := by omega
  have h2 : k < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h16 : (16 : Nat) % 2 ^ 64 = 16 := by decide
  rw [h16, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega)]
  omega

omit [Host] in
theorem add32_sw64_of_lt {x y : BitVec 64} {c : BitVec 32}
    (hx : x.toNat < 2 ^ 32) (hsum : x + c.zeroExtend 64 = y) (hy : y.toNat < 2 ^ 32) :
    BitVec.setWidth 64 (c + BitVec.setWidth 32 x) = y := by
  apply BitVec.eq_of_toNat_eq
  have hc : c.toNat < 2 ^ 32 := c.isLt
  have h : (x + c.zeroExtend 64).toNat = y.toNat := congrArg BitVec.toNat hsum
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_add] at h ⊢
  rw [Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 64)] at h
  rw [Nat.mod_eq_of_lt hx]
  have hlt32 : (c.toNat + x.toNat) % 2 ^ 32 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt32]
  omega

macro "stub_frame" h:term : tactic => `(tactic| (
  intro r' hr'
  have hnot : r' ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] := hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [get64_set64, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1,
    hr'.2.2.2.2.1, hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2, ↓reduceIte] <;>
  exact ($h) r' hnot))

omit [Host] in
theorem reg_frame_set64 {regs0 regs : Reg64s} {r : Reg64} {v : BitVec 64}
    (hr_in : r ∈ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp])
    (hprev : ∀ r', r' ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → regs.get64 r' = regs0.get64 r') :
    ∀ r', r' ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] →
      (regs.set64 r v).get64 r' = regs0.get64 r' := by
  intro r' hr'
  have hne : r' ≠ r := fun he => hr' (he ▸ hr_in)
  rw [get64_set64, ite_eq_right (fun h => absurd h hne)]
  exact hprev r' hr'

def StubLoopInv (s : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8) (t : MachineData) : Prop :=
  t.dmem = s.dmem ∧
  t.zmms = s.zmms ∧
  t.regs.get64 .rsp = s.regs.get64 .rsp ∧
  t.regs.get64 .rax = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64 ∧
  (∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r)

def StubPost (s : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8) (ra : Int64)
    (pc : Int64) (t : MachineData) : Prop :=
  pc = ra ∧
  t.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
  t.regs.get64 .rax = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64 ∧
  (∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) ∧
  t.dmem = s.dmem ∧
  t.zmms = s.zmms

theorem stub_ret (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (lblIdx : Nat) (l : Label)
    (hl : stringCompareToStubProg[lblIdx]? = some (.label l))
    (hi : stringCompareToStubProg[lblIdx + 1]? = some (.instr (.regular .W64 .W64 .ret)))
    (hlt : lblIdx + 1 ≤ stringCompareToStubProg.length)
    (hpost : StubLoopInv s c₁ c₂ d₁ d₂ t) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + lblIdx)⟩ := by
  refine Program.loop_of_interp hl ?_
  simp only [Directive.interp, Effects.All, Nat.add_assoc]
  refine Program.loopCont_of_le hlt ?_
  rcases hpost with ⟨hdmem, hzmms, hrsp, hrax, hregs⟩
  obtain ⟨L, hframe⟩ := stringsInMem_frame hmem
  have hload_bytes : ∀ (j : Nat) (hj : j < 8),
      t.dmem[t.regs.get64 .rsp + BitVec.ofNat 64 j]? =
        some ((Int.toBytes 8 ra.toBitVec.toInt)[j]'(by simp [Int.toBytes_length]; omega)) := by
    intro j hj
    rw [hdmem, hrsp]
    exact sep_get_r hframe (fun _ h => sep_get_l h (at_get _ _ (by simp [Int.toBytes_length]; omega)
      (by simp [Int.toBytes_length])))
  have hload : t.dmem.loadInt (t.regs.get64 .rsp) 8 =
      some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by
    have hload' := loadInt_eq t.dmem (t.regs.get64 .rsp) 8 (fun j hj => by
      simp [hload_bytes j hj])
    have hlist : List.map (fun i => (t.dmem[t.regs.get64 .rsp + BitVec.ofNat 64 i]?).getD 0) (List.range 8) =
        Int.toBytes 8 ra.toBitVec.toInt := by
      apply List.ext_getElem
      · simp [Int.toBytes_length]
      · intro j hj1 hj2
        simp only [List.getElem_map, List.getElem_range]
        rw [hload_bytes j (by simpa using hj1)]
        rfl
    simpa [hlist] using hload'
  have hval : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) = ra.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl ra.toBitVec
  refine Program.loop_ret_outside hi hload hval hra ?_
  refine ⟨rfl, ?_, ?_, ?_, hdmem, hzmms⟩
  · simp [get64_set64, hrsp]
  · simp [get64_set64, hrax]
  · intro r hr
    have hne : r ≠ .rsp := fun h => hr (by simp [h])
    simp [get64_set64, hne, hregs r hr]

theorem count_diff_and_ret (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms)
    (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
    (hdiff : (t.regs.get64 .rax).setWidth 32 - (t.regs.get64 .rcx).setWidth 32 =
      compareToSpec (strChars c₁ d₁) (strChars c₂ d₂))
    (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + 64)⟩ := by
  sstep
  cont
  sstep
  cont
  refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 66 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
  · simp [get64_set64, hrsp]
  · simp only [get64_set64, ↓reduceIte, BitVec.zeroExtend]
    rw [hdiff]
  · exact reg_frame_set64 (by simp) hregs

theorem this_compressed_loop (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = false) (hc2 : c₂.getLsbD 0 = true)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hk_eq : k + (m + 1) = min (c₁ >>> 1).toNat (c₂ >>> 1).toNat)
      (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms)
      (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
      (hrax : t.regs.get64 .rax = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64)
      (hrcx : t.regs.get64 .rcx = BitVec.ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k)
      (hrsi : t.regs.get64 .rsi = s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k))
      (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r)
      (hpre : ∀ (j : Nat) (hj : j < k),
        (strChars c₁ d₁)[j]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[j]'(by rw [strChars_length]; omega)),
      Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
        ⟨t, Host.addrOf (H.start + 17)⟩ := by
  induction m with
  | zero =>
    intro k t hk_eq hdmem hzmms hrsp hrax hrcx hrdi hrsi hregs hpre
    have hk1 : k < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
    have hk2 : 2 * k + 1 < d₂.length := by rw [hl₂, strByteLen_uncompressed hc2]; omega
    have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₁ (by rw [← hl₁]; exact hk1)
    have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₂ (by rw [← hl₂]; omega)
    have hload1 : t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k) 1 =
        some (Int.ofBytes [d₁[k]]) := by
      rw [hdmem]
      exact stringAt_load_byte (stringsInMem_left hmem) hl₁ hb₁ hk1
    have hload2 : t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [d₂[2 * k], d₂[2 * k + 1]]) := by
      rw [hdmem]
      exact stringAt_load_word (stringsInMem_right hmem) hl₂ hb₂ hk2
    sstep; cont; sstep
    simp only [hrdi, BitVec.add_zero, setWidth32_sw64_of_lt hlt1, hload1, byte_val_eq_8]
    cont; sstep
    simp only [hrsi, BitVec.add_zero, setWidth32_sw64_of_lt hlt2, hload2, word_val_eq_16]
    cont; sstep
    cont; sstep
    cont; sstep
    cont; sstep
    simp only [hrcx]
    have hrcx_dec : BitVec.ofNat 64 (0 + 1) - 1#64 = 0#64 := rfl
    simp only [hrcx_dec, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cont; sstep
    have hc1_eq : d₁[k].toBitVec.zeroExtend 32 =
        ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_compressed_getElem hc1 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₁ k 0 hk1]
      exact (u8_ze32 d₁[k].toBitVec).symm
    have hc2_eq : (d₂[2 * k].toBitVec.zeroExtend 16 |||
          (d₂[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
        ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_uncompressed_getElem hc2 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₂ (2 * k) 0 (by omega), list_getD_eq_getElem d₂ (2 * k + 1) 0 hk2]
    rw [hc1_eq, hc2_eq, char16_sub_eq_zero]
    by_cases hcur : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)
    · simp only [decide_eq_true hcur, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 25 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hall : ∀ (j : Nat) (h1 : j < (strChars c₁ d₁).length) (h2 : j < (strChars c₂ d₂).length),
            (strChars c₁ d₁)[j] = (strChars c₂ d₂)[j] := by
          intro j hj1 hj2
          rw [strChars_length] at hj1 hj2
          have hj_le : j ≤ k := by omega
          rcases Nat.eq_or_lt_of_le hj_le with rfl | hjlt
          · exact hcur
          · exact hpre j hjlt
        have hspec := compareToSpec_prefix hall
        rw [← sub_len_eq_compareToSpec_prefix] at hspec
        simp only [get64_set64, ↓reduceIte, hrax, BitVec.zeroExtend, sw32_64, hspec]
      · stub_frame hregs
    · simp only [decide_eq_false hcur, Bool.not_false, ↓reduceIte]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 25 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hspec := compareToSpec_diff (k := k)
          (by rw [strChars_length]; omega) (by rw [strChars_length]; omega)
          (fun j hj => hpre j hj) hcur
        simp only [get64_set64, ↓reduceIte, hspec]
      · stub_frame hregs
  | succ m' ih =>
    intro k t hk_eq hdmem hzmms hrsp hrax hrcx hrdi hrsi hregs hpre
    have hk1 : k < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
    have hk2 : 2 * k + 1 < d₂.length := by rw [hl₂, strByteLen_uncompressed hc2]; omega
    have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₁ (by rw [← hl₁]; exact hk1)
    have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₂ (by rw [← hl₂]; omega)
    have hload1 : t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k) 1 =
        some (Int.ofBytes [d₁[k]]) := by
      rw [hdmem]; exact stringAt_load_byte (stringsInMem_left hmem) hl₁ hb₁ hk1
    have hload2 : t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [d₂[2 * k], d₂[2 * k + 1]]) := by
      rw [hdmem]; exact stringAt_load_word (stringsInMem_right hmem) hl₂ hb₂ hk2
    sstep; cont; sstep
    simp only [hrdi, BitVec.add_zero, setWidth32_sw64_of_lt hlt1, hload1, byte_val_eq_8]
    cont; sstep
    simp only [hrsi, BitVec.add_zero, setWidth32_sw64_of_lt hlt2, hload2, word_val_eq_16]
    cont; sstep
    cont; sstep
    cont; sstep
    cont; sstep
    simp only [hrcx]
    have hrcx_next : BitVec.ofNat 64 (m' + 1 + 1) - 1#64 = BitVec.ofNat 64 (m' + 1) := by
      rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
    have hrcx_ne : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
      rw [bne_iff_ne]
      intro h0
      have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m' + 1 < 2 ^ 64)] at this
      omega
    have hc1_eq : d₁[k].toBitVec.zeroExtend 32 =
        ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_compressed_getElem hc1 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₁ k 0 hk1]
      exact (u8_ze32 d₁[k].toBitVec).symm
    have hc2_eq : (d₂[2 * k].toBitVec.zeroExtend 16 |||
          (d₂[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
        ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_uncompressed_getElem hc2 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₂ (2 * k) 0 (by omega), list_getD_eq_getElem d₂ (2 * k + 1) 0 hk2]
    rw [hrcx_next, hrcx_ne, Bool.true_and, hc1_eq, hc2_eq, char16_sub_eq_zero]
    by_cases hcur : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)
    · simp only [decide_eq_true hcur, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 17) rfl]
      cont
      have hk1_next : k + 1 < (c₁ >>> 1).toNat := by omega
      have hk2_next : 2 * (k + 1) < strByteLen c₂ := by rw [strByteLen_uncompressed hc2]; omega
      have hlt1_next : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₁ (by rw [strByteLen_compressed hc1]; exact hk1_next)
      have hlt2_next : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * (k + 1))).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₂ hk2_next
      refine ih (k + 1) _ (by omega) hdmem hzmms ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [get64_set64, hrsp]
      · simp [get64_set64, hrax]
      · simp [get64_set64]
      · simp only [get64_set64, (by decide : Reg64.rdi ≠ .rcx), (by decide : Reg64.rdi ≠ .r8),
          (by decide : Reg64.rdi ≠ .rsi), ↓reduceIte, hrdi]
        exact add32_sw64_of_lt hlt1
          (by change s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k + 1#64 = _; rw [BitVec.add_assoc, ← BitVec.ofNat_add])
          hlt1_next
      · simp only [get64_set64, (by decide : Reg64.rsi ≠ .rcx), (by decide : Reg64.rsi ≠ .r8),
          ↓reduceIte, hrsi]
        exact add32_sw64_of_lt hlt2
          (by change s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k) + 2#64 = _
              rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.add_assoc, ← BitVec.ofNat_add])
          hlt2_next
      · stub_frame hregs
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
        · exact hpre j hjlt
        · exact hcur
    · simp only [decide_eq_false hcur, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 25 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hspec := compareToSpec_diff (k := k)
          (by rw [strChars_length]; omega) (by rw [strChars_length]; omega)
          (fun j hj => hpre j hj) hcur
        simp only [get64_set64, ↓reduceIte, hspec]
      · stub_frame hregs

theorem that_compressed_loop (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = true) (hc2 : c₂.getLsbD 0 = false)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hk_eq : k + (m + 1) = min (c₁ >>> 1).toNat (c₂ >>> 1).toNat)
      (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms)
      (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
      (hrax : t.regs.get64 .rax = ((c₁ >>> 1) - (c₂ >>> 1)).zeroExtend 64)
      (hrcx : t.regs.get64 .rcx = BitVec.ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k))
      (hrsi : t.regs.get64 .rsi = s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k)
      (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r)
      (hpre : ∀ (j : Nat) (hj : j < k),
        (strChars c₁ d₁)[j]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[j]'(by rw [strChars_length]; omega)),
      Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
        ⟨t, Host.addrOf (H.start + 33)⟩ := by
  induction m with
  | zero =>
    intro k t hk_eq hdmem hzmms hrsp hrax hrcx hrdi hrsi hregs hpre
    have hk1 : 2 * k + 1 < d₁.length := by rw [hl₁, strByteLen_uncompressed hc1]; omega
    have hk2 : k < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
    have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₁ (by rw [← hl₁]; omega)
    have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₂ (by rw [← hl₂]; exact hk2)
    have hload1 : t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [d₁[2 * k], d₁[2 * k + 1]]) := by
      rw [hdmem]; exact stringAt_load_word (stringsInMem_left hmem) hl₁ hb₁ hk1
    have hload2 : t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k) 1 =
        some (Int.ofBytes [d₂[k]]) := by
      rw [hdmem]; exact stringAt_load_byte (stringsInMem_right hmem) hl₂ hb₂ hk2
    sstep; cont; sstep
    simp only [hrdi, BitVec.add_zero, setWidth32_sw64_of_lt hlt1, hload1, word_val_eq_16]
    cont; sstep
    simp only [hrsi, BitVec.add_zero, setWidth32_sw64_of_lt hlt2, hload2, byte_val_eq_8]
    cont; sstep
    cont; sstep
    cont; sstep
    cont; sstep
    simp only [hrcx]
    have hrcx_dec : BitVec.ofNat 64 (0 + 1) - 1#64 = 0#64 := rfl
    simp only [hrcx_dec, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cont; sstep
    have hc1_eq : (d₁[2 * k].toBitVec.zeroExtend 16 |||
          (d₁[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
        ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_uncompressed_getElem hc1 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₁ (2 * k) 0 (by omega), list_getD_eq_getElem d₁ (2 * k + 1) 0 hk1]
    have hc2_eq : d₂[k].toBitVec.zeroExtend 32 =
        ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_compressed_getElem hc2 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₂ k 0 hk2]
      exact (u8_ze32 d₂[k].toBitVec).symm
    rw [hc1_eq, hc2_eq, char16_sub_eq_zero]
    by_cases hcur : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)
    · simp only [decide_eq_true hcur, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 41 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hall : ∀ (j : Nat) (h1 : j < (strChars c₁ d₁).length) (h2 : j < (strChars c₂ d₂).length),
            (strChars c₁ d₁)[j] = (strChars c₂ d₂)[j] := by
          intro j hj1 hj2
          rw [strChars_length] at hj1 hj2
          have hj_le : j ≤ k := by omega
          rcases Nat.eq_or_lt_of_le hj_le with rfl | hjlt
          · exact hcur
          · exact hpre j hjlt
        have hspec := compareToSpec_prefix hall
        rw [← sub_len_eq_compareToSpec_prefix] at hspec
        simp only [get64_set64, ↓reduceIte, hrax, BitVec.zeroExtend, sw32_64, hspec]
      · stub_frame hregs
    · simp only [decide_eq_false hcur, Bool.not_false, ↓reduceIte]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 41 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hspec := compareToSpec_diff (k := k)
          (by rw [strChars_length]; omega) (by rw [strChars_length]; omega)
          (fun j hj => hpre j hj) hcur
        simp only [get64_set64, ↓reduceIte, hspec]
      · stub_frame hregs
  | succ m' ih =>
    intro k t hk_eq hdmem hzmms hrsp hrax hrcx hrdi hrsi hregs hpre
    have hk1 : 2 * k + 1 < d₁.length := by rw [hl₁, strByteLen_uncompressed hc1]; omega
    have hk2 : k < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
    have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₁ (by rw [← hl₁]; omega)
    have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
      p_add_16_k_lt hb₂ (by rw [← hl₂]; exact hk2)
    have hload1 : t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [d₁[2 * k], d₁[2 * k + 1]]) := by
      rw [hdmem]; exact stringAt_load_word (stringsInMem_left hmem) hl₁ hb₁ hk1
    have hload2 : t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k) 1 =
        some (Int.ofBytes [d₂[k]]) := by
      rw [hdmem]; exact stringAt_load_byte (stringsInMem_right hmem) hl₂ hb₂ hk2
    sstep; cont; sstep
    simp only [hrdi, BitVec.add_zero, setWidth32_sw64_of_lt hlt1, hload1, word_val_eq_16]
    cont; sstep
    simp only [hrsi, BitVec.add_zero, setWidth32_sw64_of_lt hlt2, hload2, byte_val_eq_8]
    cont; sstep
    cont; sstep
    cont; sstep
    cont; sstep
    simp only [hrcx]
    have hrcx_next : BitVec.ofNat 64 (m' + 1 + 1) - 1#64 = BitVec.ofNat 64 (m' + 1) := by
      rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
    have hrcx_ne : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
      rw [bne_iff_ne]
      intro h0
      have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m' + 1 < 2 ^ 64)] at this
      omega
    have hc1_eq : (d₁[2 * k].toBitVec.zeroExtend 16 |||
          (d₁[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
        ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_uncompressed_getElem hc1 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₁ (2 * k) 0 (by omega), list_getD_eq_getElem d₁ (2 * k + 1) 0 hk1]
    have hc2_eq : d₂[k].toBitVec.zeroExtend 32 =
        ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
      rw [strChars_compressed_getElem hc2 k (by rw [strChars_length]; omega),
        list_getD_eq_getElem d₂ k 0 hk2]
      exact (u8_ze32 d₂[k].toBitVec).symm
    rw [hrcx_next, hrcx_ne, Bool.true_and, hc1_eq, hc2_eq, char16_sub_eq_zero]
    by_cases hcur : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) =
        (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)
    · simp only [decide_eq_true hcur, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 33) rfl]
      cont
      have hk1_next : 2 * (k + 1) < strByteLen c₁ := by rw [strByteLen_uncompressed hc1]; omega
      have hk2_next : k + 1 < (c₂ >>> 1).toNat := by omega
      have hlt1_next : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * (k + 1))).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₁ hk1_next
      have hlt2_next : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₂ (by rw [strByteLen_compressed hc2]; exact hk2_next)
      refine ih (k + 1) _ (by omega) hdmem hzmms ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [get64_set64, hrsp]
      · simp [get64_set64, hrax]
      · simp [get64_set64]
      · simp only [get64_set64, (by decide : Reg64.rdi ≠ .rcx), (by decide : Reg64.rdi ≠ .r8),
          (by decide : Reg64.rdi ≠ .rsi), ↓reduceIte, hrdi]
        exact add32_sw64_of_lt hlt1
          (by change s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k) + 2#64 = _
              rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.add_assoc, ← BitVec.ofNat_add])
          hlt1_next
      · simp only [get64_set64, (by decide : Reg64.rsi ≠ .rcx), (by decide : Reg64.rsi ≠ .r8),
          ↓reduceIte, hrsi]
        exact add32_sw64_of_lt hlt2
          (by change s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k + 1#64 = _; rw [BitVec.add_assoc, ← BitVec.ofNat_add])
          hlt2_next
      · stub_frame hregs
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
        · exact hpre j hjlt
        · exact hcur
    · simp only [decide_eq_false hcur, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 41 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · have hspec := compareToSpec_diff (k := k)
          (by rw [strChars_length]; omega) (by rw [strChars_length]; omega)
          (fun j hj => hpre j hj) hcur
        simp only [get64_set64, ↓reduceIte, hspec]
      · stub_frame hregs

theorem both_compressed_entry (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = false) (hc2 : c₂.getLsbD 0 = false)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms) (hdf : t.status.df = false)
    (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
    (hr8 : t.regs.get64 .r8 = (c₁ >>> 1).zeroExtend 64)
    (hr9 : t.regs.get64 .r9 = (c₂ >>> 1).zeroExtend 64)
    (hrdi : t.regs.get64 .rdi = ((s.regs.get64 .rdi + 16#64).setWidth 32).zeroExtend 64)
    (hrsi : t.regs.get64 .rsi = ((s.regs.get64 .rsi + 16#64).setWidth 32).zeroExtend 64)
    (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + 43)⟩ := by
  let len₁ := c₁ >>> 1
  let len₂ := c₂ >>> 1
  have hlen1 : len₁.toNat = (c₁ >>> 1).toNat := rfl
  have hlen2 : len₂.toNat = (c₂ >>> 1).toNat := rfl
  sstep; cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  rw [cmovg_minLen len₁ len₂ (shr1_msb_false c₁) (shr1_msb_false c₂)]
  cont; sstep
  simp only [minLen_beq_zero len₁ len₂]
  by_cases hmin0 : min len₁.toNat len₂.toNat = 0
  · simp only [decide_eq_true hmin0, ↓reduceIte, addrOf_label hlab (H := H) (i := 66) rfl]
    cont
    refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 66 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
    · simp [get64_set64, hrsp]
    · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
        BitVec.zeroExtend, min_zero_spec hmin0]
    · stub_frame hregs
  · simp only [decide_eq_false hmin0, Bool.false_eq_true, ↓reduceIte]
    cont
    have hn0 : 0 < min len₁.toNat len₂.toNat := Nat.pos_of_ne_zero hmin0
    have hn64 : min len₁.toNat len₂.toNat < 2 ^ 64 := by
      have := ushiftRight1_lt c₁; omega
    have hlt_rdi : (s.regs.get64 .rdi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_compressed hc1] at hb₁; exact hb₁) (by omega)
    have hlt_rsi : (s.regs.get64 .rsi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_compressed hc2] at hb₂; exact hb₂) (by omega)
    have hrdi' : t.regs.get64 .rdi = s.regs.get64 .rdi + 16#64 := by
      rw [hrdi, setWidth32_ze64_of_lt hlt_rdi]
    have hrsi' : t.regs.get64 .rsi = s.regs.get64 .rsi + 16#64 := by
      rw [hrsi, setWidth32_ze64_of_lt hlt_rsi]
    have hrcx_val : (((t.regs.set64 .rcx (BitVec.setWidth 64 len₁)).set64 .rax
          (BitVec.setWidth 64 (len₁ - len₂))).set64 .rcx
          (BitVec.setWidth 64 (BitVec.ofNat 32 (min len₁.toNat len₂.toNat)))).get64 .rcx =
        BitVec.ofNat 64 (min len₁.toNat len₂.toNat) := by
      simp only [get64_set64, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      have hlt32 : min len₁.toNat len₂.toNat < 2 ^ 32 := by have := ushiftRight1_lt c₁; omega
      simp [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hn64]
    let f : Nat → BitVec 8 := fun j => (d₂.getD j 0).toBitVec
    let g : Nat → BitVec 8 := fun j => (d₁.getD j 0).toBitVec
    have hload_rsi : ∀ j < min len₁.toNat len₂.toNat,
        ∃ x, t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 j) 1 = some x ∧
          BitVec.ofInt 8 x = f j := by
      intro j hj
      have hj_len : j < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
      refine ⟨Int.ofBytes [d₂[j]], ?_, ?_⟩
      · rw [hdmem]; exact stringAt_load_byte (stringsInMem_right hmem) hl₂ hb₂ hj_len
      · simp only [f, list_getD_eq_getElem d₂ j 0 hj_len, byte_val_eq_8]
    have hload_rdi : ∀ j < min len₁.toNat len₂.toNat,
        ∃ y, t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 j) 1 = some y ∧
          BitVec.ofInt 8 y = g j := by
      intro j hj
      have hj_len : j < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
      refine ⟨Int.ofBytes [d₁[j]], ?_, ?_⟩
      · rw [hdmem]; exact stringAt_load_byte (stringsInMem_left hmem) hl₁ hb₁ hj_len
      · simp only [g, list_getD_eq_getElem d₁ j 0 hj_len, byte_val_eq_8]
    rcases first_diff_nat (min len₁.toNat len₂.toNat) (fun j => f j = g j) with hall | ⟨k, hk, hpre, hne⟩
    · refine Program.loop_repe_cmpsb_eq (i := 49) rfl hn0 hn64 hdf hrcx_val
        (s.regs.get64 .rsi + 16#64) (s.regs.get64 .rdi + 16#64)
        (by simp [get64_set64, hrsi']) (by simp [get64_set64, hrdi'])
        f g hload_rsi hload_rdi hall ?_
      intro t' ht_mem ht_zmm ht_zf _ _ _ _ ht_regs
      cont; sstep
      simp only [ht_zf, ↓reduceIte, addrOf_label hlab (H := H) (i := 66) rfl]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 66 _ rfl rfl (by decide)
        ⟨ht_mem.trans hdmem, ht_zmm.trans hzmms, ?_, ?_, ?_⟩
      · rw [ht_regs .rsp (by simp)]; simp [get64_set64, hrsp]
      · rw [ht_regs .rax (by simp)]
        have hall_chars : ∀ (j : Nat) (h1 : j < (strChars c₁ d₁).length) (h2 : j < (strChars c₂ d₂).length),
            (strChars c₁ d₁)[j] = (strChars c₂ d₂)[j] := by
          intro j hj1 hj2
          rw [strChars_length] at hj1 hj2
          have hj_min : j < min len₁.toNat len₂.toNat := by omega
          have hfg := (hall j hj_min).symm
          have hj1' : j < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
          have hj2' : j < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
          have hbyte : d₁[j]'hj1' = d₂[j]'hj2' := by
            apply UInt8.toBitVec_inj.mp
            dsimp only [f, g] at hfg
            rwa [list_getD_eq_getElem d₁ j 0 hj1', list_getD_eq_getElem d₂ j 0 hj2'] at hfg
          exact strChars_compressed_eq_of_bytes hc1 hc2 hl₁ hl₂ _ _ hbyte
        have hspec := compareToSpec_prefix hall_chars
        rw [← sub_len_eq_compareToSpec_prefix] at hspec
        simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
          BitVec.zeroExtend, hspec]
      · intro r hr
        have hnot : r ∉ [Reg64.rcx, .rdi, .rsi] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => hr (by simp [h]), fun h => hr (by simp [h]), fun h => hr (by simp [h])⟩
        rw [ht_regs r hnot]
        clear hnot; revert r hr; stub_frame hregs
    · refine Program.loop_repe_cmpsb_ne (i := 49) rfl hk hn64 hdf hrcx_val
        (s.regs.get64 .rsi + 16#64) (s.regs.get64 .rdi + 16#64)
        (by simp [get64_set64, hrsi']) (by simp [get64_set64, hrdi'])
        f g hload_rsi hload_rdi hpre hne ?_
      intro t' ht_mem ht_zmm ht_zf _ _ ht_rsi ht_rdi ht_regs
      cont; sstep
      simp only [ht_zf, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      have hk1 : k < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
      have hk2 : k < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
      have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₁ (by rw [← hl₁]; exact hk1)
      have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₂ (by rw [← hl₂]; exact hk2)
      have hload1 : t'.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 k) 1 =
          some (Int.ofBytes [d₁[k]]) := by
        rw [ht_mem.trans hdmem]; exact stringAt_load_byte (stringsInMem_left hmem) hl₁ hb₁ hk1
      have hload2 : t'.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 k) 1 =
          some (Int.ofBytes [d₂[k]]) := by
        rw [ht_mem.trans hdmem]; exact stringAt_load_byte (stringsInMem_right hmem) hl₂ hb₂ hk2
      simp only [ht_rdi, bit_add_sub_cancel_1, setWidth32_sw64_of_lt hlt1, hload1, byte_val_eq_8]
      cont; sstep
      simp only [ht_rsi, bit_add_sub_cancel_1, setWidth32_sw64_of_lt hlt2, hload2, byte_val_eq_8]
      cont; sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 64) rfl]
      cont
      refine count_diff_and_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem
        (ht_mem.trans hdmem) (ht_zmm.trans hzmms) ?_ ?_ ?_
      · simp [get64_set64, ht_regs .rsp (by simp), hrsp]
      · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
          sw32_64]
        have hc1_eq : d₁[k].toBitVec.zeroExtend 32 =
            ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
          rw [strChars_compressed_getElem hc1 k (by rw [strChars_length]; omega),
            list_getD_eq_getElem d₁ k 0 hk1]
          exact (u8_ze32 d₁[k].toBitVec).symm
        have hc2_eq : d₂[k].toBitVec.zeroExtend 32 =
            ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
          rw [strChars_compressed_getElem hc2 k (by rw [strChars_length]; omega),
            list_getD_eq_getElem d₂ k 0 hk2]
          exact (u8_ze32 d₂[k].toBitVec).symm
        rw [hc1_eq, hc2_eq]
        have hpre_chars : ∀ (j : Nat) (hj : j < k),
            (strChars c₁ d₁)[j]'(by rw [strChars_length]; omega) =
            (strChars c₂ d₂)[j]'(by rw [strChars_length]; omega) := by
          intro j hj
          have hj1' : j < d₁.length := by rw [hl₁, strByteLen_compressed hc1]; omega
          have hj2' : j < d₂.length := by rw [hl₂, strByteLen_compressed hc2]; omega
          have hbyte : d₁[j]'hj1' = d₂[j]'hj2' := by
            apply UInt8.toBitVec_inj.mp
            have hfg := (hpre j hj).symm
            dsimp only [f, g] at hfg
            rwa [list_getD_eq_getElem d₁ j 0 hj1', list_getD_eq_getElem d₂ j 0 hj2'] at hfg
          exact strChars_compressed_eq_of_bytes hc1 hc2 hl₁ hl₂ _ _ hbyte
        have hne_chars : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) ≠
            (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega) := by
          refine strChars_compressed_ne_of_bytes hc1 hc2 hl₁ hl₂ _ _ ?_
          intro heq
          apply hne
          dsimp only [f, g]
          rw [list_getD_eq_getElem d₁ k 0 hk1, list_getD_eq_getElem d₂ k 0 hk2, heq]
        exact (compareToSpec_diff (k := k) (by rw [strChars_length]; omega)
          (by rw [strChars_length]; omega) hpre_chars hne_chars).symm
      · intro r hr
        rw [get64_set64, ite_eq_right (fun h => hr (by simp [h])),
          get64_set64, ite_eq_right (fun h => hr (by simp [h]))]
        have hnot : r ∉ [Reg64.rcx, .rdi, .rsi] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => hr (by simp [h]), fun h => hr (by simp [h]), fun h => hr (by simp [h])⟩
        rw [ht_regs r hnot]
        clear hnot; revert r hr; stub_frame hregs

theorem both_not_compressed_entry (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = true) (hc2 : c₂.getLsbD 0 = true)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms) (hdf : t.status.df = false)
    (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
    (hr8 : t.regs.get64 .r8 = (c₁ >>> 1).zeroExtend 64)
    (hr9 : t.regs.get64 .r9 = (c₂ >>> 1).zeroExtend 64)
    (hrdi : t.regs.get64 .rdi = ((s.regs.get64 .rdi + 16#64).setWidth 32).zeroExtend 64)
    (hrsi : t.regs.get64 .rsi = ((s.regs.get64 .rsi + 16#64).setWidth 32).zeroExtend 64)
    (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + 54)⟩ := by
  let len₁ := c₁ >>> 1
  let len₂ := c₂ >>> 1
  have hlen1 : len₁.toNat = (c₁ >>> 1).toNat := rfl
  have hlen2 : len₂.toNat = (c₂ >>> 1).toNat := rfl
  sstep; cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  rw [cmovg_minLen len₁ len₂ (shr1_msb_false c₁) (shr1_msb_false c₂)]
  cont; sstep
  simp only [minLen_beq_zero len₁ len₂]
  by_cases hmin0 : min len₁.toNat len₂.toNat = 0
  · simp only [decide_eq_true hmin0, ↓reduceIte, addrOf_label hlab (H := H) (i := 66) rfl]
    cont
    refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 66 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
    · simp [get64_set64, hrsp]
    · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
        BitVec.zeroExtend, min_zero_spec hmin0]
    · stub_frame hregs
  · simp only [decide_eq_false hmin0, Bool.false_eq_true, ↓reduceIte]
    cont
    have hn0 : 0 < min len₁.toNat len₂.toNat := Nat.pos_of_ne_zero hmin0
    have hn64 : min len₁.toNat len₂.toNat < 2 ^ 64 := by
      have := ushiftRight1_lt c₁; omega
    have hlt_rdi : (s.regs.get64 .rdi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_uncompressed hc1] at hb₁; exact hb₁) (by omega)
    have hlt_rsi : (s.regs.get64 .rsi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_uncompressed hc2] at hb₂; exact hb₂) (by omega)
    have hrdi' : t.regs.get64 .rdi = s.regs.get64 .rdi + 16#64 := by
      rw [hrdi, setWidth32_ze64_of_lt hlt_rdi]
    have hrsi' : t.regs.get64 .rsi = s.regs.get64 .rsi + 16#64 := by
      rw [hrsi, setWidth32_ze64_of_lt hlt_rsi]
    have hrcx_val : (((t.regs.set64 .rcx (BitVec.setWidth 64 len₁)).set64 .rax
          (BitVec.setWidth 64 (len₁ - len₂))).set64 .rcx
          (BitVec.setWidth 64 (BitVec.ofNat 32 (min len₁.toNat len₂.toNat)))).get64 .rcx =
        BitVec.ofNat 64 (min len₁.toNat len₂.toNat) := by
      simp only [get64_set64, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      have hlt32 : min len₁.toNat len₂.toNat < 2 ^ 32 := by have := ushiftRight1_lt c₁; omega
      simp [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hn64]
    let f : Nat → BitVec 16 := fun j => (strChars c₂ d₂).getD j 0#16
    let g : Nat → BitVec 16 := fun j => (strChars c₁ d₁).getD j 0#16
    have hload_rsi : ∀ j < min len₁.toNat len₂.toNat,
        ∃ x, t.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * j)) 2 = some x ∧
          BitVec.ofInt 16 x = f j := by
      intro j hj
      have hj_len : 2 * j + 1 < d₂.length := by rw [hl₂, strByteLen_uncompressed hc2]; omega
      refine ⟨Int.ofBytes [d₂[2 * j], d₂[2 * j + 1]], ?_, ?_⟩
      · rw [hdmem]; exact stringAt_load_word (stringsInMem_right hmem) hl₂ hb₂ hj_len
      · rw [word_val_eq_16]
        have hjc : j < (strChars c₂ d₂).length := by rw [strChars_length]; omega
        rw [show f j = (strChars c₂ d₂)[j]'hjc from list_getD_eq_getElem _ j 0#16 hjc]
        rw [strChars_uncompressed_getElem hc2 j hjc,
          list_getD_eq_getElem d₂ (2 * j) 0 (by omega), list_getD_eq_getElem d₂ (2 * j + 1) 0 hj_len]
    have hload_rdi : ∀ j < min len₁.toNat len₂.toNat,
        ∃ y, t.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * j)) 2 = some y ∧
          BitVec.ofInt 16 y = g j := by
      intro j hj
      have hj_len : 2 * j + 1 < d₁.length := by rw [hl₁, strByteLen_uncompressed hc1]; omega
      refine ⟨Int.ofBytes [d₁[2 * j], d₁[2 * j + 1]], ?_, ?_⟩
      · rw [hdmem]; exact stringAt_load_word (stringsInMem_left hmem) hl₁ hb₁ hj_len
      · rw [word_val_eq_16]
        have hjc : j < (strChars c₁ d₁).length := by rw [strChars_length]; omega
        rw [show g j = (strChars c₁ d₁)[j]'hjc from list_getD_eq_getElem _ j 0#16 hjc]
        rw [strChars_uncompressed_getElem hc1 j hjc,
          list_getD_eq_getElem d₁ (2 * j) 0 (by omega), list_getD_eq_getElem d₁ (2 * j + 1) 0 hj_len]
    rcases first_diff_nat (min len₁.toNat len₂.toNat) (fun j => f j = g j) with hall | ⟨k, hk, hpre, hne⟩
    · refine Program.loop_repe_cmpsw_eq (i := 60) rfl hn0 hn64 hdf hrcx_val
        (s.regs.get64 .rsi + 16#64) (s.regs.get64 .rdi + 16#64)
        (by simp [get64_set64, hrsi']) (by simp [get64_set64, hrdi'])
        f g hload_rsi hload_rdi hall ?_
      intro t' ht_mem ht_zmm ht_zf _ _ _ _ ht_regs
      cont; sstep
      simp only [ht_zf, ↓reduceIte, addrOf_label hlab (H := H) (i := 66) rfl]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 66 _ rfl rfl (by decide)
        ⟨ht_mem.trans hdmem, ht_zmm.trans hzmms, ?_, ?_, ?_⟩
      · rw [ht_regs .rsp (by simp)]; simp [get64_set64, hrsp]
      · rw [ht_regs .rax (by simp)]
        have hall_chars : ∀ (j : Nat) (h1 : j < (strChars c₁ d₁).length) (h2 : j < (strChars c₂ d₂).length),
            (strChars c₁ d₁)[j] = (strChars c₂ d₂)[j] := by
          intro j hj1 hj2
          rw [strChars_length] at hj1 hj2
          have hfg := (hall j (by omega)).symm
          dsimp only [f, g] at hfg
          rwa [list_getD_eq_getElem (strChars c₁ d₁) j 0#16 (by rw [strChars_length]; exact hj1),
            list_getD_eq_getElem (strChars c₂ d₂) j 0#16 (by rw [strChars_length]; exact hj2)] at hfg
        have hspec := compareToSpec_prefix hall_chars
        rw [← sub_len_eq_compareToSpec_prefix] at hspec
        simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
          BitVec.zeroExtend, hspec]
      · intro r hr
        have hnot : r ∉ [Reg64.rcx, .rdi, .rsi] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => hr (by simp [h]), fun h => hr (by simp [h]), fun h => hr (by simp [h])⟩
        rw [ht_regs r hnot]
        clear hnot; revert r hr; stub_frame hregs
    · refine Program.loop_repe_cmpsw_ne (i := 60) rfl hk hn64 hdf hrcx_val
        (s.regs.get64 .rsi + 16#64) (s.regs.get64 .rdi + 16#64)
        (by simp [get64_set64, hrsi']) (by simp [get64_set64, hrdi'])
        f g hload_rsi hload_rdi hpre hne ?_
      intro t' ht_mem ht_zmm ht_zf _ _ ht_rsi ht_rdi ht_regs
      cont; sstep
      simp only [ht_zf, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      have hk1 : 2 * k + 1 < d₁.length := by rw [hl₁, strByteLen_uncompressed hc1]; omega
      have hk2 : 2 * k + 1 < d₂.length := by rw [hl₂, strByteLen_uncompressed hc2]; omega
      have hlt1 : (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₁ (by rw [← hl₁]; omega)
      have hlt2 : (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)).toNat < 2 ^ 32 :=
        p_add_16_k_lt hb₂ (by rw [← hl₂]; omega)
      have hload1 : t'.dmem.loadInt (s.regs.get64 .rdi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
          some (Int.ofBytes [d₁[2 * k], d₁[2 * k + 1]]) := by
        rw [ht_mem.trans hdmem]; exact stringAt_load_word (stringsInMem_left hmem) hl₁ hb₁ hk1
      have hload2 : t'.dmem.loadInt (s.regs.get64 .rsi + 16#64 + BitVec.ofNat 64 (2 * k)) 2 =
          some (Int.ofBytes [d₂[2 * k], d₂[2 * k + 1]]) := by
        rw [ht_mem.trans hdmem]; exact stringAt_load_word (stringsInMem_right hmem) hl₂ hb₂ hk2
      simp only [ht_rdi, bit_add_sub_cancel_2, setWidth32_sw64_of_lt hlt1, hload1, word_val_eq_16]
      cont; sstep
      simp only [ht_rsi, bit_add_sub_cancel_2, setWidth32_sw64_of_lt hlt2, hload2, word_val_eq_16]
      cont
      refine count_diff_and_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem
        (ht_mem.trans hdmem) (ht_zmm.trans hzmms) ?_ ?_ ?_
      · simp [get64_set64, ht_regs .rsp (by simp), hrsp]
      · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
          sw32_64]
        have hc1_eq : (d₁[2 * k].toBitVec.zeroExtend 16 |||
              (d₁[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
            ((strChars c₁ d₁)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
          rw [strChars_uncompressed_getElem hc1 k (by rw [strChars_length]; omega),
            list_getD_eq_getElem d₁ (2 * k) 0 (by omega), list_getD_eq_getElem d₁ (2 * k + 1) 0 hk1]
        have hc2_eq : (d₂[2 * k].toBitVec.zeroExtend 16 |||
              (d₂[2 * k + 1].toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 =
            ((strChars c₂ d₂)[k]'(by rw [strChars_length]; omega)).zeroExtend 32 := by
          rw [strChars_uncompressed_getElem hc2 k (by rw [strChars_length]; omega),
            list_getD_eq_getElem d₂ (2 * k) 0 (by omega), list_getD_eq_getElem d₂ (2 * k + 1) 0 hk2]
        rw [hc1_eq, hc2_eq]
        have hpre_chars : ∀ (j : Nat) (hj : j < k),
            (strChars c₁ d₁)[j]'(by rw [strChars_length]; omega) =
            (strChars c₂ d₂)[j]'(by rw [strChars_length]; omega) := by
          intro j hj
          have h1 : j < (strChars c₁ d₁).length := by rw [strChars_length]; omega
          have h2 : j < (strChars c₂ d₂).length := by rw [strChars_length]; omega
          have hfg := (hpre j hj).symm
          dsimp only [f, g] at hfg
          rwa [list_getD_eq_getElem (strChars c₁ d₁) j 0#16 h1,
            list_getD_eq_getElem (strChars c₂ d₂) j 0#16 h2] at hfg
        have hne_chars : (strChars c₁ d₁)[k]'(by rw [strChars_length]; omega) ≠
            (strChars c₂ d₂)[k]'(by rw [strChars_length]; omega) := by
          have h1 : k < (strChars c₁ d₁).length := by rw [strChars_length]; omega
          have h2 : k < (strChars c₂ d₂).length := by rw [strChars_length]; omega
          intro heq; apply hne
          dsimp only [f, g]
          rw [list_getD_eq_getElem (strChars c₁ d₁) k 0#16 h1,
            list_getD_eq_getElem (strChars c₂ d₂) k 0#16 h2, heq.symm]
        exact (compareToSpec_diff (k := k) (by rw [strChars_length]; omega)
          (by rw [strChars_length]; omega) hpre_chars hne_chars).symm
      · intro r hr
        rw [get64_set64, ite_eq_right (fun h => hr (by simp [h])),
          get64_set64, ite_eq_right (fun h => hr (by simp [h]))]
        have hnot : r ∉ [Reg64.rcx, .rdi, .rsi] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => hr (by simp [h]), fun h => hr (by simp [h]), fun h => hr (by simp [h])⟩
        rw [ht_regs r hnot]
        clear hnot; revert r hr; stub_frame hregs

theorem that_compressed_entry (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = true) (hc2 : c₂.getLsbD 0 = false)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms)
    (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
    (hr8 : t.regs.get64 .r8 = (c₁ >>> 1).zeroExtend 64)
    (hr9 : t.regs.get64 .r9 = (c₂ >>> 1).zeroExtend 64)
    (hrdi : t.regs.get64 .rdi = ((s.regs.get64 .rdi + 16#64).setWidth 32).zeroExtend 64)
    (hrsi : t.regs.get64 .rsi = ((s.regs.get64 .rsi + 16#64).setWidth 32).zeroExtend 64)
    (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + 27)⟩ := by
  let len₁ := c₁ >>> 1
  let len₂ := c₂ >>> 1
  have hlen1 : len₁.toNat = (c₁ >>> 1).toNat := rfl
  have hlen2 : len₂.toNat = (c₂ >>> 1).toNat := rfl
  sstep; cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr8, BitVec.zeroExtend, sw32_64]
  cont; sstep
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  rw [cmovg_minLen len₁ len₂ (shr1_msb_false c₁) (shr1_msb_false c₂)]
  cont; sstep
  simp only [minLen_beq_zero len₁ len₂]
  by_cases hmin0 : min len₁.toNat len₂.toNat = 0
  · simp only [decide_eq_true hmin0, ↓reduceIte, addrOf_label hlab (H := H) (i := 41) rfl]
    cont
    refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 41 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
    · simp [get64_set64, hrsp]
    · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
        BitVec.zeroExtend, min_zero_spec hmin0]
    · stub_frame hregs
  · simp only [decide_eq_false hmin0, Bool.false_eq_true, ↓reduceIte]
    cont
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = min len₁.toNat len₂.toNat :=
      ⟨min len₁.toNat len₂.toNat - 1, by omega⟩
    have hlt_rdi : (s.regs.get64 .rdi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_uncompressed hc1] at hb₁; exact hb₁) (by omega)
    have hlt_rsi : (s.regs.get64 .rsi + 16#64).toNat < 2 ^ 32 :=
      p_add_16_lt (by rw [strByteLen_compressed hc2] at hb₂; exact hb₂) (by omega)
    refine that_compressed_loop hlab H s c₁ c₂ d₁ d₂ R ra hra hmem hl₁ hl₂ hc1 hc2 hb₁ hb₂ m 0 _
      (by omega) hdmem hzmms ?_ ?_ ?_ ?_ ?_ ?_ (fun _ hj => absurd hj (Nat.not_lt_zero _))
    · simp [get64_set64, hrsp]
    · simp [get64_set64]
    · simp only [get64_set64, ↓reduceIte, ← hm]
      apply BitVec.eq_of_toNat_eq
      have hlt32 : m + 1 < 2 ^ 32 := by have := ushiftRight1_lt c₁; omega
      have hlt64 : m + 1 < 2 ^ 64 := by omega
      simp [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hlt64]
    · simp [get64_set64, hrdi, setWidth32_ze64_of_lt hlt_rdi]
    · simp [get64_set64, hrsi, setWidth32_ze64_of_lt hlt_rsi]
    · stub_frame hregs

theorem this_compressed_entry (hlab : LabelsPlaced)
    (H : Embedding stringCompareToStubProg)
    (s t : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hra : stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem)
    (hl₁ : d₁.length = strByteLen c₁) (hl₂ : d₂.length = strByteLen c₂)
    (hc1 : c₁.getLsbD 0 = false)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (hdmem : t.dmem = s.dmem) (hzmms : t.zmms = s.zmms) (hdf : t.status.df = false)
    (hrsp : t.regs.get64 .rsp = s.regs.get64 .rsp)
    (hr8 : t.regs.get64 .r8 = (c₁ >>> 1).zeroExtend 64)
    (hr9 : t.regs.get64 .r9 = c₂.zeroExtend 64)
    (hrdi : t.regs.get64 .rdi = ((s.regs.get64 .rdi + 16#64).setWidth 32).zeroExtend 64)
    (hrsi : t.regs.get64 .rsi = ((s.regs.get64 .rsi + 16#64).setWidth 32).zeroExtend 64)
    (hregs : ∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) :
    Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
      ⟨t, Host.addrOf (H.start + 9)⟩ := by
  sstep; cont; sstep
  intro _
  simp only [hr9, BitVec.zeroExtend, sw32_64]
  cont; sstep
  by_cases hc2 : c₂.getLsbD 0 = true
  · simp only [hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    let len₁ := c₁ >>> 1
    let len₂ := c₂ >>> 1
    have hlen1 : len₁.toNat = (c₁ >>> 1).toNat := rfl
    have hlen2 : len₂.toNat = (c₂ >>> 1).toNat := rfl
    cont; sstep
    simp only [hr8, BitVec.zeroExtend, sw32_64]
    cont; sstep
    cont; sstep
    simp only [hr8, BitVec.zeroExtend, sw32_64]
    cont; sstep
    rw [cmovg_minLen len₁ len₂ (shr1_msb_false c₁) (shr1_msb_false c₂)]
    cont; sstep
    simp only [minLen_beq_zero len₁ len₂]
    by_cases hmin0 : min len₁.toNat len₂.toNat = 0
    · simp only [decide_eq_true hmin0, ↓reduceIte, addrOf_label hlab (H := H) (i := 25) rfl]
      cont
      refine stub_ret H s _ c₁ c₂ d₁ d₂ R ra hra hmem 25 _ rfl rfl (by decide) ⟨hdmem, hzmms, ?_, ?_, ?_⟩
      · simp [get64_set64, hrsp]
      · simp only [get64_set64, (by decide : Reg64.rax ≠ .rcx), ↓reduceIte,
          BitVec.zeroExtend, min_zero_spec hmin0]
      · stub_frame hregs
    · simp only [decide_eq_false hmin0, Bool.false_eq_true, ↓reduceIte]
      cont
      obtain ⟨m, hm⟩ : ∃ m, m + 1 = min len₁.toNat len₂.toNat :=
        ⟨min len₁.toNat len₂.toNat - 1, by omega⟩
      have hlt_rdi : (s.regs.get64 .rdi + 16#64).toNat < 2 ^ 32 :=
        p_add_16_lt (by rw [strByteLen_compressed hc1] at hb₁; exact hb₁) (by omega)
      have hlt_rsi : (s.regs.get64 .rsi + 16#64).toNat < 2 ^ 32 :=
        p_add_16_lt (by rw [strByteLen_uncompressed hc2] at hb₂; exact hb₂) (by omega)
      refine this_compressed_loop hlab H s c₁ c₂ d₁ d₂ R ra hra hmem hl₁ hl₂ hc1 hc2 hb₁ hb₂ m 0 _
        (by omega) hdmem hzmms ?_ ?_ ?_ ?_ ?_ ?_ (fun _ hj => absurd hj (Nat.not_lt_zero _))
      · simp [get64_set64, hrsp]
      · simp [get64_set64]
      · simp only [get64_set64, ↓reduceIte, ← hm]
        apply BitVec.eq_of_toNat_eq
        have hlt32 : m + 1 < 2 ^ 32 := by have := ushiftRight1_lt c₁; omega
        have hlt64 : m + 1 < 2 ^ 64 := by omega
        simp [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hlt64]
      · simp [get64_set64, hrdi, setWidth32_ze64_of_lt hlt_rdi]
      · simp [get64_set64, hrsi, setWidth32_ze64_of_lt hlt_rsi]
      · stub_frame hregs
  · have hc2f : c₂.getLsbD 0 = false := Bool.eq_false_iff.mpr hc2
    simp only [hc2f, addrOf_label hlab (H := H) (i := 43) rfl]
    cont
    refine both_compressed_entry hlab H s _ c₁ c₂ d₁ d₂ R ra hra hmem hl₁ hl₂ hc1 hc2f hb₁ hb₂
      hdmem hzmms hdf ?_ ?_ ?_ ?_ ?_ ?_
    · simp [get64_set64, hrsp]
    · simp [get64_set64, hr8]
    · simp [get64_set64]
    · simp [get64_set64, hrdi]
    · simp [get64_set64, hrsi]
    · stub_frame hregs

end

end StubProof

open StubProof

public theorem stringCompareToStub_correct [Host]
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (s : MachineData) (c₁ c₂ : BitVec 32) (d₁ d₂ : List UInt8)
    (R : Mem 64 → Prop) (ra : Int64)
    (hd₁ : d₁.length = strByteLen c₁) (hd₂ : d₂.length = strByteLen c₂)
    (hb₁ : (s.regs.get64 .rdi).toNat + 16 + allocatedBytes (strByteLen c₁) ≤ 2 ^ 32)
    (hb₂ : (s.regs.get64 .rsi).toNat + 16 + allocatedBytes (strByteLen c₂) ≤ 2 ^ 32)
    (hdf : s.status.df = false)
    (hra : ∀ (H : Embedding stringCompareToStubProg), stringCompareToStubProg.IsOutside H ra)
    (hmem : (StringsInMem (s.regs.get64 .rdi) (s.regs.get64 .rsi) c₁ c₂ d₁ d₂
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R)) s.dmem) :
    ⦃ fun s₀ => s₀ = s ⦄
    stringCompareToStubProg
    ⦃ fun _ _ => False ;
      fun pc t => pc = ra ∧
        t.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        t.regs.get64 .rax = (compareToSpec (strChars c₁ d₁) (strChars c₂ d₂)).zeroExtend 64 ∧
        (∀ r, r ∉ [Reg64.rax, .rcx, .rdi, .rsi, .r8, .r9, .rsp] → t.regs.get64 r = s.regs.get64 r) ∧
        t.dmem = s.dmem ∧ t.zmms = s.zmms ⦄ := by
  rw [Program.triple_iff]
  rintro s₀ hs₀
  rw [hs₀]
  apply Program.wp_of_loop
  intro H
  change Program.Loop stringCompareToStubProg H (fun _ => False) (StubPost s c₁ c₂ d₁ d₂ ra)
    ⟨s, Host.addrOf (H.start + 0)⟩
  have hlt1_8 : (s.regs.get64 .rdi + 8#64).toNat < 2 ^ 32 := p_add_8_lt hb₁
  have hlt2_8 : (s.regs.get64 .rsi + 8#64).toNat < 2 ^ 32 := p_add_8_lt hb₂
  have hload_c1 : s.dmem.loadInt (s.regs.get64 .rdi + 8#64) 4 =
      some (Int.ofBytes (Int.toBytes 4 c₁.toInt)) :=
    stringAt_load_count (stringsInMem_left hmem)
  have hload_c2 : s.dmem.loadInt (s.regs.get64 .rsi + 8#64) 4 =
      some (Int.ofBytes (Int.toBytes 4 c₂.toInt)) :=
    stringAt_load_count (stringsInMem_right hmem)
  sstep
  simp only [setWidth32_sw64_of_lt hlt1_8, hload_c1, cnt_val]
  cont; sstep
  simp only [setWidth32_sw64_of_lt hlt2_8, hload_c2, cnt_val]
  cont; sstep
  cont; sstep
  cont; sstep
  intro _
  cont; sstep
  by_cases hc1 : c₁.getLsbD 0 = true
  · simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cont; sstep
    intro _
    cont; sstep
    by_cases hc2 : c₂.getLsbD 0 = true
    · simp only [hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cont; sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 54) rfl]
      cont
      refine both_not_compressed_entry hlab H s _ c₁ c₂ d₁ d₂ R ra (hra H) hmem hd₁ hd₂
        hc1 hc2 hb₁ hb₂ rfl rfl hdf ?_ ?_ ?_ ?_ ?_ ?_
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · stub_frame (fun _ _ => rfl)
    · have hc2f : c₂.getLsbD 0 = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2f, addrOf_label hlab (H := H) (i := 27) rfl]
      cont
      refine that_compressed_entry hlab H s _ c₁ c₂ d₁ d₂ R ra (hra H) hmem hd₁ hd₂
        hc1 hc2f hb₁ hb₂ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · simp [get64_set64]
      · stub_frame (fun _ _ => rfl)
  · have hc1f : c₁.getLsbD 0 = false := Bool.eq_false_iff.mpr hc1
    simp only [hc1f, addrOf_label hlab (H := H) (i := 9) rfl]
    cont
    refine this_compressed_entry hlab H s _ c₁ c₂ d₁ d₂ R ra (hra H) hmem hd₁ hd₂
      hc1f hb₁ hb₂ rfl rfl hdf ?_ ?_ ?_ ?_ ?_ ?_
    · simp [get64_set64]
    · simp [get64_set64]
    · simp [get64_set64]
    · simp [get64_set64]
    · simp [get64_set64]
    · stub_frame (fun _ _ => rfl)

end Kraken.X64.Art
