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
public import Kraken.X64.Art.StringIndexOfSpec

open Std
open Std.WP
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/--
Parameterized assembly template for the baseline (non-AVX2) `String.indexOf(ch)` lowering in ART,
using `repne scasb` / `repne scasw` (`start_at_zero = true`).
Fixed registers:
- `string_obj` = `%rdi`
- `search_value` = `%rax`
- `counter` = `%rcx`
- `out` = `%rdi`
- `string_length` = `len` (e.g. `%rdx`)
- TMP = `tmp` (e.g. `%r11`)
-/
def stringIndexOfRepProg (slow : Label) (len tmp : Reg64) : _root_.Program := parse("
    # 0. Check code point > 0xFFFF:
    cmpl $65535, %eax
    ❰.instr (.regular .W64 .W64 (.jcc .a slow))❱

    # 2. Load count_
    movl 8(%rdi), %❰.low len .W32❱

    testl %❰.low len .W32❱, %❰.low len .W32❱                # 3
    je not_found                                            # 4

    movl %❰.low len .W32❱, %❰.low tmp .W32❱                 # 5
    shrl $1, %❰.low len .W32❱                               # 6

    movl %❰.low len .W32❱, %ecx                             # 7
    addq $16, %rdi                                          # 8

    testl $1, %❰.low tmp .W32❱                              # 9
    jne uncompressed                                        # 10

    cmpl $127, %eax                                         # 11
    jg not_found                                            # 12
    repne scasb                                             # 13
    jmp cmp_done                                            # 14

  uncompressed:                                             # 15
    repne scasw                                             # 16

  cmp_done:                                                 # 17
    jne not_found                                           # 18

    subl %ecx, %❰.low len .W32❱                             # 19
    # 20. leal -1(string_length), out
    lea -1(%❰len❱), %edi
    jmp done                                                # 21

  not_found:                                                # 22
    movl $-1, %edi                                          # 23

  done:                                                     # 24
")

/--
Parameterized assembly template for the baseline (non-AVX2) `String.indexOf(ch, fromIndex)` lowering in ART,
using `repne scasb` / `repne scasw` (`start_at_zero = false`).
-/
def stringIndexOfAfterRepProg (slow : Label) (len tmp start_idx : Reg64) : _root_.Program := parse("
    # 0. Check code point > 0xFFFF:
    cmpl $65535, %eax
    ❰.instr (.regular .W64 .W64 (.jcc .a slow))❱

    # 2. Load count_
    movl 8(%rdi), %❰.low len .W32❱

    testl %❰.low len .W32❱, %❰.low len .W32❱                # 3
    je not_found                                            # 4

    movl %❰.low len .W32❱, %❰.low tmp .W32❱                 # 5
    shrl $1, %❰.low len .W32❱                               # 6

    cmpl %❰.low len .W32❱, %❰.low start_idx .W32❱           # 7
    jge not_found                                           # 8

    xorl %ecx, %ecx                                         # 9
    cmpl $0, %❰.low start_idx .W32❱                         # 10
    # 11. cmovg start_idx, counter (32-bit cmovg)
    cmovg %❰.low start_idx .W32❱, %ecx

    testl $1, %❰.low tmp .W32❱                              # 12
    jne offset_uncompressed                                 # 13

    # 14. leaq 16(%rdi, %rcx, 1), %rdi
    lea 16(%rdi,%rcx,1), %rdi
    jmp modify_counter                                      # 15

  offset_uncompressed:                                      # 16
    # 17. leaq 16(%rdi, %rcx, 2), %rdi
    lea 16(%rdi,%rcx,2), %rdi

  modify_counter:                                           # 18
    negq %rcx                                               # 19
    # 20. leaq (%len, %rcx, 1), %rcx
    lea (%❰len❱,%rcx,1), %rcx

    testl $1, %❰.low tmp .W32❱                              # 21
    jne uncompressed                                        # 22

    cmpl $127, %eax                                         # 23
    jg not_found                                            # 24
    repne scasb                                             # 25
    jmp cmp_done                                            # 26

  uncompressed:                                             # 27
    repne scasw                                             # 28

  cmp_done:                                                 # 29
    jne not_found                                           # 30

    subl %ecx, %❰.low len .W32❱                             # 31
    # 32. leal -1(%len), %edi
    lea -1(%❰len❱), %edi
    jmp done                                                # 33

  not_found:                                                # 34
    movl $-1, %edi                                          # 35

  done:                                                     # 36
")

theorem post_of (len tmp : Reg64) (ymm1 ymm2 : AvxReg .W256)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (s t : MachineData) (res : BitVec 32)
    (hres : indexOfSpec chars ch fromIndex = res)
    (hv : t.regs.get (.low .rdi .W32) = res)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s t := by
  refine ⟨by rw [hv, hres], ?_, hm, Or.inl hz⟩
  intro r hr_not
  apply hr
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hr_not (by simp)
  · exact hr_not (by simp)
  · exact hr_not (by simp)
  · exact hr_not (by simp)

theorem post_of_after (len tmp start_idx : Reg64) (ymm1 ymm2 : AvxReg .W256)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (s t : MachineData) (res : BitVec 32)
    (hres : indexOfSpec chars ch fromIndex = res)
    (hv : t.regs.get (.low .rdi .W32) = res)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s t := by
  refine ⟨by rw [hv, hres], ?_, hm, Or.inl hz⟩
  intro r hr_not
  apply hr
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hr_not (by simp)
  · exact hr_not (by simp)
  · exact hr_not (by simp)
  · exact hr_not (by simp)

open Proof

macro "cont_rep" : tactic => `(tactic| refine Program.loopCont_of_le (by simp [stringIndexOfRepProg]) ?_)
macro "cont_after_rep" : tactic => `(tactic| refine Program.loopCont_of_le (by simp [stringIndexOfAfterRepProg]) ?_)

theorem ofNat64_succ_sub_one (m : Nat) : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem ofNat64_eq_zero {m : Nat} (hm : m < 2 ^ 64) : (BitVec.ofNat 64 m == 0#64) = (m == 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 m ≠ 0#64 := fun h' => h (by
      have := congrArg BitVec.toNat h'; simp at this; omega)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem regs_scas_step_rdi (regs : Reg64s) (k : Nat) (A : BitVec 64) (v_rcx : BitVec 64)
    (hrdi : regs.get64 .rdi = A + 16#64 + .ofNat 64 k) :
    ((regs.set (Reg.low .rdi .W64) (regs.get (Reg.low .rdi .W64) + 1#64)).set64 .rcx v_rcx).get64 .rdi =
      A + 16#64 + .ofNat 64 (k + 1) := by
  simp only [set_low64, get_low64, get64_set64]
  have : Reg64.rdi ≠ Reg64.rcx := by decide
  simp only [this, ↓reduceIte]
  rw [hrdi, BitVec.ofNat_add]
  ac_rfl

theorem regs_scasw_step_rdi (regs : Reg64s) (k : Nat) (A : BitVec 64) (v_rcx : BitVec 64)
    (hrdi : regs.get64 .rdi = A + 16#64 + .ofNat 64 (2 * k)) :
    ((regs.set (Reg.low .rdi .W64) (regs.get (Reg.low .rdi .W64) + 2#64)).set64 .rcx v_rcx).get64 .rdi =
      A + 16#64 + .ofNat 64 (2 * (k + 1)) := by
  simp only [set_low64, get_low64, get64_set64]
  have : Reg64.rdi ≠ Reg64.rcx := by decide
  simp only [this, ↓reduceIte]
  rw [hrdi]
  have : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [this, BitVec.ofNat_add]
  ac_rfl

theorem regs_scas_frame (regs : Reg64s) (v_rdi v_rcx : BitVec 64) (r : Reg64)
    (hr : r ∉ [Reg64.rdi, Reg64.rcx]) :
    ((regs.set64 .rdi v_rdi).set64 .rcx v_rcx).get64 r = regs.get64 r := by
  have h1 : r ≠ .rcx := by intro h; subst h; simp at hr
  have h2 : r ≠ .rdi := by intro h; subst h; simp at hr
  rw [get64_set64, get64_set64]
  simp [h1, h2]

theorem setWidth32_ofNat64 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h64 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hn]

theorem ofNat32_sub_one {T : Nat} (h0 : 0 < T) :
    BitVec.ofNat 32 (T - 1) = BitVec.ofNat 32 T - 1#32 := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have : T' + 1 - 1 = T' := by omega
  rw [this]
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem ofNat32_sub_sub {T m : Nat} (h0 : m + 1 ≤ T) :
    BitVec.ofNat 32 (T - m - 1) = BitVec.ofNat 32 T - BitVec.ofNat 32 m - 1#32 := by
  obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 + m := ⟨T - m - 1, by omega⟩
  have : k + 1 + m - m - 1 = k := by omega
  rw [this]
  have hT : BitVec.ofNat 32 (k + 1 + m) = BitVec.ofNat 32 (k + 1) + BitVec.ofNat 32 m := by
    rw [BitVec.ofNat_add]
  rw [hT, BitVec.add_sub_cancel, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem string_info_of {s : MachineData} {str : Reg64} {c : BitVec 32} {d : List UInt8}
    {R : Mem 64 → Prop} (hmem : (StringAt (s.regs.get64 str) c d ⋆ R) s.dmem)
    (hl : d.length = strByteLen c) :
    let A := s.regs.get64 str
    let T := strByteLen c
    (∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome) ∧
    (∀ i < T, byteAt s.dmem A i = d.getD i 0) := by
  intro A T
  have hL := strByteLen_lt c
  have hpl : (padded d).length = strByteLen c + padBytes (strByteLen c) := by simp [hl]
  have hpad : padBytes (strByteLen c) < 8 := by unfold padBytes; omega
  have dA : ∀ i (hi : i < strByteLen c + padBytes (strByteLen c)),
      s.dmem[A + 16#64 + .ofNat 64 i]? = some ((padded d)[i]'(by omega)) :=
    fun i hi => sep_get_l hmem (fun _ h => stringAt_data (by omega) (by omega) _ h)
  constructor
  · intro i hi
    have hpad' : i < strByteLen c + padBytes (strByteLen c) := by omega
    simp [dA i hpad']
  · intro i hi
    have hpad' : i < strByteLen c + padBytes (strByteLen c) := by omega
    simp only [byteAt, dA i hpad', Option.getD_some]
    have h_get : (padded d)[i]'(by omega) = d[i]'(by omega) := List.getElem_append_left (by omega)
    rw [h_get]
    have : d.getD i 0 = d[i]'(by omega) := by
      change d[i]?.getD 0 = d[i]'(by omega)
      rw [List.getElem?_eq_getElem (by omega)]
      rfl
    rw [this]


theorem ret_slow [Host] (slow : Label) (len tmp : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (chars : List (BitVec 16)) (fromIndex : BitVec 32)
    (H : Embedding (stringIndexOfRepProg slow len tmp)) (s t : MachineData)
    (ch : BitVec 32) (h_ch : ch.toNat > 65535)
    (h_rax : t.regs.get (Reg.low Reg64.rax Width.W32) = ch)
    (h_regs : t.regs = s.regs)
    (h_mem : t.dmem = s.dmem)
    (h_zmms : t.zmms = s.zmms)
    (hslow : IsSlowPathLabel (stringIndexOfRepProg slow len tmp) H slow) :
    Program.Loop (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 0)⟩ := by
  have h_eq : ch = BitVec.ofNat 32 ch.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ch.isLt]
  have h_cf : (BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned) = false := by
    conv => lhs; rw [h_eq]
    have := cf_ofNat32 (x := ch.toNat) (c := 65535) ch.isLt (by decide)
    rw [this]
    simp only [decide_eq_false_iff_not]
    omega
  have h_zf : (ch - 65535#32 == 0#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  have h_cond : (!BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned &&
      !ch - 65535#32 == 0#32) = true := by
    simp [h_cf, h_zf]
  sstep; cont_rep; sstep
  rw [get_low32] at h_rax
  rw [h_rax, h_cond]
  simp only [↓reduceIte]
  change Program.LoopCont _ _ _ _ ⟨_, label slow⟩
  unfold Program.LoopCont
  by_cases h : label slow = H.endAddr ∨ (stringIndexOfRepProg slow len tmp).IsLabelAddr (label slow) ∨
      (∃ i < (stringIndexOfRepProg slow len tmp).length, label slow = Host.addrOf (H.start + i))
  · exact False.elim (hslow h)
  · simp only [h, ↓reduceIte]
    refine ⟨rfl, h_ch, h_regs, h_mem, h_zmms⟩

theorem ret_slow_after [Host] (slow : Label) (len tmp start_idx : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (chars : List (BitVec 16)) (fromIndex : BitVec 32)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx)) (s t : MachineData)
    (ch : BitVec 32) (h_ch : ch.toNat > 65535)
    (h_rax : t.regs.get (Reg.low Reg64.rax Width.W32) = ch)
    (h_regs : t.regs = s.regs)
    (h_mem : t.dmem = s.dmem)
    (h_zmms : t.zmms = s.zmms)
    (hslow : IsSlowPathLabel (stringIndexOfAfterRepProg slow len tmp start_idx) H slow) :
    Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 0)⟩ := by
  have h_eq : ch = BitVec.ofNat 32 ch.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ch.isLt]
  have h_cf : (BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned) = false := by
    conv => lhs; rw [h_eq]
    have := cf_ofNat32 (x := ch.toNat) (c := 65535) ch.isLt (by decide)
    rw [this]
    simp only [decide_eq_false_iff_not]
    omega
  have h_zf : (ch - 65535#32 == 0#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  have h_cond : (!BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned &&
      !ch - 65535#32 == 0#32) = true := by
    simp [h_cf, h_zf]
  sstep; cont_after_rep; sstep
  rw [get_low32] at h_rax
  rw [h_rax, h_cond]
  simp only [↓reduceIte]
  change Program.LoopCont _ _ _ _ ⟨_, label slow⟩
  unfold Program.LoopCont
  by_cases h : label slow = H.endAddr ∨ (stringIndexOfAfterRepProg slow len tmp start_idx).IsLabelAddr (label slow) ∨
      (∃ i < (stringIndexOfAfterRepProg slow len tmp start_idx).length, label slow = Host.addrOf (H.start + i))
  · exact False.elim (hslow h)
  · simp only [h, ↓reduceIte]
    refine ⟨rfl, h_ch, h_regs, h_mem, h_zmms⟩

theorem ret_not_found [Host] (slow : Label) (len tmp : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (_hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch : BitVec 32)
    (hspec : indexOfSpec chars ch 0#32 = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    Program.Loop (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 22)⟩ := by
  sstep; cont_rep; sstep; cont_rep; sstep; cont_rep
  exact Program.loop_done (post_of len tmp ymm1 ymm2 chars ch 0#32 s _ (-1#32) hspec
    (by simp only [get_low32, set_low32, get64_set64]; rfl) hm (by
      intro r hr_out
      simp only [set_low32, get64_set64]
      by_cases h1 : r = .rdi
      · subst h1; simp at hr_out
      · simp [h1, hr r hr_out]) hz)

theorem ret_not_found_after [Host] (slow : Label) (len tmp start_idx : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (_hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms) :
    Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 34)⟩ := by
  sstep; cont_after_rep; sstep; cont_after_rep; sstep; cont_after_rep
  exact Program.loop_done (post_of_after len tmp start_idx ymm1 ymm2 chars ch fromIndex s _ (-1#32) hspec
    (by simp only [get_low32, set_low32, get64_set64]; rfl) hm (by
      intro r hr_out
      simp only [set_low32, get64_set64]
      by_cases h1 : r = .rdi
      · subst h1; simp at hr_out
      · simp [h1, hr r hr_out]) hz)

theorem subl_leal_eq (A B : BitVec 32) :
    BitVec.setWidth 32
      (BitVec.setWidth 64
        (BitVec.zeroExtend 32
          (BitVec.setWidth 64 (A - B) + -1#64))) =
    A - B - 1#32 := by
  bv_decide

theorem ret_found [Host] (slow : Label) (len tmp : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch : BitVec 32)
    (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch 0#32 = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.Loop (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 19)⟩ := by
  sstep; cont_rep; sstep; cont_rep; sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 24) rfl]
  cont_rep; sstep; cont_rep
  exact Program.loop_done (post_of len tmp ymm1 ymm2 chars ch 0#32 s _ match_idx hspec
    (by
      simp only [get_low32, get64_set64, ↓reduceIte]
      rw [subl_leal_eq]
      rw [← hlen]
      simp only [get_low32]) hm (by
      intro r hr_out
      simp only [get64_set64]
      by_cases h1 : r = .rdi
      · subst h1; simp at hr_out
      · by_cases h2 : r = len
        · subst h2; simp at hr_out
        · simp [h1, h2, hr r hr_out]) hz)

theorem step_match_to_ret_found [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s t : MachineData) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch 0#32 = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = true)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.LoopCont (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 14)⟩ := by
  refine Program.loopCont_of_le (j := 14) (by simp [stringIndexOfRepProg]) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 17) rfl]
  refine Program.loopCont_of_le (j := 17) (by simp [stringIndexOfRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 18) (by simp [stringIndexOfRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 19) (by simp [stringIndexOfRepProg]) ?_
  exact ret_found slow len tmp ymm1 ymm2 hlab H s t chars ch match_idx hspec hm hr hz hlen

theorem step_no_match_to_ret_not_found [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s t : MachineData) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256)
    (hspec : indexOfSpec chars ch 0#32 = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = false) :
    Program.LoopCont (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 14)⟩ := by
  refine Program.loopCont_of_le (j := 14) (by simp [stringIndexOfRepProg]) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 17) rfl]
  refine Program.loopCont_of_le (j := 17) (by simp [stringIndexOfRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 18) (by simp [stringIndexOfRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 22) rfl]
  refine Program.loopCont_of_le (j := 22) (by simp [stringIndexOfRepProg]) ?_
  exact ret_not_found slow len tmp ymm1 ymm2 hlab H s t chars ch hspec hm hr hz

theorem ret_found_after [Host] (slow : Label) (len tmp start_idx : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 31)⟩ := by
  sstep; cont_after_rep; sstep; cont_after_rep; sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 36) rfl]
  cont_after_rep; sstep; cont_after_rep
  exact Program.loop_done (post_of_after len tmp start_idx ymm1 ymm2 chars ch fromIndex s _ match_idx hspec
    (by
      simp only [get_low32, get64_set64, ↓reduceIte]
      rw [subl_leal_eq]
      rw [← hlen]
      simp only [get_low32]) hm (by
      intro r hr_out
      simp only [get64_set64]
      by_cases h1 : r = .rdi
      · subst h1; simp at hr_out
      · by_cases h2 : r = len
        · subst h2; simp at hr_out
        · simp [h1, h2, hr r hr_out]) hz)

theorem step_match_to_ret_found_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s t : MachineData) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = true)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.LoopCont (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 26)⟩ := by
  refine Program.loopCont_of_le (j := 26) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 29) rfl]
  refine Program.loopCont_of_le (j := 29) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 30) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 31) (by simp [stringIndexOfAfterRepProg]) ?_
  exact ret_found_after slow len tmp start_idx ymm1 ymm2 hlab H s t chars ch fromIndex match_idx hspec hm hr hz hlen

theorem step_no_match_to_ret_not_found_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s t : MachineData) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = false) :
    Program.LoopCont (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 26)⟩ := by
  refine Program.loopCont_of_le (j := 26) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 29) rfl]
  refine Program.loopCont_of_le (j := 29) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 30) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 34) rfl]
  refine Program.loopCont_of_le (j := 34) (by simp [stringIndexOfAfterRepProg]) ?_
  exact ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s t chars ch fromIndex hspec hm hr hz

theorem step_from_cmp_done_match_to_ret_found [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s t : MachineData) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch 0#32 = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = true)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.LoopCont (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 17)⟩ := by
  refine Program.loopCont_of_le (j := 17) (by simp [stringIndexOfRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 18) (by simp [stringIndexOfRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 19) (by simp [stringIndexOfRepProg]) ?_
  exact ret_found slow len tmp ymm1 ymm2 hlab H s t chars ch match_idx hspec hm hr hz hlen

theorem step_from_cmp_done_no_match_to_ret_not_found [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s t : MachineData) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256)
    (hspec : indexOfSpec chars ch 0#32 = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = false) :
    Program.LoopCont (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 17)⟩ := by
  refine Program.loopCont_of_le (j := 17) (by simp [stringIndexOfRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 18) (by simp [stringIndexOfRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 22) rfl]
  refine Program.loopCont_of_le (j := 22) (by simp [stringIndexOfRepProg]) ?_
  exact ret_not_found slow len tmp ymm1 ymm2 hlab H s t chars ch hspec hm hr hz

theorem scasw_zero [Host] (slow : Label) (len tmp : Reg64) (ymm1 ymm2 : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch : BitVec 32)
    (hspec : indexOfSpec chars ch 0#32 = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (hzf : t.status.zf = false)
    (hrcx0 : t.regs.get64 .rcx = 0#64) :
    Program.Loop (stringIndexOfRepProg slow len tmp) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 16)⟩ := by
  refine Program.loop_repne_scasw_zero (i := 16) rfl hrcx0 ?_
  refine Program.loopCont_of_le (j := 17) (by simp [stringIndexOfRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 18) (by simp [stringIndexOfRepProg]) ?_
  sstep
  rw [hzf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 22) rfl]
  refine Program.loopCont_of_le (j := 22) (by simp [stringIndexOfRepProg]) ?_
  exact ret_not_found slow len tmp ymm1 ymm2 hlab H s t chars ch hspec hm hr hz

theorem scasw_loop [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s : MachineData) (A : BitVec 64) (T : Nat) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (d : List UInt8)
    (h_ch : ch.toNat ≤ 65535)
    (h_T_lt : T < 2 ^ 32 - 1)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_chars : ∀ (i : Nat) (hi : i < chars.length), chars.get ⟨i, hi⟩ = (d.getD (2 * i) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8))
    (h_len : chars.length = T)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hm_mem : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms)
      (hdf : t.status.df = false)
      (hrcx : t.regs.get64 .rcx = .ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = A + 16#64 + .ofNat 64 (2 * k))
      (hrax : t.regs.get (Reg.low .rax .W16) = ch.setWidth 16)
      (hlen_reg : t.regs.get (.low len .W32) = .ofNat 32 T)
      (hk : k + (m + 1) = T)
      (hpre : ∀ (i : Nat) (hi : i < k), (chars.get ⟨i, by omega⟩).zeroExtend 32 ≠ ch)
      (h_distinct : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup),
      Program.Loop (stringIndexOfRepProg slow len tmp) H
        (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 16)⟩ := by
  induction m with
  | zero =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    have hne0 : (BitVec.ofNat 64 1 == 0#64) = false := rfl
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_word_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = 0#64 := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx]; rfl
    have h_word_val : BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) =
        (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
      rw [h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega), word_of_bytes]
    by_cases heq : (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) = ch.setWidth 16
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) == 0#16) = true := by
        rw [sub_beq_zero, hrax, h_word_val, heq, beq_self_eq_true]
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch := by
        rw [h_chars k (by omega)]
        exact (word_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch 0#32 = BitVec.ofNat 32 k := by
        have := indexOfSpec_eq_some (chars := chars) (ch := ch) (fromIndex := 0#32) k (by simp [h_len]; omega)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide,
          Nat.zero_add] at this
        apply this
        · exact h_char_k
        · intro i hi
          exact hpre i hi
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 17)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = 0#32 := by
        simp only [get_low32]
        rw [hrcx_eval]; rfl
      have hlen_calc : .ofNat 32 T - 0#32 - 1#32 = BitVec.ofNat 32 k := by
        have : k = T - 1 := by omega
        rw [this]
        have h_pos : 0 < T := by omega
        rw [BitVec.sub_zero, ← ofNat32_sub_one h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 k := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_from_cmp_done_match_to_ret_found slow len tmp hlab H s _ chars ch ymm1 ymm2 (.ofNat 32 k) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 16 ≠ (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) == 0#16) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_word_val]
        exact hne_symm
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 ≠ ch := by
        rw [h_chars k (by omega)]
        intro h
        have := (word_eq_iff _ ch h_ch).mp h
        exact heq this
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64) = 0#64 := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx]; rfl
      have h_count_zero : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64 != 0#64) = false) := by
        rw [h_val_rcx]; rfl
      rw [hzf_false, h_count_zero]
      simp only [Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 17)⟩
      have hspec : indexOfSpec chars ch 0#32 = -1#32 := by
        have := indexOfSpec_eq_none (chars := chars) (ch := ch) (fromIndex := 0#32)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide] at this
        apply this
        intro i hi
        have : (chars.drop 0) = chars := rfl
        rw [this] at hi
        rw [h_len] at hi
        have : i < k ∨ i = k := by omega
        rcases this with h_lt | rfl
        · exact hpre i h_lt
        · exact h_char_k
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      exact step_from_cmp_done_no_match_to_ret_not_found slow len tmp hlab H s _ chars ch ymm1 ymm2 hspec hm_mem hr_step hz rfl
  | succ m' ih =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == 0#64) = false := by
      simp [ofNat64_eq_zero (show m' + 1 + 1 < 2 ^ 64 by omega)]
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_word_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = .ofNat 64 (m' + 1) := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx, ofNat64_succ_sub_one]
    have h_word_val : BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) =
        (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
      rw [h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega), word_of_bytes]
    by_cases heq : (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) = ch.setWidth 16
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) == 0#16) = true := by
        rw [sub_beq_zero, hrax, h_word_val, heq, beq_self_eq_true]
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch := by
        rw [h_chars k (by omega)]
        exact (word_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch 0#32 = BitVec.ofNat 32 k := by
        have := indexOfSpec_eq_some (chars := chars) (ch := ch) (fromIndex := 0#32) k (by simp [h_len]; omega)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide,
          Nat.zero_add] at this
        apply this
        · exact h_char_k
        · intro i hi
          exact hpre i hi
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 17)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = .ofNat 32 (m' + 1) := by
        simp only [get_low32]
        rw [hrcx_eval, setWidth32_ofNat64 _ (by omega)]
      have hlen_calc : .ofNat 32 T - .ofNat 32 (m' + 1) - 1#32 = BitVec.ofNat 32 k := by
        have : k = T - (m' + 1) - 1 := by omega
        rw [this]
        have h_pos : (m' + 1) + 1 ≤ T := by omega
        rw [ofNat32_sub_sub h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 k := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_from_cmp_done_match_to_ret_found slow len tmp hlab H s _ chars ch ymm1 ymm2 (.ofNat 32 k) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 16 ≠ (d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8) := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) == 0#16) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_word_val]
        exact hne_symm
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 ≠ ch := by
        rw [h_chars k (by omega)]
        intro h
        have := (word_eq_iff _ ch h_ch).mp h
        exact heq this
      have hne_zero : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
        rw [bne_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64) = BitVec.ofNat 64 (m' + 1) := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx, ofNat64_succ_sub_one]
      have h_val_rcx_ne : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64 != 0#64) = true) := by
        rw [h_val_rcx, hne_zero]
      rw [hzf_false, h_val_rcx_ne]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 16)⟩
      refine Program.loopCont_of_le (j := 16) (by simp [stringIndexOfRepProg]) ?_
      have hrdi' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get64 Reg64.rdi = A + 16#64 + BitVec.ofNat 64 (2 * (k + 1)) := by
        exact regs_scasw_step_rdi _ _ _ _ hrdi
      have hrax' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get (Reg.low .rax .W16) = ch.setWidth 16 := by
        have : Reg64.rax ≠ .rcx := by decide
        have : Reg64.rax ≠ .rdi := by decide
        simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, this, ↓reduceIte]
        exact hrax
      have hlen_reg' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      exact ih (k + 1) _ hm_mem
        (fun r hr_out => by
          have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          simp only [get64_set64, set_low64, get_low64, h1, h2, ↓reduceIte]
          exact hr r hr_out) hz rfl
        hrcx_eval hrdi' hrax' hlen_reg' (by omega)
        (fun i hi => by
          have : i < k ∨ i = k := by omega
          rcases this with h_lt | rfl
          · exact hpre i h_lt
          · exact h_char_k)
        (by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, by decide⟩)

theorem scasb_loop [Host] (slow : Label) (len tmp : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfRepProg slow len tmp))
    (s : MachineData) (A : BitVec 64) (T : Nat) (chars : List (BitVec 16)) (ch : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (d : List UInt8)
    (h_ascii : ∀ c ∈ chars, c.toNat < 128)
    (h_ch : ch.toNat ≤ 127)
    (h_T_lt : T < 2 ^ 32 - 1)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_chars : ∀ (i : Nat) (hi : i < chars.length), chars.get ⟨i, hi⟩ = (d.getD i 0).toBitVec.zeroExtend 16)
    (h_len : chars.length = T)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hm_mem : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms)
      (hdf : t.status.df = false)
      (hrcx : t.regs.get64 .rcx = .ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = A + 16#64 + .ofNat 64 k)
      (hrax : t.regs.get (Reg.low .rax .W8) = ch.setWidth 8)
      (hlen_reg : t.regs.get (.low len .W32) = .ofNat 32 T)
      (hk : k + (m + 1) = T)
      (hpre : ∀ (i : Nat) (hi : i < k), (chars.get ⟨i, by omega⟩).zeroExtend 32 ≠ ch)
      (h_distinct : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup),
      Program.Loop (stringIndexOfRepProg slow len tmp) H
        (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch 0#32 s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 13)⟩ := by
  induction m with
  | zero =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : k < T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm_mem, load_chunk _ _ k 1 T h_some (by omega)]
      rfl
    have hne0 : (BitVec.ofNat 64 1 == 0#64) = false := rfl
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_byte_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = 0#64 := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx]; rfl
    have h_byte_val : BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) = (d.getD k 0).toBitVec := by
      rw [h_data k hk_lt, ofInt_ofBytes_one]
    by_cases heq : (d.getD k 0).toBitVec = ch.setWidth 8
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) == 0#8) = true := by
        rw [sub_beq_zero, hrax, h_byte_val, heq, beq_self_eq_true]
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch := by
        rw [h_chars k (by omega)]
        exact (byte_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch 0#32 = BitVec.ofNat 32 k := by
        have := indexOfSpec_eq_some (chars := chars) (ch := ch) (fromIndex := 0#32) k (by simp [h_len]; omega)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide,
          Nat.zero_add] at this
        apply this
        · exact h_char_k
        · intro i hi
          exact hpre i hi
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 14)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = 0#32 := by
        simp only [get_low32]
        rw [hrcx_eval, setWidth32_ofNat64 _ (by omega)]
      have hlen_calc : .ofNat 32 T - 0#32 - 1#32 = BitVec.ofNat 32 k := by
        have : k = T - 1 := by omega
        rw [this]
        have h_pos : 0 < T := by omega
        rw [BitVec.sub_zero, ← ofNat32_sub_one h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 k := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      refine step_match_to_ret_found slow len tmp hlab H s _ chars ch ymm1 ymm2 (.ofNat 32 k) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 8 ≠ (d.getD k 0).toBitVec := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) == 0#8) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_byte_val]
        exact hne_symm
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 ≠ ch := by
        rw [h_chars k (by omega)]
        intro h
        have := (byte_eq_iff _ ch h_ch).mp h
        exact heq this
      have hspec : indexOfSpec chars ch 0#32 = -1#32 := by
        have := indexOfSpec_eq_none (chars := chars) (ch := ch) (fromIndex := 0#32)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide] at this
        apply this
        intro i hi
        have : (chars.drop 0) = chars := rfl
        rw [this] at hi
        rw [h_len] at hi
        have : i < k ∨ i = k := by omega
        rcases this with h_lt | rfl
        · exact hpre i h_lt
        · exact h_char_k
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64) = 0#64 := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx]; rfl
      have h_count_zero : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64 != 0#64) = false) := by
        rw [h_val_rcx]; rfl
      rw [hzf_false, h_count_zero]
      simp only [Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 14)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      refine step_no_match_to_ret_not_found slow len tmp hlab H s _ chars ch ymm1 ymm2 hspec hm_mem hr_step hz rfl
  | succ m' ih =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : k < T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm_mem, load_chunk _ _ k 1 T h_some (by omega)]
      rfl
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == 0#64) = false := by
      simp [ofNat64_eq_zero (show m' + 1 + 1 < 2 ^ 64 by omega)]
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_byte_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = .ofNat 64 (m' + 1) := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx, ofNat64_succ_sub_one]
    have h_byte_val : BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) = (d.getD k 0).toBitVec := by
      rw [h_data k hk_lt, ofInt_ofBytes_one]
    by_cases heq : (d.getD k 0).toBitVec = ch.setWidth 8
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) == 0#8) = true := by
        rw [sub_beq_zero, hrax, h_byte_val, heq, beq_self_eq_true]
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch := by
        rw [h_chars k (by omega)]
        exact (byte_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch 0#32 = BitVec.ofNat 32 k := by
        have := indexOfSpec_eq_some (chars := chars) (ch := ch) (fromIndex := 0#32) k (by simp [h_len]; omega)
        simp only [show (if (0#32 : BitVec 32).slt 0 then 0 else (0#32 : BitVec 32).toNat) = 0 by decide,
          Nat.zero_add] at this
        apply this
        · exact h_char_k
        · intro i hi
          exact hpre i hi
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 14)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = .ofNat 32 (m' + 1) := by
        simp only [get_low32]
        rw [hrcx_eval, setWidth32_ofNat64 _ (by omega)]
      have hlen_calc : .ofNat 32 T - .ofNat 32 (m' + 1) - 1#32 = BitVec.ofNat 32 k := by
        have : k = T - (m' + 1) - 1 := by omega
        rw [this]
        have h_pos : (m' + 1) + 1 ≤ T := by omega
        have h_T_lt' : T < 2 ^ 32 := by omega
        rw [ofNat32_sub_sub h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 k := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      refine step_match_to_ret_found slow len tmp hlab H s _ chars ch ymm1 ymm2 (.ofNat 32 k) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 8 ≠ (d.getD k 0).toBitVec := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A k]) == 0#8) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_byte_val]
        exact hne_symm
      have h_char_k : (chars.get ⟨k, by omega⟩).zeroExtend 32 ≠ ch := by
        rw [h_chars k (by omega)]
        intro h
        have := (byte_eq_iff _ ch h_ch).mp h
        exact heq this
      have hne_zero : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
        rw [bne_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64) = BitVec.ofNat 64 (m' + 1) := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx, ofNat64_succ_sub_one]
      have h_val_rcx_ne : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64 != 0#64) = true) := by
        rw [h_val_rcx, hne_zero]
      rw [hzf_false, h_val_rcx_ne]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 13)⟩
      refine Program.loopCont_of_le (j := 13) (by simp [stringIndexOfRepProg]) ?_
      have hrdi' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get64 Reg64.rdi = A + 16#64 + BitVec.ofNat 64 (k + 1) := by
        exact regs_scas_step_rdi _ _ _ _ hrdi
      have hrax' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get (Reg.low .rax .W8) = ch.setWidth 8 := by
        have : Reg64.rax ≠ .rcx := by decide
        have : Reg64.rax ≠ .rdi := by decide
        simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, ↓reduceIte]
        exact hrax
      have hlen_reg' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      exact ih (k + 1) _ hm_mem
        (fun r hr_out => by
          have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          simp only [get64_set64, set_low64, get_low64, h1, h2, ↓reduceIte]
          exact hr r hr_out) hz rfl
        hrcx_eval hrdi' hrax' hlen_reg' (by omega)
        (fun i hi => by
          have : i < k ∨ i = k := by omega
          rcases this with h_lt | rfl
          · exact hpre i h_lt
          · exact h_char_k)
        (by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, by decide⟩)

theorem step_from_cmp_done_match_to_ret_found_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s t : MachineData) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (match_idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = match_idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = true)
    (hlen : t.regs.get (.low len .W32) - t.regs.get (.low .rcx .W32) - 1#32 = match_idx) :
    Program.LoopCont (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 29)⟩ := by
  refine Program.loopCont_of_le (j := 29) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 30) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 31) (by simp [stringIndexOfAfterRepProg]) ?_
  exact ret_found_after slow len tmp start_idx ymm1 ymm2 hlab H s t chars ch fromIndex match_idx hspec hm hr hz hlen

theorem step_from_cmp_done_no_match_to_ret_not_found_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s t : MachineData) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (h_zf : t.status.zf = false) :
    Program.LoopCont (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 29)⟩ := by
  refine Program.loopCont_of_le (j := 29) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 30) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  rw [h_zf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 34) rfl]
  refine Program.loopCont_of_le (j := 34) (by simp [stringIndexOfAfterRepProg]) ?_
  exact ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s t chars ch fromIndex hspec hm hr hz

theorem scasb_loop_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s : MachineData) (A : BitVec 64) (T start_val : Nat) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (d : List UInt8)
    (h_ascii : ∀ c ∈ chars, c.toNat < 128)
    (h_ch : ch.toNat ≤ 127)
    (h_T_lt : T < 2 ^ 32 - 1)
    (h_start_val : start_val = (if fromIndex.slt 0 then 0 else fromIndex.toNat))
    (h_start_lt : start_val < T)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_chars : ∀ (i : Nat) (hi : i < chars.length), chars.get ⟨i, hi⟩ = (d.getD i 0).toBitVec.zeroExtend 16)
    (h_len : chars.length = T)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hm_mem : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms)
      (hdf : t.status.df = false)
      (hrcx : t.regs.get64 .rcx = .ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = A + 16#64 + .ofNat 64 (start_val + k))
      (hrax : t.regs.get (Reg.low .rax .W8) = ch.setWidth 8)
      (hlen_reg : t.regs.get (.low len .W32) = .ofNat 32 T)
      (hk : k + (m + 1) = T - start_val)
      (hpre : ∀ (i : Nat) (hi : i < k), ((chars.drop start_val).get ⟨i, by
        have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
        omega⟩).zeroExtend 32 ≠ ch)
      (h_distinct : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup),
      Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
        (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 25)⟩ := by
  induction m with
  | zero =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : start_val + k < T := by omega
    have haddr : A + 16#64 + .ofNat 64 (start_val + k) = A + .ofNat 64 (start_val + k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (start_val + k)) 1 =
        some (Int.ofBytes [byteAt s.dmem A (start_val + k)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (start_val + k) 1 T h_some (by omega)]
      rfl
    have hne0 : (BitVec.ofNat 64 1 == 0#64) = false := rfl
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_byte_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = 0#64 := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx]; rfl
    have h_byte_val : BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) = (d.getD (start_val + k) 0).toBitVec := by
      rw [h_data (start_val + k) hk_lt, ofInt_ofBytes_one]
    by_cases heq : (d.getD (start_val + k) 0).toBitVec = ch.setWidth 8
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) == 0#8) = true := by
        rw [sub_beq_zero, hrax, h_byte_val, heq, beq_self_eq_true]
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 = ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        exact (byte_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (start_val + k) := by
        dsimp only [indexOfSpec]
        rw [← h_start_val]
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop start_val) k (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 26)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = 0#32 := by
        simp only [get_low32]
        rw [hrcx_eval]; rfl
      have hlen_calc : .ofNat 32 T - 0#32 - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        have : start_val + k = T - 1 := by omega
        rw [this]
        have h_pos : 0 < T := by omega
        rw [BitVec.sub_zero, ← ofNat32_sub_one h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_match_to_ret_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 (.ofNat 32 (start_val + k)) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 8 ≠ (d.getD (start_val + k) 0).toBitVec := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) == 0#8) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_byte_val]
        exact hne_symm
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 ≠ ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        intro h
        have := (byte_eq_iff _ ch h_ch).mp h
        exact heq this
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64) = 0#64 := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx]; rfl
      have h_count_zero : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64 != 0#64) = false) := by
        rw [h_val_rcx]; rfl
      rw [hzf_false, h_count_zero]
      simp only [Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 26)⟩
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        have := indexOfSpec_eq_none (chars := chars) (ch := ch) (fromIndex := fromIndex)
        rw [← h_start_val] at this
        apply this
        intro i hi
        have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
        rw [this] at hi
        have : i < k ∨ i = k := by omega
        rcases this with h_lt | rfl
        · exact hpre i h_lt
        · exact h_char_k
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      exact step_no_match_to_ret_not_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 hspec hm_mem hr_step hz rfl
  | succ m' ih =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : start_val + k < T := by omega
    have haddr : A + 16#64 + .ofNat 64 (start_val + k) = A + .ofNat 64 (start_val + k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (start_val + k)) 1 =
        some (Int.ofBytes [byteAt s.dmem A (start_val + k)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (start_val + k) 1 T h_some (by omega)]
      rfl
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == 0#64) = false := by
      simp [ofNat64_eq_zero (show m' + 1 + 1 < 2 ^ 64 by omega)]
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_byte_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = .ofNat 64 (m' + 1) := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx, ofNat64_succ_sub_one]
    have h_byte_val : BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) = (d.getD (start_val + k) 0).toBitVec := by
      rw [h_data (start_val + k) hk_lt, ofInt_ofBytes_one]
    by_cases heq : (d.getD (start_val + k) 0).toBitVec = ch.setWidth 8
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) == 0#8) = true := by
        rw [sub_beq_zero, hrax, h_byte_val, heq, beq_self_eq_true]
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 = ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        exact (byte_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (start_val + k) := by
        dsimp only [indexOfSpec]
        rw [← h_start_val]
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop start_val) k (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 26)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = .ofNat 32 (m' + 1) := by
        simp only [get_low32]
        rw [hrcx_eval, setWidth32_ofNat64 _ (by omega)]
      have hlen_calc : .ofNat 32 T - .ofNat 32 (m' + 1) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        have : start_val + k = T - (m' + 1) - 1 := by omega
        rw [this]
        have h_pos : (m' + 1) + 1 ≤ T := by omega
        rw [ofNat32_sub_sub h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_match_to_ret_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 (.ofNat 32 (start_val + k)) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 8 ≠ (d.getD (start_val + k) 0).toBitVec := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W8) -
          BitVec.ofInt 8 (Int.ofBytes [byteAt s.dmem A (start_val + k)]) == 0#8) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_byte_val]
        exact hne_symm
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 ≠ ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        intro h
        have := (byte_eq_iff _ ch h_ch).mp h
        exact heq this
      have hne_zero : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
        rw [bne_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64) = BitVec.ofNat 64 (m' + 1) := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx, ofNat64_succ_sub_one]
      have h_val_rcx_ne : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64 Reg64.rcx - 1#64 != 0#64) = true) := by
        rw [h_val_rcx, hne_zero]
      rw [hzf_false, h_val_rcx_ne]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 25)⟩
      refine Program.loopCont_of_le (j := 25) (by simp [stringIndexOfAfterRepProg]) ?_
      have hrdi' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get64 Reg64.rdi = A + 16#64 + BitVec.ofNat 64 (start_val + (k + 1)) := by
        have : start_val + (k + 1) = (start_val + k) + 1 := by omega
        rw [this]
        exact regs_scas_step_rdi _ _ _ _ hrdi
      have hrax' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get (Reg.low .rax .W8) = ch.setWidth 8 := by
        have : Reg64.rax ≠ .rcx := by decide
        have : Reg64.rax ≠ .rdi := by decide
        simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, this, ↓reduceIte]
        exact hrax
      have hlen_reg' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 1#64)).get64
                Reg64.rcx -
              1#64))).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      exact ih (k + 1) _ hm_mem
        (fun r hr_out => by
          have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          simp only [get64_set64, set_low64, get_low64, h1, h2, ↓reduceIte]
          exact hr r hr_out) hz rfl
        hrcx_eval hrdi' hrax' hlen_reg' (by omega)
        (fun i hi => by
          have : i < k ∨ i = k := by omega
          rcases this with h_lt | rfl
          · exact hpre i h_lt
          · exact h_char_k)
        (by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, by decide⟩)



theorem scasw_after_zero [Host] (slow : Label) (len tmp start_idx : Reg64) (ymm1 ymm2 : AvxReg .W256) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx)) (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms)
    (hzf : t.status.zf = false)
    (hrcx0 : t.regs.get64 .rcx = 0#64) :
    Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
      (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 28)⟩ := by
  refine Program.loop_repne_scasw_zero (i := 28) rfl hrcx0 ?_
  refine Program.loopCont_of_le (j := 29) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  refine Program.loopCont_of_le (j := 30) (by simp [stringIndexOfAfterRepProg]) ?_
  sstep
  rw [hzf]
  simp only [Bool.not_false, ↓reduceIte]
  simp only [addrOf_label hlab (H := H) (i := 34) rfl]
  refine Program.loopCont_of_le (j := 34) (by simp [stringIndexOfAfterRepProg]) ?_
  exact ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s t chars ch fromIndex hspec hm hr hz

theorem scasw_loop_after [Host] (slow : Label) (len tmp start_idx : Reg64) (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx))
    (s : MachineData) (A : BitVec 64) (T start_val : Nat) (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (ymm1 ymm2 : AvxReg .W256) (d : List UInt8)
    (h_ch : ch.toNat ≤ 65535)
    (h_T_lt : T < 2 ^ 32 - 1)
    (h_start_val : start_val = (if fromIndex.slt 0 then 0 else fromIndex.toNat))
    (h_start_lt : start_val < T)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_chars : ∀ (i : Nat) (hi : i < chars.length), chars.get ⟨i, hi⟩ = (d.getD (2 * i) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8))
    (h_len : chars.length = T)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData)
      (hm_mem : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms)
      (hdf : t.status.df = false)
      (hrcx : t.regs.get64 .rcx = .ofNat 64 (m + 1))
      (hrdi : t.regs.get64 .rdi = A + 16#64 + .ofNat 64 (2 * (start_val + k)))
      (hrax : t.regs.get (Reg.low .rax .W16) = ch.setWidth 16)
      (hlen_reg : t.regs.get (.low len .W32) = .ofNat 32 T)
      (hk : k + (m + 1) = T - start_val)
      (hpre : ∀ (i : Nat) (hi : i < k), ((chars.drop start_val).get ⟨i, by
        have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
        omega⟩).zeroExtend 32 ≠ ch)
      (h_distinct : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup),
      Program.Loop (stringIndexOfAfterRepProg slow len tmp start_idx) H
        (StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 28)⟩ := by
  induction m with
  | zero =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : 2 * (start_val + k) + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * (start_val + k)) = A + .ofNat 64 (2 * (start_val + k)) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * (start_val + k))) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (2 * (start_val + k)) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * (start_val + k) + j)) =
          [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)] := rfl
      rw [this]
    have hne0 : (BitVec.ofNat 64 1 == 0#64) = false := rfl
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_word_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = 0#64 := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx]; rfl
    have h_word_val : BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) =
        (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
      rw [h_data (2 * (start_val + k)) (by omega), h_data (2 * (start_val + k) + 1) (by omega), word_of_bytes]
    by_cases heq : (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) = ch.setWidth 16
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) == 0#16) = true := by
        rw [sub_beq_zero, hrax, h_word_val, heq, beq_self_eq_true]
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 = ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        exact (word_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (start_val + k) := by
        dsimp only [indexOfSpec]
        rw [← h_start_val]
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop start_val) k (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 29)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = 0#32 := by
        simp only [get_low32]
        rw [hrcx_eval]; rfl
      have hlen_calc : .ofNat 32 T - 0#32 - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        have : start_val + k = T - 1 := by omega
        rw [this]
        have h_pos : 0 < T := by omega
        rw [BitVec.sub_zero, ← ofNat32_sub_one h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_from_cmp_done_match_to_ret_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 (.ofNat 32 (start_val + k)) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 16 ≠ (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) == 0#16) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_word_val]
        exact hne_symm
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 ≠ ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        intro h
        have := (word_eq_iff _ ch h_ch).mp h
        exact heq this
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64) = 0#64 := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx]; rfl
      have h_count_zero : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64 != 0#64) = false) := by
        rw [h_val_rcx]; rfl
      rw [hzf_false, h_count_zero]
      simp only [Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 29)⟩
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        have := indexOfSpec_eq_none (chars := chars) (ch := ch) (fromIndex := fromIndex)
        rw [← h_start_val] at this
        apply this
        intro i hi
        have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
        rw [this] at hi
        have : i < k ∨ i = k := by omega
        rcases this with h_lt | rfl
        · exact hpre i h_lt
        · exact h_char_k
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      exact step_from_cmp_done_no_match_to_ret_not_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 hspec hm_mem hr_step hz rfl
  | succ m' ih =>
    intro k t hm_mem hr hz hdf hrcx hrdi hrax hlen_reg hk hpre hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, -⟩ := hd
    have hk_lt : 2 * (start_val + k) + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * (start_val + k)) = A + .ofNat 64 (2 * (start_val + k)) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * (start_val + k))) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) := by
      rw [haddr, hm_mem, load_chunk _ _ (2 * (start_val + k)) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * (start_val + k) + j)) =
          [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)] := rfl
      rw [this]
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == 0#64) = false := by
      simp [ofNat64_eq_zero (show m' + 1 + 1 < 2 ^ 64 by omega)]
    sstep
    rw [hrcx, hne0, hdf]
    simp only [Option.isSome, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [hrdi, hload]
    dsimp only []
    simp only [MachineData.setReg, strStep_64_word_false, Effects.All_require_read_access]
    have h_ne : Reg64.rcx ≠ Reg64.rdi := Ne.symm h_rdi_rcx
    have hrcx_eval : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
          Reg64.rcx
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
              Reg64.rcx -
            1#64)).get64 Reg64.rcx) = .ofNat 64 (m' + 1) := by
      simp only [get64_set64, set_low64, get_low64, h_ne, ↓reduceIte]
      rw [hrcx, ofNat64_succ_sub_one]
    have h_word_val : BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) =
        (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) := by
      rw [h_data (2 * (start_val + k)) (by omega), h_data (2 * (start_val + k) + 1) (by omega), word_of_bytes]
    by_cases heq : (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) = ch.setWidth 16
    · have hzf_true : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) == 0#16) = true := by
        rw [sub_beq_zero, hrax, h_word_val, heq, beq_self_eq_true]
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 = ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        exact (word_eq_iff _ ch h_ch).mpr heq
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (start_val + k) := by
        dsimp only [indexOfSpec]
        rw [← h_start_val]
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop start_val) k (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
      rw [hzf_true]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 29)⟩
      have hr_step : ∀ r, r ∉ [Reg64.rdi, Reg64.rcx, len, tmp] →
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get64 r = s.regs.get64 r := by
        intro r hr_out
        simp only [get64_set64, set_low64, get_low64]
        have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
        have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
        simp only [h1, h2, ↓reduceIte]
        exact hr r hr_out
      have hlen_eval : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      have hrcx_low : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) = .ofNat 32 (m' + 1) := by
        simp only [get_low32]
        rw [hrcx_eval, setWidth32_ofNat64 _ (by omega)]
      have hlen_calc : .ofNat 32 T - .ofNat 32 (m' + 1) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        have : start_val + k = T - (m' + 1) - 1 := by omega
        rw [this]
        have h_pos : (m' + 1) + 1 ≤ T := by omega
        rw [ofNat32_sub_sub h_pos]
      have hlen_step : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low len .W32) -
          ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64)).get (.low .rcx .W32) - 1#32 = BitVec.ofNat 32 (start_val + k) := by
        rw [hlen_eval, hrcx_low, hlen_calc]
      exact step_from_cmp_done_match_to_ret_found_after slow len tmp start_idx hlab H s _ chars ch fromIndex ymm1 ymm2 (.ofNat 32 (start_val + k)) hspec hm_mem hr_step hz rfl hlen_step
    · have hne_symm : ch.setWidth 16 ≠ (d.getD (2 * (start_val + k)) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * (start_val + k) + 1) 0).toBitVec.zeroExtend 16 <<< 8) := Ne.symm heq
      have hzf_false : (t.regs.get (Reg.low Reg64.rax Width.W16) -
          BitVec.ofInt 16 (Int.ofBytes [byteAt s.dmem A (2 * (start_val + k)), byteAt s.dmem A (2 * (start_val + k) + 1)]) == 0#16) = false := by
        rw [sub_beq_zero, beq_eq_false_iff_ne]
        rw [hrax, h_word_val]
        exact hne_symm
      have h_char_k : ((chars.drop start_val).get ⟨k, by
          have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
          omega⟩).zeroExtend 32 ≠ ch := by
        have : (chars.drop start_val).get ⟨k, by
            have : (chars.drop start_val).length = T - start_val := by rw [List.length_drop, h_len]
            omega⟩ = chars.get ⟨start_val + k, by rw [h_len]; omega⟩ := by
          exact List.getElem_drop
        rw [this, h_chars (start_val + k) (by rw [h_len]; omega)]
        intro h
        have := (word_eq_iff _ ch h_ch).mp h
        exact heq this
      have hne_zero : (BitVec.ofNat 64 (m' + 1) != 0#64) = true := by
        rw [bne_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        omega
      have h_val_rcx : ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64) = BitVec.ofNat 64 (m' + 1) := by
        simp only [get64_set64, set_low64, get_low64, Ne.symm h_rdi_rcx, ↓reduceIte]
        rw [hrcx, ofNat64_succ_sub_one]
      have h_val_rcx_ne : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64 Reg64.rcx - 1#64 != 0#64) = true) := by
        rw [h_val_rcx, hne_zero]
      rw [hzf_false, h_val_rcx_ne]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
      change Program.LoopCont _ _ _ _ ⟨_, Host.addrOf (H.start + 28)⟩
      refine Program.loopCont_of_le (j := 28) (by simp [stringIndexOfAfterRepProg]) ?_
      have hrdi' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get64 Reg64.rdi = A + 16#64 + BitVec.ofNat 64 (2 * (start_val + (k + 1))) := by
        have : 2 * (start_val + (k + 1)) = 2 * (start_val + k) + 2 := by omega
        rw [this]
        exact regs_scasw_step_rdi _ _ _ _ hrdi
      have hrax' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get (Reg.low .rax .W16) = ch.setWidth 16 := by
        have : Reg64.rax ≠ .rcx := by decide
        have : Reg64.rax ≠ .rdi := by decide
        simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, this, ↓reduceIte]
        exact hrax
      have hlen_reg' : (((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).set64
            Reg64.rcx
            ((t.regs.set (Reg.low Reg64.rdi Width.W64) (t.regs.get (Reg.low Reg64.rdi Width.W64) + 2#64)).get64
                Reg64.rcx -
              1#64))).get (.low len .W32) = .ofNat 32 T := by
        have h_len_rcx : len ≠ Reg64.rcx := Ne.symm h_rcx_len
        have h_len_rdi : len ≠ Reg64.rdi := Ne.symm h_rdi_len
        simp only [get_low32, get64_set64, set_low64, get_low64, h_len_rcx, h_len_rdi, ↓reduceIte]
        rw [get_low32] at hlen_reg
        exact hlen_reg
      exact ih (k + 1) _ hm_mem
        (fun r hr_out => by
          have h1 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          simp only [get64_set64, set_low64, get_low64, h1, h2, ↓reduceIte]
          exact hr r hr_out) hz rfl
        hrcx_eval hrdi' hrax' hlen_reg' (by omega)
        (fun i hi => by
          have : i < k ∨ i = k := by omega
          rcases this with h_lt | rfl
          · exact hpre i h_lt
          · exact h_char_k)
        (by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨⟨h_rdi_rcx, h_rdi_len, h_rdi_tmp⟩, ⟨h_rcx_len, h_rcx_tmp⟩, h_len_tmp, by decide⟩)


theorem stringIndexOfRep_correct [Host] (slow : Label) (len tmp : Reg64) (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [Reg64.rdi, Reg64.rax, Reg64.rcx, len, tmp].Nodup)
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (hslow : ∀ (H : Embedding (stringIndexOfRepProg slow len tmp)), IsSlowPathLabel (stringIndexOfRepProg slow len tmp) H slow)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ (s.regs.get64 .rdi).toNat + 16 < 2 ^ 32 ∧
        d.length = strByteLen c ∧
        s.status.df = false ∧
        (c.getLsbD 0 = false → ∀ b ∈ d, b < 0x80) ∧
        (c.getLsbD 0 = true → 0 < (c >>> 1).toNat) ∧
        ∃ R, (StringAt (s.regs.get64 .rdi) c d ⋆ R) s.dmem ⦄
      (stringIndexOfRepProg slow len tmp)
    ⦃ fun _ => StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2
          (strChars c d) (s₀.regs.get (Reg.low Reg64.rax Width.W32)) 0#32 s₀;
      fun pc s => StringIndexOfSlow slow (s₀.regs.get (Reg.low Reg64.rax Width.W32)) s₀ pc s ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hA32, hl, hdf, h_ascii, h_uncomp_pos, R, hmem⟩
  apply Program.wp_of_loop
  intro H
  have h_prog_len : (stringIndexOfRepProg slow len tmp).length = 25 := rfl
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  let ch := BitVec.setWidth 32 (s.regs.get64 Reg64.rax)
  have hch_def : s.regs.get (Reg.low Reg64.rax Width.W32) = ch := by rw [get_low32]
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp⟩, ⟨hd_rax_rcx, hd_rax_len, hd_rax_tmp⟩, ⟨hd_rcx_len, hd_rcx_tmp⟩, hd_len_tmp, -⟩ := hd
  have hd_distinct4 : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp⟩, ⟨hd_rcx_len, hd_rcx_tmp⟩, hd_len_tmp, by decide⟩
  have hd_len_rcx : len ≠ Reg64.rcx := Ne.symm hd_rcx_len
  have hd_tmp_rcx : tmp ≠ Reg64.rcx := Ne.symm hd_rcx_tmp
  have hd_len_rdi : len ≠ Reg64.rdi := Ne.symm hd_rdi_len
  have hd_tmp_rdi : tmp ≠ Reg64.rdi := Ne.symm hd_rdi_tmp
  have hd_rcx_rdi : Reg64.rcx ≠ Reg64.rdi := Ne.symm hd_rdi_rcx
  have hd_rax_rdi : Reg64.rax ≠ Reg64.rdi := Ne.symm hd_rdi_rax
  have hd_rcx_rax : Reg64.rcx ≠ Reg64.rax := Ne.symm hd_rax_rcx
  have hd_len_rax : len ≠ Reg64.rax := Ne.symm hd_rax_len
  have hd_tmp_rax : tmp ≠ Reg64.rax := Ne.symm hd_rax_tmp
  by_cases h_ch : ch.toNat > 65535
  · have hch_gt : (s.regs.get (Reg.low Reg64.rax Width.W32)).toNat > 65535 := by
      rw [hch_def]; exact h_ch
    have hret := ret_slow slow len tmp ymm1 ymm2 (strChars c d) 0#32 H s s (s.regs.get (Reg.low Reg64.rax Width.W32)) hch_gt rfl rfl rfl rfl (hslow H)
    exact hret
  have h_ch_le : ch.toNat ≤ 65535 := by omega
  have h_eq : ch = BitVec.ofNat 32 ch.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ch.isLt]
  have h_cf : (BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned) =
      decide (ch.toNat < 65535) := by
    conv => lhs; rw [h_eq]
    exact cf_ofNat32 (x := ch.toNat) (c := 65535) ch.isLt (by decide)
  have h_ja : (!BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned &&
      !(ch - 65535#32 == 0#32)) = false := by
    by_cases h_lt : ch.toNat < 65535
    · rw [h_cf, decide_eq_true_iff.mpr h_lt]
      rfl
    · have : ch.toNat = 65535 := by omega
      have hch_val : ch = 65535#32 := by rw [h_eq, this]
      rw [hch_val]
      decide
  -- Directive 0: cmp search_value, $0xFFFF
  sstep
  refine Program.loopCont_of_le (j := 1) (by rw [h_prog_len]; omega) ?_
  -- Directive 1: ja slow
  sstep
  rw [h_ja]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 2) (by rw [h_prog_len]; omega) ?_
  -- Directive 2: movl count, len
  have cA := fun i (hi : i < 4) => sep_get_l hmem (stringAt_cnt (i := i) hi)
  sstep
  rw [load_count s.dmem (s.regs.get64 .rdi) c cA]
  simp only [cnt_val]
  refine Program.loopCont_of_le (j := 3) (by rw [h_prog_len]; omega) ?_
  -- Directive 3: testl len, len
  sstep
  intro _
  refine Program.loopCont_of_le (j := 4) (by rw [h_prog_len]; omega) ?_
  -- Directive 4: jz not_found
  sstep
  have h_and_self : (c &&& c == 0#32) = (c == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hc0 : c = 0#32
  · rw [hc0, beq_self_eq_true]
    simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 22) rfl]
    refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
    have hd_nil : d = [] := by
      have : d.length = 0 := by rw [hl, hc0]; rfl
      exact List.eq_nil_of_length_eq_zero this
    have hchars_nil : strChars (0#32) d = [] := by
      unfold strChars; rw [hd_nil]; rfl
    have hspec : indexOfSpec (strChars (0#32) d) (BitVec.setWidth 32 (s.regs.get64 Reg64.rax)) 0#32 = -1#32 := by
      rw [hchars_nil]; rfl
    exact ret_not_found slow len tmp ymm1 ymm2 hlab H s _ (strChars (0#32) d) (BitVec.setWidth 32 (s.regs.get64 Reg64.rax)) hspec rfl (by
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      obtain ⟨hrdi_ne, hrcx_ne, hlen_ne, htmp_ne⟩ := hr_out
      simp only [get64_set64, hlen_ne, ↓reduceIte]) rfl
  · rw [beq_eq_false_iff_ne.mpr hc0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 5) (by rw [h_prog_len]; omega) ?_
    -- Directive 5: movl len, tmp
    sstep
    refine Program.loopCont_of_le (j := 6) (by rw [h_prog_len]; omega) ?_
    -- Directive 6: shrl $1, len
    sstep
    intro af
    simp only [↓reduceIte, beq_self_eq_true, Bool.false_eq_true]
    refine Program.loopCont_of_le (j := 7) (by rw [h_prog_len]; omega) ?_
    -- Directive 7: movl len, %ecx
    sstep
    refine Program.loopCont_of_le (j := 8) (by rw [h_prog_len]; omega) ?_
    -- Directive 8: addq $16, str
    sstep
    refine Program.loopCont_of_le (j := 9) (by rw [h_prog_len]; omega) ?_
    -- Directive 9: testl $1, tmp
    sstep
    intro _
    refine Program.loopCont_of_le (j := 10) (by rw [h_prog_len]; omega) ?_
    -- Directive 10: jnz uncompressed
    sstep
    simp only [hd_tmp_rdi, hd_tmp_rcx, Ne.symm hd_len_tmp, ↓reduceIte, sw32_64, lsb_and1 c, Bool.not_not]
    by_cases h_comp : c.getLsbD 0 = false
    · -- COMPRESSED PATH
      rw [h_comp]
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 11) (by rw [h_prog_len]; omega) ?_
      -- Directive 11: cmpl $127, search_value
      sstep
      simp only [hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, ↓reduceIte]
      refine Program.loopCont_of_le (j := 12) (by rw [h_prog_len]; omega) ?_
      -- Directive 12: jg not_found
      sstep
      by_cases h_ch127 : ch.toNat > 127
      · have h_jg := jg_ch127_true (ch := ch) h_ch127 h_ch_le
        rw [h_jg]
        simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 22) rfl]
        refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
        have h_ascii' := strChars_compressed_ascii h_comp hl (h_ascii h_comp)
        have hspec : indexOfSpec (strChars c d) ch 0#32 = -1#32 := by
          exact indexOfSpec_compressed_gt127 h_ascii' h_ch127
        exact ret_not_found slow len tmp ymm1 ymm2 hlab H s _ (strChars c d) ch hspec rfl (by
          intro r hr_out
          simp only [get64_set64, set_low64, get_low64]
          have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h3 : r ≠ len := by intro h; subst h; simp at hr_out
          have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
          simp [h1, h2, h3, h4]) rfl
      · have h_ch127_le : ch.toNat ≤ 127 := by omega
        have h_not_jg := jg_ch127_false (ch := ch) h_ch127_le
        rw [h_not_jg]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 13) (by rw [h_prog_len]; omega) ?_
        -- Directive 13: repne scasb!
        have hinfo := string_info_of hmem hl
        have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
        have hT_lt : (c >>> 1).toNat < 2 ^ 32 - 1 := by
          have := strByteLen_lt c; unfold strByteLen at this; rw [h_comp] at this; exact this
        have h_pos : 0 < (c >>> 1).toNat := pos_of_comp c hc0 h_comp
        let m := (c >>> 1).toNat - 1
        have hm1 : m + 1 = (c >>> 1).toNat := by omega
        have h_ascii' : ∀ c_1 ∈ strChars c d, c_1.toNat < 128 := by
          intro c_1 hc_1
          exact strChars_compressed_ascii h_comp hl (h_ascii h_comp) c_1 hc_1
        have hinfo1 : ∀ i < (c >>> 1).toNat, s.dmem[s.regs.get64 Reg64.rdi + 16#64 + BitVec.ofNat 64 i]?.isSome = true := by
          intro i hi
          have : strByteLen c = (c >>> 1).toNat := by unfold strByteLen; rw [h_comp]; simp
          rw [this] at hinfo
          exact hinfo.1 i hi
        have hinfo2 : ∀ i < (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 Reg64.rdi) i = d.getD i 0 := by
          intro i hi
          have : strByteLen c = (c >>> 1).toNat := by unfold strByteLen; rw [h_comp]; simp
          rw [this] at hinfo
          exact hinfo.2 i hi
        have hch_eq : BitVec.setWidth 32 (s.regs.get64 Reg64.rax) = ch := rax_w32_eq s ch hch_def
        rw [hch_eq]
        refine scasb_loop slow len tmp hlab H s (s.regs.get64 .rdi) (c >>> 1).toNat
          (strChars c d) ch ymm1 ymm2 d h_ascii' h_ch127_le hT_lt hinfo1 hinfo2 (by
            intro i hi
            exact strChars_compressed_get h_comp i (by rw [← h_len_eq]; exact hi))
          h_len_eq m 0 _ rfl ?_ rfl hdf ?_ ?_ ?_ ?_ (by omega) (by intro i hi; omega) hd_distinct4
        · intro r hr_out
          have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h3 : r ≠ len := by intro h; subst h; simp at hr_out
          have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
          simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
        · simp only [get64_set64, hd_rcx_rdi, hd_rcx_len, hd_rcx_tmp, hd_len_tmp, ↓reduceIte]
          rw [hm1]
          exact rcx_eval_eq c
        · simp only [get64_set64, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, ↓reduceIte]
          rw [BitVec.add_comm, BitVec.add_zero]
        · have : Reg64.rax ≠ .rdi := by decide
          have : Reg64.rax ≠ .rcx := by decide
          have : Reg64.rax ≠ len := hd_rax_len
          have : Reg64.rax ≠ tmp := hd_rax_tmp
          simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, ↓reduceIte]
          exact rax_w8_eq s ch hch_def
        · simp only [get_low32, get64_set64, hd_len_rdi, hd_len_rcx, hd_len_tmp, ↓reduceIte]
          exact len_eval_eq c
    · -- UNCOMPRESSED PATH
      have h_uncomp : c.getLsbD 0 = true := by
        cases h : c.getLsbD 0
        · contradiction
        · rfl
      rw [h_uncomp]
      simp only [Bool.not_true, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 15) rfl]
      refine Program.loopCont_of_le (j := 15) (by rw [h_prog_len]; omega) ?_
      -- Directive 15: .label "uncompressed"
      sstep
      refine Program.loopCont_of_le (j := 16) (by rw [h_prog_len]; omega) ?_
      -- Directive 16: repne scasw!
      have hinfo := string_info_of hmem hl
      have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
      have hT_lt : (c >>> 1).toNat < 2 ^ 32 - 1 := shift_right_lt c
      by_cases hT0 : (c >>> 1).toNat = 0
      · have hspec : indexOfSpec (strChars c d) ch 0#32 = -1#32 := by
          have : strChars c d = [] := by
            apply List.length_eq_zero_iff.mp
            rw [h_len_eq, hT0]
          rw [this, indexOfSpec_empty]
        refine scasw_zero slow len tmp ymm1 ymm2 hlab H s _ (strChars c d) ch hspec rfl ?_ rfl ?_ ?_
        · intro r hr_out
          have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h3 : r ≠ len := by intro h; subst h; simp at hr_out
          have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
          simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
        · simp only [hd_tmp_rdi, hd_tmp_rcx, Ne.symm hd_len_tmp, ↓reduceIte, sw32_64, lsb_and1 c, h_uncomp]
        · simp only [get64_set64, hd_rcx_rdi, hd_len_tmp, ↓reduceIte]
          rw [rcx_eval_eq c, hT0]
      · have h_pos : 0 < (c >>> 1).toNat := by omega
        let m := (c >>> 1).toNat - 1
        have hm1 : m + 1 = (c >>> 1).toNat := by omega
        have hch_eq : BitVec.setWidth 32 (s.regs.get64 Reg64.rax) = ch := rax_w32_eq s ch hch_def
        rw [hch_eq]
        refine scasw_loop slow len tmp hlab H s (s.regs.get64 .rdi) (c >>> 1).toNat
          (strChars c d) ch ymm1 ymm2 d h_ch_le hT_lt (by
            intro i hi
            have : strByteLen c = 2 * (c >>> 1).toNat := by
              unfold strByteLen; rw [h_uncomp]; simp
            rw [this] at hinfo
            exact hinfo.1 i hi) (by
            intro i hi
            have : strByteLen c = 2 * (c >>> 1).toNat := by
              unfold strByteLen; rw [h_uncomp]; simp
            rw [this] at hinfo
            exact hinfo.2 i hi) (by
            intro i hi
            exact strChars_uncompressed_get h_uncomp i (by rw [← h_len_eq]; exact hi))
          h_len_eq m 0 _ rfl ?_ rfl hdf ?_ ?_ ?_ ?_ (by omega) (by intro i hi; omega) hd_distinct4
        · intro r hr_out
          have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
          have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
          have h3 : r ≠ len := by intro h; subst h; simp at hr_out
          have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
          simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
        · simp only [get64_set64, hd_rcx_rdi, hd_rcx_len, hd_rcx_tmp, hd_len_tmp, ↓reduceIte]
          rw [hm1]
          exact rcx_eval_eq c
        · simp only [get64_set64, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, ↓reduceIte]
          rw [BitVec.add_comm, BitVec.add_zero]
        · have : Reg64.rax ≠ .rdi := by decide
          have : Reg64.rax ≠ .rcx := by decide
          have : Reg64.rax ≠ len := hd_rax_len
          have : Reg64.rax ≠ tmp := hd_rax_tmp
          simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, ↓reduceIte]
          exact rax_w16_eq s ch hch_def
        · simp only [get_low32, get64_set64, hd_len_rdi, hd_len_rcx, hd_len_tmp, ↓reduceIte]
          exact len_eval_eq c


theorem stringIndexOfAfterRep_correct [Host] (slow : Label) (len tmp start_idx : Reg64) (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [Reg64.rdi, Reg64.rax, Reg64.rcx, len, tmp, start_idx].Nodup)
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (hslow : ∀ (H : Embedding (stringIndexOfAfterRepProg slow len tmp start_idx)), IsSlowPathLabel (stringIndexOfAfterRepProg slow len tmp start_idx) H slow)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ (s.regs.get64 .rdi).toNat + 16 < 2 ^ 32 ∧
        d.length = strByteLen c ∧
        s.status.df = false ∧
        (c.getLsbD 0 = false → ∀ b ∈ d, b < 0x80) ∧
        (c.getLsbD 0 = true → 0 < (c >>> 1).toNat) ∧
        ∃ R, (StringAt (s.regs.get64 .rdi) c d ⋆ R) s.dmem ⦄
      (stringIndexOfAfterRepProg slow len tmp start_idx)
    ⦃ fun _ => StringIndexOfPost .rdi [.rcx, len, tmp] ymm1 ymm2
          (strChars c d) (s₀.regs.get (Reg.low Reg64.rax Width.W32)) (s₀.regs.get (Reg.low start_idx Width.W32)) s₀;
      fun pc s => StringIndexOfSlow slow (s₀.regs.get (Reg.low Reg64.rax Width.W32)) s₀ pc s ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hA32, hl, hdf, h_ascii, h_uncomp_pos, R, hmem⟩
  apply Program.wp_of_loop
  intro H
  have h_prog_len : (stringIndexOfAfterRepProg slow len tmp start_idx).length = 37 := rfl
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  let ch := BitVec.setWidth 32 (s.regs.get64 Reg64.rax)
  let fromIndex := BitVec.setWidth 32 (s.regs.get64 start_idx)
  have hch_def : s.regs.get (Reg.low Reg64.rax Width.W32) = ch := by rw [get_low32]
  have hfrom_def : s.regs.get (Reg.low start_idx Width.W32) = fromIndex := by rw [get_low32]
  rw [hch_def, hfrom_def]
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start⟩,
          ⟨hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start⟩,
          ⟨hd_rcx_len, hd_rcx_tmp, hd_rcx_start⟩,
          ⟨hd_len_tmp, hd_len_start⟩,
          hd_tmp_start, -⟩ := hd
  have hd_rdi_rcx : Reg64.rdi ≠ Reg64.rcx := hd_rdi_rcx
  have hd_rdi_len : Reg64.rdi ≠ len := hd_rdi_len
  have hd_rdi_tmp : Reg64.rdi ≠ tmp := hd_rdi_tmp
  have hd_rdi_rax : Reg64.rdi ≠ Reg64.rax := hd_rdi_rax
  have hd_rdi_start : Reg64.rdi ≠ start_idx := hd_rdi_start
  have hd_rcx_len : Reg64.rcx ≠ len := hd_rcx_len
  have hd_rcx_tmp : Reg64.rcx ≠ tmp := hd_rcx_tmp
  have hd_rcx_rax : Reg64.rcx ≠ Reg64.rax := Ne.symm hd_rax_rcx
  have hd_rcx_start : Reg64.rcx ≠ start_idx := hd_rcx_start
  have hd_len_tmp : len ≠ tmp := hd_len_tmp
  have hd_len_rax : len ≠ Reg64.rax := Ne.symm hd_rax_len
  have hd_len_start : len ≠ start_idx := hd_len_start
  have hd_tmp_rax : tmp ≠ Reg64.rax := Ne.symm hd_rax_tmp
  have hd_tmp_start : tmp ≠ start_idx := hd_tmp_start
  have hd_start_rax : start_idx ≠ Reg64.rax := Ne.symm hd_rax_start
  have hd_rax_rdi : Reg64.rax ≠ Reg64.rdi := Ne.symm hd_rdi_rax
  have hd_rax_rcx : Reg64.rax ≠ Reg64.rcx := hd_rax_rcx
  have hd_rax_len : Reg64.rax ≠ len := hd_rax_len
  have hd_rax_tmp : Reg64.rax ≠ tmp := hd_rax_tmp
  have hd_rax_start : Reg64.rax ≠ start_idx := hd_rax_start
  have hd_rcx_rdi : Reg64.rcx ≠ Reg64.rdi := Ne.symm hd_rdi_rcx
  have hd_len_rdi : len ≠ Reg64.rdi := Ne.symm hd_rdi_len
  have hd_tmp_rdi : tmp ≠ Reg64.rdi := Ne.symm hd_rdi_tmp
  have hd_start_rdi : start_idx ≠ Reg64.rdi := Ne.symm hd_rdi_start
  have hd_len_rcx : len ≠ Reg64.rcx := Ne.symm hd_rcx_len
  have hd_tmp_rcx : tmp ≠ Reg64.rcx := Ne.symm hd_rcx_tmp
  have hd_start_rcx : start_idx ≠ Reg64.rcx := Ne.symm hd_rcx_start
  have hd_tmp_len : tmp ≠ len := Ne.symm hd_len_tmp
  have hd_start_len : start_idx ≠ len := Ne.symm hd_len_start
  have hd_start_tmp : start_idx ≠ tmp := Ne.symm hd_tmp_start
  have hd_distinct4 : [Reg64.rdi, Reg64.rcx, len, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp⟩, ⟨hd_rcx_len, hd_rcx_tmp⟩, hd_len_tmp, by decide⟩
  by_cases h_ch : ch.toNat > 65535
  · have hch_gt : ch.toNat > 65535 := h_ch
    exact ret_slow_after slow len tmp start_idx ymm1 ymm2 (strChars c d) fromIndex H s s ch hch_gt hch_def rfl rfl rfl (hslow H)
  have h_ch_le : ch.toNat ≤ 65535 := by omega
  have h_eq : ch = BitVec.ofNat 32 ch.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
  have h_cf : (BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned) =
      decide (ch.toNat < 65535) := by
    conv => lhs; rw [h_eq]
    exact cf_ofNat32 (x := ch.toNat) (c := 65535) ch.isLt (by decide)
  have h_ja : (!BitVec.unsigned (ch - 65535#32) != ch.unsigned - (65535#32).unsigned &&
      !(ch - 65535#32 == 0#32)) = false := by
    by_cases h_lt : ch.toNat < 65535
    · rw [h_cf, decide_eq_true_iff.mpr h_lt]
      rfl
    · have : ch.toNat = 65535 := by omega
      have hch_val : ch = 65535#32 := by rw [h_eq, this]
      rw [hch_val]
      decide
  -- Directive 0: cmp search_value, $0xFFFF
  sstep
  refine Program.loopCont_of_le (j := 1) (by rw [h_prog_len]; omega) ?_
  -- Directive 1: ja slow
  sstep
  rw [h_ja]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 2) (by rw [h_prog_len]; omega) ?_
  -- Directive 2: movl count, len
  have cA := fun i (hi : i < 4) => sep_get_l hmem (stringAt_cnt (i := i) hi)
  sstep
  rw [load_count s.dmem (s.regs.get64 .rdi) c cA]
  simp only [cnt_val]
  refine Program.loopCont_of_le (j := 3) (by rw [h_prog_len]; omega) ?_
  -- Directive 3: testl len, len
  sstep
  intro _
  refine Program.loopCont_of_le (j := 4) (by rw [h_prog_len]; omega) ?_
  -- Directive 4: jz not_found
  sstep
  have h_and_self : (c &&& c == 0#32) = (c == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hc0 : c = 0#32
  · rw [hc0, beq_self_eq_true]
    simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 34) rfl]
    refine Program.loopCont_of_le (j := 34) (by rw [h_prog_len]; omega) ?_
    have hd_nil : d = [] := by
      have : d.length = 0 := by rw [hl, hc0]; rfl
      exact List.eq_nil_of_length_eq_zero this
    have hchars_nil : strChars (0#32) d = [] := by
      unfold strChars; rw [hd_nil]; rfl
    have hspec : indexOfSpec (strChars (0#32) d) ch fromIndex = -1#32 := by
      rw [hchars_nil, indexOfSpec_empty]
    refine ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s _ (strChars (0#32) d) ch fromIndex hspec rfl ?_ rfl
    · intro r hr_out
      simp only [get64_set64]
      by_cases h1 : r = len
      · subst h1; simp at hr_out
      · simp [h1]
  · rw [beq_eq_false_iff_ne.mpr hc0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 5) (by rw [h_prog_len]; omega) ?_
    -- Directive 5: movl len, tmp
    sstep
    refine Program.loopCont_of_le (j := 6) (by rw [h_prog_len]; omega) ?_
    -- Directive 6: shrl $1, len
    sstep
    intro af
    simp only [↓reduceIte, beq_self_eq_true]
    refine Program.loopCont_of_le (j := 7) (by rw [h_prog_len]; omega) ?_
    -- Directive 7: cmpl len, start_idx
    sstep
    refine Program.loopCont_of_le (j := 8) (by rw [h_prog_len]; omega) ?_
    -- Directive 8: jge not_found
    sstep
    simp only [hd_start_len, hd_start_tmp, hd_len_tmp, ↓reduceIte]
    have hT_lt : (c >>> 1).toNat < 2 ^ 32 - 1 := shift_right_lt c
    have hT_lt31 : (c >>> 1).toNat < 2 ^ 31 := by
      rw [BitVec.toNat_ushiftRight]
      have := c.isLt
      omega
    have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
    let start_val := BitVec.setWidth 32 (s.regs.get64 start_idx)
    let len_val := (BitVec.setWidth 32 (BitVec.setWidth 64 c)).ushiftRight 1
    let v_ge := (start_val - len_val).msb ==
      ((start_val - len_val).signed != start_val.signed - len_val.signed)
    by_cases hge : v_ge = true
    · dsimp only [v_ge] at hge
      rw [hge]
      simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 34) rfl]
      refine Program.loopCont_of_le (j := 34) (by rw [h_prog_len]; omega) ?_
      have hlen_eq : len_val = BitVec.ofNat 32 (c >>> 1).toNat := by
        dsimp [len_val]
        have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
        rw [BitVec.ofNat_toNat]
        bv_decide
      have hstart_eq : start_val = fromIndex := rfl
      have hge_spec : (strChars c d).length ≤ (if fromIndex.slt 0 then 0 else fromIndex.toNat) := by
        rw [h_len_eq]
        rw [hstart_eq, hlen_eq] at hge
        have hjge := jge_implies_ge fromIndex (BitVec.ofNat 32 (c >>> 1).toNat) (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hT_lt31) hge
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hjge
        exact hjge
      have hspec : indexOfSpec (strChars c d) ch fromIndex = -1#32 := indexOfSpec_ge hge_spec
      refine ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s _ (strChars c d) ch fromIndex hspec rfl ?_ rfl
      · intro r hr_out
        simp only [get64_set64]
        by_cases h1 : r = len
        · subst h1; simp at hr_out
        · by_cases h2 : r = tmp
          · subst h2; simp at hr_out
          · simp [h1, h2]
    · dsimp only [v_ge] at hge
      have hnot_ge : v_ge = false := by
        cases h : v_ge
        · rfl
        · contradiction
      dsimp only [v_ge] at hnot_ge
      rw [hnot_ge]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 9) (by rw [h_prog_len]; omega) ?_
      -- Directive 9: xorl %rcx, %rcx
      sstep
      intro _
      refine Program.loopCont_of_le (j := 10) (by rw [h_prog_len]; omega) ?_
      -- Directive 10: cmpl $0, start_idx
      sstep
      refine Program.loopCont_of_le (j := 11) (by rw [h_prog_len]; omega) ?_
      -- Directive 11: cmovg start_idx, counter
      sstep
      refine Program.loopCont_of_le (j := 12) (by rw [h_prog_len]; omega) ?_
      -- Directive 12: testl $1, tmp
      sstep
      intro _
      refine Program.loopCont_of_le (j := 13) (by rw [h_prog_len]; omega) ?_
      -- Directive 13: jnz offset_uncompressed
      sstep
      simp only [hd_tmp_rdi, hd_tmp_rcx, hd_tmp_start, hd_tmp_len, Ne.symm hd_len_tmp, ↓reduceIte, lsb_and1 c, sw32_64, Bool.not_not]
      by_cases h_comp : c.getLsbD 0 = false
      · -- COMPRESSED PATH
        rw [h_comp]
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 14) (by rw [h_prog_len]; omega) ?_
        -- Directive 14: leaq 16(%rdi, %rcx, 1), %rdi
        sstep
        refine Program.loopCont_of_le (j := 15) (by rw [h_prog_len]; omega) ?_
        -- Directive 15: jmp modify_counter
        sstep
        simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 18) rfl]
        refine Program.loopCont_of_le (j := 18) (by rw [h_prog_len]; omega) ?_
        -- Directive 18: .label "modify_counter"
        sstep
        refine Program.loopCont_of_le (j := 19) (by rw [h_prog_len]; omega) ?_
        -- Directive 19: negq %rcx
        sstep
        refine Program.loopCont_of_le (j := 20) (by rw [h_prog_len]; omega) ?_
        -- Directive 20: leaq (%len, %rcx, 1), %rcx
        sstep
        refine Program.loopCont_of_le (j := 21) (by rw [h_prog_len]; omega) ?_
        -- Directive 21: testl $1, tmp
        sstep
        intro _
        refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
        -- Directive 22: jnz uncompressed
        sstep
        simp only [hd_tmp_rdi, hd_tmp_rcx, hd_tmp_len, hd_tmp_start, Ne.symm hd_len_tmp, ↓reduceIte, sw32_64, lsb_and1 c, h_comp, Bool.not_false, Bool.false_eq_true]
        refine Program.loopCont_of_le (j := 23) (by rw [h_prog_len]; omega) ?_
        -- Directive 23: cmpl $127, %rax
        sstep
        have : Reg64.rax ≠ Reg64.rdi := hd_rax_rdi
        have : Reg64.rax ≠ Reg64.rcx := hd_rax_rcx
        have : Reg64.rax ≠ len := hd_rax_len
        have : Reg64.rax ≠ tmp := hd_rax_tmp
        have : Reg64.rax ≠ start_idx := hd_rax_start
        simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start, ↓reduceIte]
        rw [rax_w32_eq s ch hch_def]
        refine Program.loopCont_of_le (j := 24) (by rw [h_prog_len]; omega) ?_
        -- Directive 24: jg not_found
        sstep
        by_cases h_ch127 : ch.toNat > 127
        · have h_jg := jg_ch127_true (ch := ch) h_ch127 h_ch_le
          rw [h_jg]
          simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 34) rfl]
          refine Program.loopCont_of_le (j := 34) (by rw [h_prog_len]; omega) ?_
          have h_ascii_c := strChars_compressed_ascii h_comp hl (h_ascii h_comp)
          have hspec : indexOfSpec (strChars c d) ch fromIndex = -1#32 := by
            exact indexOfSpec_compressed_gt127 h_ascii_c h_ch127
          exact ret_not_found_after slow len tmp start_idx ymm1 ymm2 hlab H s _ (strChars c d) ch fromIndex hspec rfl (by
            intro r hr_out
            simp only [get64_set64, set_low64, get_low64]
            have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
            have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
            have h3 : r ≠ len := by intro h; subst h; simp at hr_out
            have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
            simp [h1, h2, h3, h4]) rfl
        · have h_ch127_le : ch.toNat ≤ 127 := by omega
          have h_not_jg := jg_ch127_false (ch := ch) h_ch127_le
          rw [h_not_jg]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Program.loopCont_of_le (j := 25) (by rw [h_prog_len]; omega) ?_
          -- Directive 25: repne scasb!
          have hinfo := string_info_of hmem hl
          have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
          have hT_lt : (c >>> 1).toNat < 2 ^ 32 - 1 := shift_right_lt c
          have h_pos : 0 < (c >>> 1).toNat := pos_of_comp c hc0 h_comp
          have hlen_eq : len_val = BitVec.ofNat 32 (c >>> 1).toNat := by
            dsimp [len_val]
            have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
            rw [BitVec.ofNat_toNat]
            bv_decide
          have hstart_eq : start_val = fromIndex := rfl
          have h_start_val_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) < (c >>> 1).toNat := by
            rw [hstart_eq, hlen_eq] at hnot_ge
            have hjge := not_jge_implies_lt fromIndex (BitVec.ofNat 32 (c >>> 1).toNat) (by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              exact h_pos) (by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              exact hT_lt31) hnot_ge
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hjge
            exact hjge
          let start_val_nat := if fromIndex.slt 0 then 0 else fromIndex.toNat
          let m := (c >>> 1).toNat - start_val_nat - 1
          have hm1 : m + 1 = (c >>> 1).toNat - start_val_nat := by omega
          have h_ascii_c := strChars_compressed_ascii h_comp hl (h_ascii h_comp)
          refine scasb_loop_after slow len tmp start_idx hlab H s (s.regs.get64 .rdi) (c >>> 1).toNat start_val_nat
            (strChars c d) ch fromIndex ymm1 ymm2 d h_ascii_c h_ch127_le hT_lt rfl h_start_val_eq (by
              intro i hi
              have : strByteLen c = (c >>> 1).toNat := by
                unfold strByteLen; rw [h_comp]; rfl
              rw [this] at hinfo
              exact hinfo.1 i hi) (by
              intro i hi
              have : strByteLen c = (c >>> 1).toNat := by
                unfold strByteLen; rw [h_comp]; rfl
              rw [this] at hinfo
              exact hinfo.2 i hi) (by
              intro i hi
              exact strChars_compressed_get h_comp i (by rw [← h_len_eq]; exact hi))
            h_len_eq m 0 _ rfl ?_ rfl hdf ?_ ?_ ?_ ?_ (by omega) (by intro i hi; omega) hd_distinct4
          · intro r hr_out
            have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
            have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
            have h3 : r ≠ len := by intro h; subst h; simp at hr_out
            have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
            simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
          · -- Goal 2: hrcx
            simp only [get64_set64,
              hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start,
              hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start,
              hd_rcx_len, hd_rcx_tmp, hd_rcx_start,
              hd_len_tmp, hd_len_start,
              hd_tmp_start,
              Ne.symm hd_rdi_rax, Ne.symm hd_rdi_rcx, Ne.symm hd_rdi_len, Ne.symm hd_rdi_tmp, Ne.symm hd_rdi_start,
              Ne.symm hd_rax_rcx, Ne.symm hd_rax_len, Ne.symm hd_rax_tmp, Ne.symm hd_rax_start,
              Ne.symm hd_rcx_len, Ne.symm hd_rcx_tmp, Ne.symm hd_rcx_start,
              Ne.symm hd_len_tmp, Ne.symm hd_len_start,
              Ne.symm hd_tmp_start,
              ↓reduceIte]
            have h_xor_self : BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) ^^^ BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) = 0#32 := by bv_decide
            have h_from_eq : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
            rw [h_from_eq, h_xor_self]
            have h_signed_eq : (BitVec.signed (fromIndex - 0#32) != fromIndex.signed - (0#32).signed) =
                ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) := rfl
            rw [h_signed_eq]
            rw [cmovg_start_idx_eval fromIndex]
            rw [BitVec.add_zero]
            have h_len_eval : BitVec.setWidth 64 (c.ushiftRight 1) = BitVec.ofNat 64 (c >>> 1).toNat := by
              have : (c >>> 1).toNat < 2 ^ 64 := by
                have := (c >>> 1).isLt; omega
              rw [BitVec.ofNat_toNat]
              bv_decide
            rw [h_len_eval]
            change BitVec.ofNat 64 (c >>> 1).toNat + -BitVec.ofNat 64 start_val_nat = BitVec.ofNat 64 (m + 1)
            have h_sub_neg : BitVec.ofNat 64 (c >>> 1).toNat + -BitVec.ofNat 64 start_val_nat =
                BitVec.ofNat 64 (c >>> 1).toNat - BitVec.ofNat 64 start_val_nat := by bv_decide
            rw [h_sub_neg]
            rw [ofNat_sub_eq ((c >>> 1).toNat) start_val_nat (by omega) (by omega)]
            rw [hm1]
          · -- Goal 3: hrdi
            simp only [get64_set64,
              hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start,
              hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start,
              hd_rcx_len, hd_rcx_tmp, hd_rcx_start,
              hd_len_tmp, hd_len_start,
              hd_tmp_start,
              Ne.symm hd_rdi_rax, Ne.symm hd_rdi_rcx, Ne.symm hd_rdi_len, Ne.symm hd_rdi_tmp, Ne.symm hd_rdi_start,
              Ne.symm hd_rax_rcx, Ne.symm hd_rax_len, Ne.symm hd_rax_tmp, Ne.symm hd_rax_start,
              Ne.symm hd_rcx_len, Ne.symm hd_rcx_tmp, Ne.symm hd_rcx_start,
              Ne.symm hd_len_tmp, Ne.symm hd_len_start,
              Ne.symm hd_tmp_start,
              ↓reduceIte]
            have h_xor_self : BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) ^^^ BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) = 0#32 := by bv_decide
            have h_from_eq : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
            rw [h_from_eq, h_xor_self]
            have h_signed_eq : (BitVec.signed (fromIndex - 0#32) != fromIndex.signed - (0#32).signed) =
                ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) := rfl
            rw [h_signed_eq]
            rw [cmovg_start_idx_eval fromIndex]
            rw [Nat.add_zero]
            have : (BitVec.ofNat 64 (if fromIndex.slt 0 = true then 0 else fromIndex.toNat)) =
                BitVec.ofNat 64 start_val_nat := rfl
            rw [this]
            ac_rfl
          · have : Reg64.rax ≠ .rdi := by decide
            have : Reg64.rax ≠ .rcx := by decide
            have : Reg64.rax ≠ len := hd_rax_len
            have : Reg64.rax ≠ tmp := hd_rax_tmp
            simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, ↓reduceIte]
            exact rax_w8_eq s ch hch_def
          · simp only [get_low32, get64_set64, hd_len_rdi, hd_len_rcx, ↓reduceIte]
            exact len_eval_simple c
      · -- UNCOMPRESSED PATH
        have h_uncomp : c.getLsbD 0 = true := by
          cases h : c.getLsbD 0
          · contradiction
          · rfl
        rw [h_uncomp]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 16) rfl]
        refine Program.loopCont_of_le (j := 16) (by rw [h_prog_len]; omega) ?_
        -- Directive 16: offset_uncompressed
        sstep
        refine Program.loopCont_of_le (j := 17) (by rw [h_prog_len]; omega) ?_
        -- Directive 17: leaq 16(%rdi, %rcx, 2), %rdi
        sstep
        refine Program.loopCont_of_le (j := 18) (by rw [h_prog_len]; omega) ?_
        -- Directive 18: modify_counter
        sstep
        refine Program.loopCont_of_le (j := 19) (by rw [h_prog_len]; omega) ?_
        -- Directive 19: negq %rcx
        sstep
        refine Program.loopCont_of_le (j := 20) (by rw [h_prog_len]; omega) ?_
        -- Directive 20: leaq (%len, %rcx, 1), %rcx
        sstep
        refine Program.loopCont_of_le (j := 21) (by rw [h_prog_len]; omega) ?_
        -- Directive 21: testl $1, tmp
        sstep
        intro _
        refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
        -- Directive 22: jnz uncompressed
        sstep
        simp only [hd_tmp_rdi, hd_tmp_rcx, hd_tmp_start, hd_tmp_len, Ne.symm hd_len_tmp, ↓reduceIte, sw32_64, lsb_and1 c, h_uncomp, Bool.not_true, Bool.false_eq_true, addrOf_label hlab (H := H) (i := 27) rfl]
        refine Program.loopCont_of_le (j := 27) (by rw [h_prog_len]; omega) ?_
        -- Directive 27: .label "uncompressed"
        sstep
        refine Program.loopCont_of_le (j := 28) (by rw [h_prog_len]; omega) ?_
        -- Directive 28: repne scasw
        have hinfo := string_info_of hmem hl
        have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
        have hT_lt : (c >>> 1).toNat < 2 ^ 32 - 1 := shift_right_lt c
        by_cases hT0 : (c >>> 1).toNat = 0
        · have h_chars_nil : strChars c d = [] := by
            apply List.length_eq_zero_iff.mp
            rw [strChars_length, hT0]
          have hspec : indexOfSpec (strChars c d) ch fromIndex = -1#32 := by
            rw [h_chars_nil, indexOfSpec_empty]
          refine scasw_after_zero slow len tmp start_idx ymm1 ymm2 hlab H s _ (strChars c d) ch fromIndex hspec rfl ?_ rfl ?_ ?_
          · intro r hr_out
            have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
            have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
            have h3 : r ≠ len := by intro h; subst h; simp at hr_out
            have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
            simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
          · simp only [get64_set64, hd_tmp_rdi, hd_tmp_rcx, hd_tmp_start, hd_tmp_len, Ne.symm hd_len_tmp, ↓reduceIte, sw32_64, lsb_and1 c, h_uncomp]
          · simp only [get64_set64,
              hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start,
              hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start,
              hd_rcx_len, hd_rcx_tmp, hd_rcx_start,
              hd_len_tmp, hd_len_start,
              hd_tmp_start,
              Ne.symm hd_rdi_rax, Ne.symm hd_rdi_rcx, Ne.symm hd_rdi_len, Ne.symm hd_rdi_tmp, Ne.symm hd_rdi_start,
              Ne.symm hd_rax_rcx, Ne.symm hd_rax_len, Ne.symm hd_rax_tmp, Ne.symm hd_rax_start,
              Ne.symm hd_rcx_len, Ne.symm hd_rcx_tmp, Ne.symm hd_rcx_start,
              Ne.symm hd_len_tmp, Ne.symm hd_len_start,
              Ne.symm hd_tmp_start,
              ↓reduceIte]
            have h_xor_self : BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) ^^^ BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) = 0#32 := by bv_decide
            have h_from_eq : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
            rw [h_from_eq, h_xor_self]
            have h_signed_eq : (BitVec.signed (fromIndex - 0#32) != fromIndex.signed - (0#32).signed) =
                ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) := rfl
            rw [h_signed_eq]
            have hc_shift : c.ushiftRight 1 = 0#32 := by
              apply BitVec.eq_of_toNat_eq
              exact hT0
            have hlen0 : len_val = 0#32 := by
              dsimp [len_val]
              have : BitVec.setWidth 32 (BitVec.setWidth 64 c) = c := by bv_decide
              rw [this, hc_shift]
            have hnot_ge0 : ((fromIndex - 0#32).msb == ((fromIndex - 0#32).signed != fromIndex.signed - (0#32).signed)) = false := by
              rw [← hlen0]
              exact hnot_ge
            rw [rcx_zero_of_len_zero fromIndex hnot_ge0]
            have h_len_eval : BitVec.setWidth 64 (c.ushiftRight 1) = 0#64 := by
              rw [hc_shift]
              rfl
            rw [h_len_eval]
            rfl
        · have h_pos : 0 < (c >>> 1).toNat := by omega
          have hlen_eq : len_val = BitVec.ofNat 32 (c >>> 1).toNat := by
            dsimp [len_val]
            have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
            rw [BitVec.ofNat_toNat]
            bv_decide
          have hstart_eq : start_val = fromIndex := rfl
          have h_start_val_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) < (c >>> 1).toNat := by
            rw [hstart_eq, hlen_eq] at hnot_ge
            have hjge := not_jge_implies_lt fromIndex (BitVec.ofNat 32 (c >>> 1).toNat) (by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              exact h_pos) (by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              exact hT_lt31) hnot_ge
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hjge
            exact hjge
          let start_val_nat := if fromIndex.slt 0 then 0 else fromIndex.toNat
          let m := (c >>> 1).toNat - start_val_nat - 1
          have hm1 : m + 1 = (c >>> 1).toNat - start_val_nat := by omega
          refine scasw_loop_after slow len tmp start_idx hlab H s (s.regs.get64 .rdi) (c >>> 1).toNat start_val_nat
            (strChars c d) ch fromIndex ymm1 ymm2 d h_ch_le hT_lt rfl h_start_val_eq (by
              intro i hi
              have : strByteLen c = 2 * (c >>> 1).toNat := by
                unfold strByteLen; rw [h_uncomp]; simp
              rw [this] at hinfo
              exact hinfo.1 i hi) (by
              intro i hi
              have : strByteLen c = 2 * (c >>> 1).toNat := by
                unfold strByteLen; rw [h_uncomp]; simp
              rw [this] at hinfo
              exact hinfo.2 i hi) (by
              intro i hi
              exact strChars_uncompressed_get h_uncomp i (by rw [← h_len_eq]; exact hi))
            h_len_eq m 0 _ rfl ?_ rfl hdf ?_ ?_ ?_ ?_ (by omega) (by intro i hi; omega) hd_distinct4
          · intro r hr_out
            have h1 : r ≠ .rdi := by intro h; subst h; simp at hr_out
            have h2 : r ≠ .rcx := by intro h; subst h; simp at hr_out
            have h3 : r ≠ len := by intro h; subst h; simp at hr_out
            have h4 : r ≠ tmp := by intro h; subst h; simp at hr_out
            simp only [get64_set64, h1, h2, h3, h4, ↓reduceIte]
          · simp only [get64_set64,
              hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start,
              hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start,
              hd_rcx_len, hd_rcx_tmp, hd_rcx_start,
              hd_len_tmp, hd_len_start,
              hd_tmp_start,
              Ne.symm hd_rdi_rax, Ne.symm hd_rdi_rcx, Ne.symm hd_rdi_len, Ne.symm hd_rdi_tmp, Ne.symm hd_rdi_start,
              Ne.symm hd_rax_rcx, Ne.symm hd_rax_len, Ne.symm hd_rax_tmp, Ne.symm hd_rax_start,
              Ne.symm hd_rcx_len, Ne.symm hd_rcx_tmp, Ne.symm hd_rcx_start,
              Ne.symm hd_len_tmp, Ne.symm hd_len_start,
              Ne.symm hd_tmp_start,
              ↓reduceIte]
            have h_xor_self : BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) ^^^ BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) = 0#32 := by bv_decide
            have h_from_eq : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
            rw [h_from_eq, h_xor_self]
            have h_signed_eq : (BitVec.signed (fromIndex - 0#32) != fromIndex.signed - (0#32).signed) =
                ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) := rfl
            rw [h_signed_eq]
            rw [cmovg_start_idx_eval fromIndex]
            rw [BitVec.add_zero]
            have : (BitVec.ofNat 64 (if fromIndex.slt 0 = true then 0 else fromIndex.toNat)) =
                BitVec.ofNat 64 start_val_nat := rfl
            rw [this]
            have h_len_eval : BitVec.setWidth 64 (c.ushiftRight 1) = BitVec.ofNat 64 (c >>> 1).toNat := by
              have : (c >>> 1).toNat < 2 ^ 64 := by
                have := (c >>> 1).isLt; omega
              rw [BitVec.ofNat_toNat]
              bv_decide
            rw [h_len_eval]
            have h_sub_neg : BitVec.ofNat 64 (c >>> 1).toNat + -BitVec.ofNat 64 start_val_nat =
                BitVec.ofNat 64 (c >>> 1).toNat - BitVec.ofNat 64 start_val_nat := by bv_decide
            rw [h_sub_neg]
            rw [ofNat_sub_eq ((c >>> 1).toNat) start_val_nat (by omega) (by omega)]
            rw [hm1]
          · simp only [get64_set64,
              addr_sib2_disp', ofInt_signed_mul2, ofNat_mul2,
              hd_rdi_rax, hd_rdi_rcx, hd_rdi_len, hd_rdi_tmp, hd_rdi_start,
              hd_rax_rcx, hd_rax_len, hd_rax_tmp, hd_rax_start,
              hd_rcx_len, hd_rcx_tmp, hd_rcx_start,
              hd_len_tmp, hd_len_start,
              hd_tmp_start,
              Ne.symm hd_rdi_rax, Ne.symm hd_rdi_rcx, Ne.symm hd_rdi_len, Ne.symm hd_rdi_tmp, Ne.symm hd_rdi_start,
              Ne.symm hd_rax_rcx, Ne.symm hd_rax_len, Ne.symm hd_rax_tmp, Ne.symm hd_rax_start,
              Ne.symm hd_rcx_len, Ne.symm hd_rcx_tmp, Ne.symm hd_rcx_start,
              Ne.symm hd_len_tmp, Ne.symm hd_len_start,
              Ne.symm hd_tmp_start,
              ↓reduceIte]
            have h_xor_self : BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) ^^^ BitVec.setWidth 32 (s.regs.get64 Reg64.rcx) = 0#32 := by bv_decide
            have h_from_eq : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
            rw [h_from_eq, h_xor_self]
            have h_signed_eq : (BitVec.signed (fromIndex - 0#32) != fromIndex.signed - (0#32).signed) =
                ((fromIndex - 0#32).toInt != fromIndex.toInt - (0#32).toInt) := rfl
            rw [h_signed_eq]
            rw [cmovg_start_idx_eval fromIndex]
            rw [Nat.add_zero]
            have : (BitVec.ofNat 64 (if fromIndex.slt 0 = true then 0 else fromIndex.toNat)) =
                BitVec.ofNat 64 start_val_nat := rfl
            rw [this]
            rw [ofNat_mul2]
            ac_rfl
          · have : Reg64.rax ≠ .rdi := by decide
            have : Reg64.rax ≠ .rcx := by decide
            have : Reg64.rax ≠ len := hd_rax_len
            have : Reg64.rax ≠ tmp := hd_rax_tmp
            simp only [Reg64s.get, Reg.base, Reg.offset, get64_set64, set_low64, get_low64, this, hd_rax_rdi, hd_rax_rcx, hd_rax_len, hd_rax_tmp, ↓reduceIte]
            exact rax_w16_eq s ch hch_def
          · simp only [get_low32, get64_set64, hd_len_rdi, hd_len_rcx, ↓reduceIte]
            exact len_eval_simple c

end

end Kraken.X64.Art
