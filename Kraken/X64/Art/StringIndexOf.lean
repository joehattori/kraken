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
public import Kraken.X64.Art.StringEquals
public import Kraken.X64.Art.StringIndexOfSpec
public import Kraken.ToBytes

open Std
open Std.WP
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/--
AVX2 assembly template for `String.indexOf(ch)` (`start_at_zero = true`).
-/
@[expose] public def stringIndexOfProg (slow : Label)
    (str search_value out : Reg64)
    (temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256) : _root_.Program := parse("
    # 0. Check code point > 0xFFFF:
    cmpl $65535, %❰.low search_value .W32❱
    ❰.instr (.regular .W64 .W64 (.jcc .a slow))❱

    # 2. Load count_
    movl 8(%❰str❱), %❰.low temp_len .W32❱
    testl %❰.low temp_len .W32❱, %❰.low temp_len .W32❱      # 3
    je not_found                                            # 4

    movl %❰.low temp_len .W32❱, %❰.low temp_mask .W32❱      # 5
    shrl $1, %❰.low temp_len .W32❱                          # 6

    xorq %❰.low temp_offset .W64❱, %❰.low temp_offset .W64❱  # 7

    movl %❰.low temp_len .W32❱, %ecx                        # 8
    subl %❰.low temp_offset .W32❱, %ecx                     # 9

    testl $1, %❰.low temp_mask .W32❱                        # 10
    jne uncompressed_path                                   # 11

    # === COMPRESSED PATH ===
    cmpl $127, %❰.low search_value .W32❱                    # 12
    jg not_found                                            # 13

    cmpl $32, %❰.low temp_len .W32❱                         # 14
    jb compressed_scalar_loop                               # 15

    # 16. vmovd search_value, ymm_match
    ❰.instr (.avx .W64 .W256 (.vmovIn .W32 ymm_match (.reg (.low search_value .W32))))❱
    vpbroadcastb %❰ymm_match❱, %❰ymm_target❱                # 17

    cmpl $32, %ecx                                          # 18
    jb compressed_tail                                      # 19

  compressed_avx_loop:                                      # 20
    # 21. vpcmpeqb 16(str, temp_offset, 1), ymm_target, ymm_match
    vpcmpeqb 16(%❰str❱,%❰temp_offset❱,1), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 22
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 23
    jne compressed_match_found                              # 24
    addq $32, %❰.low temp_offset .W64❱                      # 25
    subl $32, %ecx                                          # 26
    cmpl $32, %ecx                                          # 27
    jae compressed_avx_loop                                 # 28

  compressed_tail:                                          # 29
    testl %ecx, %ecx                                        # 30
    je not_found_vzero                                      # 31

    # 32. vpcmpeqb -16(str, temp_len, 1), ymm_target, ymm_match
    vpcmpeqb -16(%❰str❱,%❰temp_len❱,1), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 33
    negl %ecx                                               # 34
    addl $32, %ecx                                          # 35
    shrl %cl, %❰.low temp_mask .W32❱                        # 36
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 37
    je not_found_vzero                                      # 38
    bsf %❰.low temp_mask .W32❱, %ecx                        # 39
    addl %ecx, %❰.low temp_offset .W32❱                     # 40
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 41
    vzeroupper                                              # 42
    jmp done                                                # 43

  compressed_match_found:                                   # 44
    bsf %❰.low temp_mask .W32❱, %ecx                        # 45
    addl %ecx, %❰.low temp_offset .W32❱                     # 46
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 47
    vzeroupper                                              # 48
    jmp done                                                # 49

  compressed_scalar_loop:                                   # 50
    # 51. movzxb 16(str, temp_offset, 1), temp_mask
    movzbl 16(%❰str❱,%❰temp_offset❱,1), %❰.low temp_mask .W32❱
    cmpl %❰.low temp_mask .W32❱, %❰.low search_value .W32❱  # 52
    je compressed_scalar_found                              # 53
    addq $1, %❰.low temp_offset .W64❱                       # 54
    subl $1, %ecx                                           # 55
    jne compressed_scalar_loop                              # 56
    jmp not_found                                           # 57

  compressed_scalar_found:                                  # 58
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 59
    jmp done                                                # 60

  # === UNCOMPRESSED PATH ===
  uncompressed_path:                                        # 61
    cmpl $16, %❰.low temp_len .W32❱                         # 62
    jb uncompressed_scalar_loop                             # 63

    # 64. vmovd search_value, ymm_match
    ❰.instr (.avx .W64 .W256 (.vmovIn .W32 ymm_match (.reg (.low search_value .W32))))❱
    vpbroadcastw %❰ymm_match❱, %❰ymm_target❱                # 65

    cmpl $16, %ecx                                          # 66
    jb uncompressed_tail                                    # 67

  uncompressed_avx_loop:                                    # 68
    # 69. vpcmpeqw 16(str, temp_offset, 2), ymm_target, ymm_match
    vpcmpeqw 16(%❰str❱,%❰temp_offset❱,2), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 70
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 71
    jne uncompressed_match_found                            # 72
    addq $16, %❰.low temp_offset .W64❱                      # 73
    subl $16, %ecx                                          # 74
    cmpl $16, %ecx                                          # 75
    jae uncompressed_avx_loop                               # 76

  uncompressed_tail:                                        # 77
    testl %ecx, %ecx                                        # 78
    je not_found_vzero                                      # 79

    # 80. vpcmpeqw -16(str, temp_len, 2), ymm_target, ymm_match
    vpcmpeqw -16(%❰str❱,%❰temp_len❱,2), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 81
    shll $1, %ecx                                           # 82
    negl %ecx                                               # 83
    addl $32, %ecx                                          # 84
    shrl %cl, %❰.low temp_mask .W32❱                        # 85
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 86
    je not_found_vzero                                      # 87
    bsf %❰.low temp_mask .W32❱, %ecx                        # 88
    shrl $1, %ecx                                           # 89
    addl %ecx, %❰.low temp_offset .W32❱                     # 90
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 91
    vzeroupper                                              # 92
    jmp done                                                # 93

  uncompressed_match_found:                                 # 94
    bsf %❰.low temp_mask .W32❱, %ecx                        # 95
    shrl $1, %ecx                                           # 96
    addl %ecx, %❰.low temp_offset .W32❱                     # 97
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 98
    vzeroupper                                              # 99
    jmp done                                                # 100

  uncompressed_scalar_loop:                                 # 101
    # 102. movzxw 16(str, temp_offset, 2), temp_mask
    movzwl 16(%❰str❱,%❰temp_offset❱,2), %❰.low temp_mask .W32❱
    cmpl %❰.low temp_mask .W32❱, %❰.low search_value .W32❱  # 103
    je uncompressed_scalar_found                            # 104
    addq $1, %❰.low temp_offset .W64❱                       # 105
    subl $1, %ecx                                           # 106
    jne uncompressed_scalar_loop                            # 107
    jmp not_found                                           # 108

  uncompressed_scalar_found:                                # 109
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 110
    jmp done                                                # 111

  not_found_vzero:                                          # 112
    vzeroupper                                              # 113

  not_found:                                                # 114
    movl $-1, %❰.low out .W32❱                              # 115

  done:                                                     # 116
")

/--
AVX2 assembly template for `String.indexOf(ch, fromIndex)` (`start_at_zero = false`).
-/
@[expose] public def stringIndexOfAfterProg (slow : Label)
    (str search_value start_idx out : Reg64)
    (temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256) : _root_.Program := parse("
    # 0. Check code point > 0xFFFF:
    cmpl $65535, %❰.low search_value .W32❱
    ❰.instr (.regular .W64 .W64 (.jcc .a slow))❱

    # 2. Load count_
    movl 8(%❰str❱), %❰.low temp_len .W32❱
    testl %❰.low temp_len .W32❱, %❰.low temp_len .W32❱      # 3
    je not_found                                            # 4

    movl %❰.low temp_len .W32❱, %❰.low temp_mask .W32❱      # 5
    shrl $1, %❰.low temp_len .W32❱                          # 6

    cmpl %❰.low temp_len .W32❱, %❰.low start_idx .W32❱      # 7
    jge not_found                                           # 8

    xorq %❰.low temp_offset .W64❱, %❰.low temp_offset .W64❱  # 9
    cmpl $0, %❰.low start_idx .W32❱                         # 10
    cmovg %❰.low start_idx .W32❱, %❰.low temp_offset .W32❱  # 11

    movl %❰.low temp_len .W32❱, %ecx                        # 12
    subl %❰.low temp_offset .W32❱, %ecx                     # 13

    testl $1, %❰.low temp_mask .W32❱                        # 14
    jne uncompressed_path                                   # 15

    # === COMPRESSED PATH ===
    cmpl $127, %❰.low search_value .W32❱                    # 16
    jg not_found                                            # 17

    cmpl $32, %❰.low temp_len .W32❱                         # 18
    jb compressed_scalar_loop                               # 19

    # 20. vmovd search_value, ymm_match
    ❰.instr (.avx .W64 .W256 (.vmovIn .W32 ymm_match (.reg (.low search_value .W32))))❱
    vpbroadcastb %❰ymm_match❱, %❰ymm_target❱                # 21

    cmpl $32, %ecx                                          # 22
    jb compressed_tail                                      # 23

  compressed_avx_loop:                                      # 24
    # 25. vpcmpeqb 16(str, temp_offset, 1), ymm_target, ymm_match
    vpcmpeqb 16(%❰str❱,%❰temp_offset❱,1), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 26
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 27
    jne compressed_match_found                              # 28
    addq $32, %❰.low temp_offset .W64❱                      # 29
    subl $32, %ecx                                          # 30
    cmpl $32, %ecx                                          # 31
    jae compressed_avx_loop                                 # 32

  compressed_tail:                                          # 33
    testl %ecx, %ecx                                        # 34
    je not_found_vzero                                      # 35

    # 36. vpcmpeqb -16(str, temp_len, 1), ymm_target, ymm_match
    vpcmpeqb -16(%❰str❱,%❰temp_len❱,1), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 37
    negl %ecx                                               # 38
    addl $32, %ecx                                          # 39
    shrl %cl, %❰.low temp_mask .W32❱                        # 40
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 41
    je not_found_vzero                                      # 42
    bsf %❰.low temp_mask .W32❱, %ecx                        # 43
    addl %ecx, %❰.low temp_offset .W32❱                     # 44
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 45
    vzeroupper                                              # 46
    jmp done                                                # 47

  compressed_match_found:                                   # 48
    bsf %❰.low temp_mask .W32❱, %ecx                        # 49
    addl %ecx, %❰.low temp_offset .W32❱                     # 50
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 51
    vzeroupper                                              # 52
    jmp done                                                # 53

  compressed_scalar_loop:                                   # 54
    # 55. movzxb 16(str, temp_offset, 1), temp_mask
    movzbl 16(%❰str❱,%❰temp_offset❱,1), %❰.low temp_mask .W32❱
    cmpl %❰.low temp_mask .W32❱, %❰.low search_value .W32❱  # 56
    je compressed_scalar_found                              # 57
    addq $1, %❰.low temp_offset .W64❱                       # 58
    subl $1, %ecx                                           # 59
    jne compressed_scalar_loop                              # 60
    jmp not_found                                           # 61

  compressed_scalar_found:                                  # 62
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 63
    jmp done                                                # 64

  # === UNCOMPRESSED PATH ===
  uncompressed_path:                                        # 65
    cmpl $16, %❰.low temp_len .W32❱                         # 66
    jb uncompressed_scalar_loop                             # 67

    # 68. vmovd search_value, ymm_match
    ❰.instr (.avx .W64 .W256 (.vmovIn .W32 ymm_match (.reg (.low search_value .W32))))❱
    vpbroadcastw %❰ymm_match❱, %❰ymm_target❱                # 69

    cmpl $16, %ecx                                          # 70
    jb uncompressed_tail                                    # 71

  uncompressed_avx_loop:                                    # 72
    # 73. vpcmpeqw 16(str, temp_offset, 2), ymm_target, ymm_match
    vpcmpeqw 16(%❰str❱,%❰temp_offset❱,2), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 74
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 75
    jne uncompressed_match_found                            # 76
    addq $16, %❰.low temp_offset .W64❱                      # 77
    subl $16, %ecx                                          # 78
    cmpl $16, %ecx                                          # 79
    jae uncompressed_avx_loop                               # 80

  uncompressed_tail:                                        # 81
    testl %ecx, %ecx                                        # 82
    je not_found_vzero                                      # 83

    # 84. vpcmpeqw -16(str, temp_len, 2), ymm_target, ymm_match
    vpcmpeqw -16(%❰str❱,%❰temp_len❱,2), %❰ymm_target❱, %❰ymm_match❱
    vpmovmskb %❰ymm_match❱, %❰.low temp_mask .W32❱          # 85
    shll $1, %ecx                                           # 86
    negl %ecx                                               # 87
    addl $32, %ecx                                          # 88
    shrl %cl, %❰.low temp_mask .W32❱                        # 89
    testl %❰.low temp_mask .W32❱, %❰.low temp_mask .W32❱    # 90
    je not_found_vzero                                      # 91
    bsf %❰.low temp_mask .W32❱, %ecx                        # 92
    shrl $1, %ecx                                           # 93
    addl %ecx, %❰.low temp_offset .W32❱                     # 94
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 95
    vzeroupper                                              # 96
    jmp done                                                # 97

  uncompressed_match_found:                                 # 98
    bsf %❰.low temp_mask .W32❱, %ecx                        # 99
    shrl $1, %ecx                                           # 100
    addl %ecx, %❰.low temp_offset .W32❱                     # 101
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 102
    vzeroupper                                              # 103
    jmp done                                                # 104

  uncompressed_scalar_loop:                                 # 105
    # 106. movzxw 16(str, temp_offset, 2), temp_mask
    movzwl 16(%❰str❱,%❰temp_offset❱,2), %❰.low temp_mask .W32❱
    cmpl %❰.low temp_mask .W32❱, %❰.low search_value .W32❱  # 107
    je uncompressed_scalar_found                            # 108
    addq $1, %❰.low temp_offset .W64❱                       # 109
    subl $1, %ecx                                           # 110
    jne uncompressed_scalar_loop                            # 111
    jmp not_found                                           # 112

  uncompressed_scalar_found:                                # 113
    movl %❰.low temp_offset .W32❱, %❰.low out .W32❱         # 114
    jmp done                                                # 115

  not_found_vzero:                                          # 116
    vzeroupper                                              # 117

  not_found:                                                # 118
    movl $-1, %❰.low out .W32❱                              # 119

  done:                                                     # 120
")

namespace Proof

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

theorem byte_of_bytes (b : UInt8) : BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  dsimp [Int.ofBytes, UInt8.toBitVec]
  simp [BitVec.toNat_setWidth]

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

theorem ret_slow [Host] (slow : Label) (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (chars : List (BitVec 16)) (fromIndex : BitVec 32)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (ch : BitVec 32) (h_ch : ch.toNat > 65535)
    (h_search : t.regs.get (Reg.low search_value Width.W32) = ch)
    (h_regs : t.regs = s.regs)
    (h_mem : t.dmem = s.dmem)
    (h_zmms : t.zmms = s.zmms)
    (hslow : IsSlowPathLabel (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H slow) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
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
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  sstep
  rw [get_low32] at h_search
  rw [h_search]
  refine Program.loopCont_of_le (j := 1) (by rw [h_prog_len]; omega) ?_
  sstep
  rw [h_cond]
  simp only [↓reduceIte]
  change Program.LoopCont _ _ _ _ ⟨_, label slow⟩
  unfold Program.LoopCont
  by_cases h : label slow = H.endAddr ∨ (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).IsLabelAddr (label slow) ∨
      (∃ i < (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length, label slow = Host.addrOf (H.start + i))
  · exact False.elim (hslow h)
  · simp only [h, ↓reduceIte]
    refine ⟨rfl, h_ch, h_regs, h_mem, h_zmms⟩

theorem ret_slow_after [Host] (slow : Label) (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256) (chars : List (BitVec 16)) (fromIndex : BitVec 32)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (ch : BitVec 32) (h_ch : ch.toNat > 65535)
    (h_search : t.regs.get (Reg.low search_value Width.W32) = ch)
    (h_regs : t.regs = s.regs)
    (h_mem : t.dmem = s.dmem)
    (h_zmms : t.zmms = s.zmms)
    (hslow : IsSlowPathLabel (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H slow) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
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
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  sstep
  rw [get_low32] at h_search
  rw [h_search]
  refine Program.loopCont_of_le (j := 1) (by rw [h_prog_len]; omega) ?_
  sstep
  rw [h_cond]
  simp only [↓reduceIte]
  change Program.LoopCont _ _ _ _ ⟨_, label slow⟩
  unfold Program.LoopCont
  by_cases h : label slow = H.endAddr ∨ (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).IsLabelAddr (label slow) ∨
      (∃ i < (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length, label slow = Host.addrOf (H.start + i))
  · exact False.elim (hslow h)
  · simp only [h, ↓reduceIte]
    refine ⟨rfl, h_ch, h_regs, h_mem, h_zmms⟩

theorem ret_not_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 114)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  -- Directive 114: .label "not_found"
  sstep
  refine Program.loopCont_of_le (j := 115) (by rw [h_prog_len]; omega) ?_
  -- Directive 115: movl $-1, out
  sstep
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec]
    bv_decide
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)

theorem ret_not_found_vzero [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 112)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  -- Directive 112: .label "not_found_vzero"
  sstep
  refine Program.loopCont_of_le (j := 113) (by rw [h_prog_len]; omega) ?_
  -- Directive 113: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
  obtain ⟨v1, v2, hv⟩ := hz
  exact ret_not_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
    h_distinct H s _ chars ch fromIndex hspec hm hr (Or.inr ⟨v1, v2, by rw [hv]⟩)
theorem ret_compressed_scalar_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
    (hoff : BitVec.setWidth 32 (t.regs.get64 temp_offset) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 58)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  -- Directive 58: .label "compressed_scalar_found"
  sstep
  refine Program.loopCont_of_le (j := 59) (by rw [h_prog_len]; omega) ?_
  -- Directive 59: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 60) (by rw [h_prog_len]; omega) ?_
  -- Directive 60: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec, hoff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)
theorem bsf_add_trunc (A : BitVec 64) (B : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (B + BitVec.setWidth 32 A)) =
      BitVec.setWidth 32 (A + B.zeroExtend 64) := by
  bv_decide

theorem ret_compressed_avx_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + (BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 44)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 44: .label "compressed_match_found"
  sstep
  refine Program.loopCont_of_le (j := 45) (by rw [h_prog_len]; omega) ?_
  -- Directive 45: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 46) (by rw [h_prog_len]; omega) ?_
  -- Directive 46: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 47) (by rw [h_prog_len]; omega) ?_
  -- Directive 47: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 48) (by rw [h_prog_len]; omega) ?_
  -- Directive 48: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 49) (by rw [h_prog_len]; omega) ?_
  -- Directive 49: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)

theorem ret_compressed_tail_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + (BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 39)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 39: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 40) (by rw [h_prog_len]; omega) ?_
  -- Directive 40: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 41) (by rw [h_prog_len]; omega) ?_
  -- Directive 41: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 42) (by rw [h_prog_len]; omega) ?_
  -- Directive 42: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 43) (by rw [h_prog_len]; omega) ?_
  -- Directive 43: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)


theorem bsf_shr1_add_trunc (A : BitVec 64) (B : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (B.ushiftRight 1 + BitVec.setWidth 32 A)) =
      BitVec.setWidth 32 (A + (B >>> 1).zeroExtend 64) := by
  bv_decide

theorem ret_uncompressed_avx_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + ((BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))) >>> 1).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 94)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 94: .label "uncompressed_match_found"
  sstep
  refine Program.loopCont_of_le (j := 95) (by rw [h_prog_len]; omega) ?_
  -- Directive 95: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 96) (by rw [h_prog_len]; omega) ?_
  -- Directive 96: shrl $1, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 97) (by rw [h_prog_len]; omega) ?_
  -- Directive 97: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 98) (by rw [h_prog_len]; omega) ?_
  -- Directive 98: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 99) (by rw [h_prog_len]; omega) ?_
  -- Directive 99: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 100) (by rw [h_prog_len]; omega) ?_
  -- Directive 100: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_shr1_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)

theorem ret_uncompressed_scalar_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
    (hoff : BitVec.setWidth 32 (t.regs.get64 temp_offset) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 109)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  sstep
  refine Program.loopCont_of_le (j := 110) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 111) (by rw [h_prog_len]; omega) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec, hoff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)




theorem ret_uncompressed_tail_found [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + ((BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))) >>> 1).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 88)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 88: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 89) (by rw [h_prog_len]; omega) ?_
  -- Directive 89: shrl $1, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 90) (by rw [h_prog_len]; omega) ?_
  -- Directive 90: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 91) (by rw [h_prog_len]; omega) ?_
  -- Directive 91: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 92) (by rw [h_prog_len]; omega) ?_
  -- Directive 92: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 93) (by rw [h_prog_len]; omega) ?_
  -- Directive 93: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 116) rfl]
  refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
  -- Directive 116: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_shr1_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)


theorem ret_not_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 118)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  sstep
  refine Program.loopCont_of_le (j := 119) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec]
    bv_decide
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)

theorem ret_not_found_vzero_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = -1#32)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 116)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  sstep
  refine Program.loopCont_of_le (j := 117) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
  obtain ⟨v1, v2, hv⟩ := hz
  exact ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
    h_distinct H s _ chars ch fromIndex hspec hm hr (Or.inr ⟨v1, v2, by rw [hv]⟩)

theorem ret_compressed_scalar_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
    (hoff : BitVec.setWidth 32 (t.regs.get64 temp_offset) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 62)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  sstep
  refine Program.loopCont_of_le (j := 63) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 64) (by rw [h_prog_len]; omega) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec, hoff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)

theorem ret_compressed_avx_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + (BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 48)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -, -⟩,
          ⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  sstep
  refine Program.loopCont_of_le (j := 49) (by rw [h_prog_len]; omega) ?_
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 50) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 51) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 52) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 53) (by rw [h_prog_len]; omega) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)

theorem ret_compressed_tail_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + (BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 43)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -, -⟩,
          ⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 43: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 44) (by rw [h_prog_len]; omega) ?_
  -- Directive 44: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 45) (by rw [h_prog_len]; omega) ?_
  -- Directive 45: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 46) (by rw [h_prog_len]; omega) ?_
  -- Directive 46: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 47) (by rw [h_prog_len]; omega) ?_
  -- Directive 47: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  -- Directive 120: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)


theorem ret_uncompressed_scalar_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (_h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
    (hoff : BitVec.setWidth 32 (t.regs.get64 temp_offset) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 113)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  sstep
  refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 115) (by rw [h_prog_len]; omega) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  refine ⟨?_, ?_, hm, hz⟩
  · simp only [get_low32, get64_set64, hspec, hoff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    simp only [get64_set64, hr_out.1, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with h | h | h | h | h
      · exact hr_out.1 h
      · exact hr_out.2.1 h
      · exact hr_out.2.2.1 h
      · exact hr_out.2.2.2.1 h
      · exact hr_out.2.2.2.2 h)

theorem ret_uncompressed_avx_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + ((BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))) >>> 1).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 98)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -, -⟩,
          ⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  sstep
  refine Program.loopCont_of_le (j := 99) (by rw [h_prog_len]; omega) ?_
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 100) (by rw [h_prog_len]; omega) ?_
  sstep
  intro _
  refine Program.loopCont_of_le (j := 101) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 102) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 103) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 104) (by rw [h_prog_len]; omega) ?_
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_shr1_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)


theorem ret_uncompressed_tail_found_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s t : MachineData)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32)
    (idx : BitVec 32)
    (hspec : indexOfSpec chars ch fromIndex = idx)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm1 v1).set ymm2 v2)
    (h_mask_ne : BitVec.setWidth 32 (t.regs.get64 temp_mask) ≠ 0#32)
    (h_match_idx : BitVec.setWidth 32 (t.regs.get64 temp_offset + ((BitVec.bsf (BitVec.setWidth 32 (t.regs.get64 temp_mask))) >>> 1).zeroExtend 64) = idx) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 92)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨-, -, -, -, -, -, -⟩,
          ⟨-, -, -, -, -, -⟩,
          ⟨-, -, -, -, -⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  -- Directive 92: bsfl temp_mask, %ecx
  sstep
  have h_mask_cond : (BitVec.setWidth 32 (t.regs.get64 temp_mask) == 0#32) = false := by
    simp [h_mask_ne]
  simp only [h_mask_cond, Bool.false_eq_true, ↓reduceIte]
  -- CF, PF, AF, SF, and OF are undefined after `bsf`
  intro _ _ _ _ _
  simp only [Effects.All]
  refine Program.loopCont_of_le (j := 93) (by rw [h_prog_len]; omega) ?_
  -- Directive 93: shrl $1, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 94) (by rw [h_prog_len]; omega) ?_
  -- Directive 94: addl %ecx, temp_offset
  sstep
  refine Program.loopCont_of_le (j := 95) (by rw [h_prog_len]; omega) ?_
  -- Directive 95: movl temp_offset, out
  sstep
  refine Program.loopCont_of_le (j := 96) (by rw [h_prog_len]; omega) ?_
  -- Directive 96: vzeroupper
  sstep
  refine Program.loopCont_of_le (j := 97) (by rw [h_prog_len]; omega) ?_
  -- Directive 97: jmp done
  sstep
  simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 120) rfl]
  refine Program.loopCont_of_le (j := 120) (by rw [h_prog_len]; omega) ?_
  -- Directive 120: .label "done"
  sstep
  refine Program.loopCont_of_le (j := 121) (by rw [h_prog_len]; omega) ?_
  refine Program.loop_done ?_
  dsimp [StringIndexOfPost]
  obtain ⟨v1, v2, hv⟩ := hz
  refine ⟨?_, ?_, hm, Or.inr ⟨v1, v2, by rw [hv]⟩⟩
  · simp only [get_low32, get64_set64, Ne.symm hd_rcx_offset, ↓reduceIte]
    rw [bsf_shr1_add_trunc, h_match_idx, hspec]
  · intro r hr_out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
    have h1 : r ≠ out := hr_out.1
    have h2 : r ≠ Reg64.rcx := hr_out.2.1
    have h3 : r ≠ temp_len := hr_out.2.2.1
    have h4 : r ≠ temp_offset := hr_out.2.2.2.1
    have h5 : r ≠ temp_mask := hr_out.2.2.2.2
    simp only [get64_set64, h1, h2, h4, ↓reduceIte]
    exact hr r (by
      intro h_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
      rcases h_in with rfl | rfl | rfl | rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact h4 rfl
      · exact h5 rfl)


theorem compressed_scalar_loop_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ m k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
      (h_search : t.regs.get (.low search_value .W32) = ch)
      (h_off : t.regs.get64 temp_offset = .ofNat 64 k)
      (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 (m + 1))
      (hk : k + (m + 1) = T)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 50)⟩ := by
  intro m
  induction m with
  | zero =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : k + 1 ≤ T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm, load_chunk _ _ k 1 T h_some (by omega)]
      have : (List.range 1).map (fun j => byteAt s.dmem A (k + j)) = [byteAt s.dmem A k] := rfl
      rw [this]
    -- Directive 50: .label "compressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 51) (by rw [h_prog_len]; omega) ?_
    -- Directive 51: movzxb 16(str, temp_offset, 1), temp_mask
    sstep
    simp only [addr_sib1_disp', hstr, h_off]
    rw [← haddr, hload]
    dsimp only []
    rw [byte_of_bytes, h_data k (by omega)]
    refine Program.loopCont_of_le (j := 52) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 52: cmpl temp_mask, search_value
    sstep
    simp only [get64_set64, hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 53) (by rw [h_prog_len]; omega) ?_
    -- Directive 53: je compressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 58) rfl]
      refine Program.loopCont_of_le (j := 58) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_compressed_scalar_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 54) (by rw [h_prog_len]; omega) ?_
      -- Directive 54: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 55) (by rw [h_prog_len]; omega) ?_
      -- Directive 55: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 56) (by rw [h_prog_len]; omega) ?_
      -- Directive 56: jnz compressed_scalar_loop
      sstep
      simp only [get64_set64, hd_rcx_offset, hd_rcx_mask, h_rcx, ↓reduceIte]
      refine Program.loopCont_of_le (j := 57) (by rw [h_prog_len]; omega) ?_
      -- Directive 57: jmp not_found
      sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 114) rfl]
      refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_none : ∀ (i : Nat) (hi : i < (chars.drop from_k).length),
            decide (((chars.drop from_k).get ⟨i, hi⟩).zeroExtend 32 = ch) = false := by
          intro i hi
          rw [List.length_drop, h_len] at hi
          simp only [decide_eq_false_iff_not]
          by_cases hi_lt : i < k - from_k
          · exact hpre i hi_lt
          · have hi_eq : i = k - from_k := by omega
            subst hi_eq
            have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
                chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
            rw [this]
            have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
              ext; exact Nat.add_sub_of_le h_from_k
            have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
              congr 1
            rw [this]
            exact heq
        have h_find := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) h_none
        rw [h_find]
      refine ret_not_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct H s _ chars ch fromIndex hspec hm ?_ hz
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      have h1 : r ≠ out := hr_out.1
      have h2 : r ≠ Reg64.rcx := hr_out.2.1
      have h3 : r ≠ temp_len := hr_out.2.2.1
      have h4 : r ≠ temp_offset := hr_out.2.2.2.1
      have h5 : r ≠ temp_mask := hr_out.2.2.2.2
      simp only [get64_set64, h2, h4, h5, ↓reduceIte]
      exact hr r (by
        intro h_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
        rcases h_in with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
        · exact h3 rfl
        · exact h4 rfl
        · exact h5 rfl)
  | succ m ih =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : k + 1 ≤ T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm, load_chunk _ _ k 1 T h_some (by omega)]
      have : (List.range 1).map (fun j => byteAt s.dmem A (k + j)) = [byteAt s.dmem A k] := rfl
      rw [this]
    -- Directive 50: .label "compressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 51) (by rw [h_prog_len]; omega) ?_
    -- Directive 51: movzxb 16(str, temp_offset, 1), temp_mask
    sstep
    simp only [hstr, h_off]
    rw [← haddr, hload]
    dsimp only []
    rw [byte_of_bytes, h_data k (by omega)]
    refine Program.loopCont_of_le (j := 52) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 52: cmpl temp_mask, search_value
    sstep
    simp only [hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 53) (by rw [h_prog_len]; omega) ?_
    -- Directive 53: je compressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, addrOf_label hlab (H := H) (i := 58) rfl]
      refine Program.loopCont_of_le (j := 58) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_compressed_scalar_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 54) (by rw [h_prog_len]; omega) ?_
      -- Directive 54: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 55) (by rw [h_prog_len]; omega) ?_
      -- Directive 55: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 56) (by rw [h_prog_len]; omega) ?_
      -- Directive 56: jnz compressed_scalar_loop
      sstep
      have hzf_sub : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) - 1#32 == 0#32) = false := by
        rw [h_rcx]
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [hd_rcx_offset, hd_rcx_mask, hzf_sub, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 50) rfl]
      refine Program.loopCont_of_le (j := 50) (by rw [h_prog_len]; omega) ?_
      have hpre_step : ∀ (i : Nat) (hi : i < k + 1 - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        by_cases hi_lt : i < k - from_k
        · exact hpre i hi_lt
        · have hi_eq : i = k - from_k := by omega
          subst hi_eq
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
      refine ih (k + 1) _ hm ?_ hz ?_ ?_ ?_ (by omega) (by omega) hpre_step
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h1 : r ≠ out := hr_out.1
        have h2 : r ≠ Reg64.rcx := hr_out.2.1
        have h3 : r ≠ temp_len := hr_out.2.2.1
        have h4 : r ≠ temp_offset := hr_out.2.2.2.1
        have h5 : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h2, h4, h5, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
          · exact h3 rfl
          · exact h4 rfl
          · exact h5 rfl)
      · rw [get_low32]
        simp only [get64_set64, hd_search_rcx, hd_search_offset, hd_search_mask, ↓reduceIte]
        exact h_search32
      · simp only [get64_set64, Ne.symm hd_rcx_offset, hd_offset_mask, ↓reduceIte, h_off]
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 by rfl, ofNat_add_lit]
      · simp only [get64_set64, sw32_64, ↓reduceIte, h_rcx]
        rw [ofNat_succ_sub_one (m + 1)]


theorem compressed_scalar_loop_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ m k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
      (h_search : t.regs.get (.low search_value .W32) = ch)
      (h_off : t.regs.get64 temp_offset = .ofNat 64 k)
      (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 (m + 1))
      (hk : k + (m + 1) = T)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 54)⟩ := by
  intro m
  induction m with
  | zero =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : k + 1 ≤ T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm, load_chunk _ _ k 1 T h_some (by omega)]
      have : (List.range 1).map (fun j => byteAt s.dmem A (k + j)) = [byteAt s.dmem A k] := rfl
      rw [this]
    -- Directive 54: .label "compressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 55) (by rw [h_prog_len]; omega) ?_
    -- Directive 55: movzxb 16(str, temp_offset, 1), temp_mask
    sstep
    simp only [addr_sib1_disp', hstr, h_off]
    rw [← haddr, hload]
    dsimp only []
    rw [byte_of_bytes, h_data k (by omega)]
    refine Program.loopCont_of_le (j := 56) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 56: cmpl temp_mask, search_value
    sstep
    simp only [get64_set64, hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 57) (by rw [h_prog_len]; omega) ?_
    -- Directive 57: je compressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 62) rfl]
      refine Program.loopCont_of_le (j := 62) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_compressed_scalar_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 58) (by rw [h_prog_len]; omega) ?_
      -- Directive 58: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 59) (by rw [h_prog_len]; omega) ?_
      -- Directive 59: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 60) (by rw [h_prog_len]; omega) ?_
      -- Directive 60: jnz compressed_scalar_loop
      sstep
      simp only [get64_set64, hd_rcx_offset, hd_rcx_mask, h_rcx, ↓reduceIte]
      refine Program.loopCont_of_le (j := 61) (by rw [h_prog_len]; omega) ?_
      -- Directive 61: jmp not_found
      sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 118) rfl]
      refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_none : ∀ (i : Nat) (hi : i < (chars.drop from_k).length),
            decide (((chars.drop from_k).get ⟨i, hi⟩).zeroExtend 32 = ch) = false := by
          intro i hi
          rw [List.length_drop, h_len] at hi
          simp only [decide_eq_false_iff_not]
          by_cases hi_lt : i < k - from_k
          · exact hpre i hi_lt
          · have hi_eq : i = k - from_k := by omega
            subst hi_eq
            have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
                chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
            rw [this]
            have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
              ext; exact Nat.add_sub_of_le h_from_k
            have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
              congr 1
            rw [this]
            exact heq
        have h_find := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) h_none
        rw [h_find]
      refine ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct H s _ chars ch fromIndex hspec hm ?_ hz
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      have h1 : r ≠ out := hr_out.1
      have h2 : r ≠ Reg64.rcx := hr_out.2.1
      have h3 : r ≠ temp_len := hr_out.2.2.1
      have h4 : r ≠ temp_offset := hr_out.2.2.2.1
      have h5 : r ≠ temp_mask := hr_out.2.2.2.2
      simp only [get64_set64, h2, h4, h5, ↓reduceIte]
      exact hr r (by
        intro h_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
        rcases h_in with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
        · exact h3 rfl
        · exact h4 rfl
        · exact h5 rfl)
  | succ m ih =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : k + 1 ≤ T := by omega
    have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 1 =
        some (Int.ofBytes [byteAt s.dmem A k]) := by
      rw [haddr, hm, load_chunk _ _ k 1 T h_some (by omega)]
      have : (List.range 1).map (fun j => byteAt s.dmem A (k + j)) = [byteAt s.dmem A k] := rfl
      rw [this]
    -- Directive 54: .label "compressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 55) (by rw [h_prog_len]; omega) ?_
    -- Directive 55: movzxb 16(str, temp_offset, 1), temp_mask
    sstep
    simp only [hstr, h_off]
    rw [← haddr, hload]
    dsimp only []
    rw [byte_of_bytes, h_data k (by omega)]
    refine Program.loopCont_of_le (j := 56) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 56: cmpl temp_mask, search_value
    sstep
    simp only [hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 57) (by rw [h_prog_len]; omega) ?_
    -- Directive 57: je compressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, addrOf_label hlab (H := H) (i := 62) rfl]
      refine Program.loopCont_of_le (j := 62) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_compressed_scalar_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) - (d.getD k 0).toBitVec.zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 58) (by rw [h_prog_len]; omega) ?_
      -- Directive 58: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 59) (by rw [h_prog_len]; omega) ?_
      -- Directive 59: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 60) (by rw [h_prog_len]; omega) ?_
      -- Directive 60: jnz compressed_scalar_loop
      sstep
      have hzf_sub : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) - 1#32 == 0#32) = false := by
        rw [h_rcx]
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [hd_rcx_offset, hd_rcx_mask, hzf_sub, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 54) rfl]
      refine Program.loopCont_of_le (j := 54) (by rw [h_prog_len]; omega) ?_
      have hpre_step : ∀ (i : Nat) (hi : i < k + 1 - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        by_cases hi_lt : i < k - from_k
        · exact hpre i hi_lt
        · have hi_eq : i = k - from_k := by omega
          subst hi_eq
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
      refine ih (k + 1) _ hm ?_ hz ?_ ?_ ?_ (by omega) (by omega) hpre_step
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h1 : r ≠ out := hr_out.1
        have h2 : r ≠ Reg64.rcx := hr_out.2.1
        have h3 : r ≠ temp_len := hr_out.2.2.1
        have h4 : r ≠ temp_offset := hr_out.2.2.2.1
        have h5 : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h2, h4, h5, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
          · exact h3 rfl
          · exact h4 rfl
          · exact h5 rfl)
      · rw [get_low32]
        simp only [get64_set64, hd_search_rcx, hd_search_offset, hd_search_mask, ↓reduceIte]
        exact h_search32
      · simp only [get64_set64, Ne.symm hd_rcx_offset, hd_offset_mask, ↓reduceIte, h_off]
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 by rfl, ofNat_add_lit]
      · simp only [get64_set64, sw32_64, ↓reduceIte, h_rcx]
        rw [ofNat_succ_sub_one (m + 1)]


theorem uncompressed_scalar_loop_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ m k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
      (h_search : t.regs.get (.low search_value .W32) = ch)
      (h_off : t.regs.get64 temp_offset = .ofNat 64 k)
      (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 (m + 1))
      (hk : k + (m + 1) = T)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 101)⟩ := by
  intro m
  induction m with
  | zero =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    -- Directive 101: .label "uncompressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 102) (by rw [h_prog_len]; omega) ?_
    -- Directive 102: movzxw 16(str, temp_offset, 2), temp_mask
    sstep
    simp only [addr_sib2_disp', ofInt_signed_mul2, ofNat_mul2, hstr, h_off]
    have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
    rw [this]
    have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + BitVec.ofNat 64 (2 * k) := by ac_rfl
    rw [h_addr_match, hload]
    dsimp only []
    rw [word_of_bytes, h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega)]
    refine Program.loopCont_of_le (j := 103) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 103: cmpl temp_mask, search_value
    sstep
    simp only [get64_set64, hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 104) (by rw [h_prog_len]; omega) ?_
    -- Directive 104: je uncompressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 109) rfl]
      refine Program.loopCont_of_le (j := 109) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_uncompressed_scalar_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 105) (by rw [h_prog_len]; omega) ?_
      sstep
      refine Program.loopCont_of_le (j := 106) (by rw [h_prog_len]; omega) ?_
      -- Directive 106: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 107) (by rw [h_prog_len]; omega) ?_
      -- Directive 107: jnz uncompressed_scalar_loop
      sstep
      simp only [get64_set64, hd_rcx_offset, hd_rcx_mask, h_rcx, ↓reduceIte]
      refine Program.loopCont_of_le (j := 108) (by rw [h_prog_len]; omega) ?_
      -- Directive 108: jmp not_found
      sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 114) rfl]
      refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_none : ∀ (i : Nat) (hi : i < (chars.drop from_k).length),
            decide (((chars.drop from_k).get ⟨i, hi⟩).zeroExtend 32 = ch) = false := by
          intro i hi
          rw [List.length_drop, h_len] at hi
          simp only [decide_eq_false_iff_not]
          by_cases hi_lt : i < k - from_k
          · exact hpre i hi_lt
          · have hi_eq : i = k - from_k := by omega
            subst hi_eq
            have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
                chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
            rw [this]
            have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
              ext; exact Nat.add_sub_of_le h_from_k
            have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
              congr 1
            rw [this]
            exact heq
        have h_find := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) h_none
        rw [h_find]
      refine ret_not_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct H s _ chars ch fromIndex hspec hm ?_ hz
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      have h1 : r ≠ out := hr_out.1
      have h2 : r ≠ Reg64.rcx := hr_out.2.1
      have h3 : r ≠ temp_len := hr_out.2.2.1
      have h4 : r ≠ temp_offset := hr_out.2.2.2.1
      have h5 : r ≠ temp_mask := hr_out.2.2.2.2
      simp only [get64_set64, h2, h4, h5, ↓reduceIte]
      exact hr r (by
        intro h_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
        rcases h_in with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
        · exact h3 rfl
        · exact h4 rfl
        · exact h5 rfl)
  | succ m ih =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2).length = 117 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    -- Directive 101: .label "uncompressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 102) (by rw [h_prog_len]; omega) ?_
    -- Directive 102: movzxw 16(str, temp_offset, 2), temp_mask
    sstep
    simp only [addr_sib2_disp', ofInt_signed_mul2, ofNat_mul2, hstr, h_off]
    have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
    rw [this]
    have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + BitVec.ofNat 64 (2 * k) := by ac_rfl
    rw [h_addr_match, hload]
    dsimp only []
    rw [word_of_bytes, h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega)]
    refine Program.loopCont_of_le (j := 103) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 103: cmpl temp_mask, search_value
    sstep
    simp only [hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 104) (by rw [h_prog_len]; omega) ?_
    -- Directive 104: je uncompressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, addrOf_label hlab (H := H) (i := 109) rfl]
      refine Program.loopCont_of_le (j := 109) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_uncompressed_scalar_found slow str search_value out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 105) (by rw [h_prog_len]; omega) ?_
      -- Directive 105: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 106) (by rw [h_prog_len]; omega) ?_
      -- Directive 106: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 107) (by rw [h_prog_len]; omega) ?_
      -- Directive 107: jnz uncompressed_scalar_loop
      sstep
      have hzf_sub : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) - 1#32 == 0#32) = false := by
        rw [h_rcx]
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [hd_rcx_offset, hd_rcx_mask, hzf_sub, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 101) rfl]
      refine Program.loopCont_of_le (j := 101) (by rw [h_prog_len]; omega) ?_
      have hpre_step : ∀ (i : Nat) (hi : i < k + 1 - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        by_cases hi_lt : i < k - from_k
        · exact hpre i hi_lt
        · have hi_eq : i = k - from_k := by omega
          subst hi_eq
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
      refine ih (k + 1) _ hm ?_ hz ?_ ?_ ?_ (by omega) (by omega) hpre_step
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h1 : r ≠ out := hr_out.1
        have h2 : r ≠ Reg64.rcx := hr_out.2.1
        have h3 : r ≠ temp_len := hr_out.2.2.1
        have h4 : r ≠ temp_offset := hr_out.2.2.2.1
        have h5 : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h2, h4, h5, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
          · exact h3 rfl
          · exact h4 rfl
          · exact h5 rfl)
      · rw [get_low32]
        simp only [get64_set64, hd_search_rcx, hd_search_offset, hd_search_mask, ↓reduceIte]
        exact h_search32
      · simp only [get64_set64, Ne.symm hd_rcx_offset, hd_offset_mask, ↓reduceIte, h_off]
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 by rfl, ofNat_add_lit]
      · simp only [get64_set64, sw32_64, ↓reduceIte, h_rcx]
        rw [ofNat_succ_sub_one (m + 1)]


theorem uncompressed_scalar_loop_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ m k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : t.zmms = s.zmms ∨ ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)
      (h_search : t.regs.get (.low search_value .W32) = ch)
      (h_off : t.regs.get64 temp_offset = .ofNat 64 k)
      (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 (m + 1))
      (hk : k + (m + 1) = T)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm1 ymm2 chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 105)⟩ := by
  intro m
  induction m with
  | zero =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    -- Directive 105: .label "uncompressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 106) (by rw [h_prog_len]; omega) ?_
    -- Directive 106: movzxw 16(str, temp_offset, 2), temp_mask
    sstep
    simp only [addr_sib2_disp', ofInt_signed_mul2, ofNat_mul2, hstr, h_off]
    have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
    rw [this]
    have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + BitVec.ofNat 64 (2 * k) := by ac_rfl
    rw [h_addr_match, hload]
    dsimp only []
    rw [word_of_bytes, h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega)]
    refine Program.loopCont_of_le (j := 107) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 107: cmpl temp_mask, search_value
    sstep
    simp only [get64_set64, hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 108) (by rw [h_prog_len]; omega) ?_
    -- Directive 108: je uncompressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 113) rfl]
      refine Program.loopCont_of_le (j := 113) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_uncompressed_scalar_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 109) (by rw [h_prog_len]; omega) ?_
      sstep
      refine Program.loopCont_of_le (j := 110) (by rw [h_prog_len]; omega) ?_
      -- Directive 110: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 111) (by rw [h_prog_len]; omega) ?_
      -- Directive 111: jnz uncompressed_scalar_loop
      sstep
      simp only [get64_set64, hd_rcx_offset, hd_rcx_mask, h_rcx, ↓reduceIte]
      refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
      -- Directive 112: jmp not_found
      sstep
      simp only [Int64.ofBitVec_toBitVec, i64_add_sub, addrOf_label hlab (H := H) (i := 118) rfl]
      refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = -1#32 := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_none : ∀ (i : Nat) (hi : i < (chars.drop from_k).length),
            decide (((chars.drop from_k).get ⟨i, hi⟩).zeroExtend 32 = ch) = false := by
          intro i hi
          rw [List.length_drop, h_len] at hi
          simp only [decide_eq_false_iff_not]
          by_cases hi_lt : i < k - from_k
          · exact hpre i hi_lt
          · have hi_eq : i = k - from_k := by omega
            subst hi_eq
            have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
                chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
            rw [this]
            have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
              ext; exact Nat.add_sub_of_le h_from_k
            have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
              congr 1
            rw [this]
            exact heq
        have h_find := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) h_none
        rw [h_find]
      refine ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct H s _ chars ch fromIndex hspec hm ?_ hz
      intro r hr_out
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
      have h1 : r ≠ out := hr_out.1
      have h2 : r ≠ Reg64.rcx := hr_out.2.1
      have h3 : r ≠ temp_len := hr_out.2.2.1
      have h4 : r ≠ temp_offset := hr_out.2.2.2.1
      have h5 : r ≠ temp_mask := hr_out.2.2.2.2
      simp only [get64_set64, h2, h4, h5, ↓reduceIte]
      exact hr r (by
        intro h_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
        rcases h_in with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
        · exact h3 rfl
        · exact h4 rfl
        · exact h5 rfl)
  | succ m ih =>
    intro k t hm hr hz h_search h_off h_rcx hk h_from_k hpre
    have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2).length = 121 := rfl
    have hd := h_distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
            ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
            ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
            ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
            ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
            ⟨hd_len_offset, hd_len_mask⟩,
            hd_offset_mask, -⟩ := hd
    have hstr : t.regs.get64 str = A := by
      rw [hA]
      exact hr str (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hd_str_out rfl
        · exact hd_str_rcx rfl
        · exact hd_str_len rfl
        · exact hd_str_offset rfl
        · exact hd_str_mask rfl)
    have hk_lt : 2 * k + 2 ≤ 2 * T := by omega
    have haddr : A + 16#64 + .ofNat 64 (2 * k) = A + .ofNat 64 (2 * k) + 16#64 := by ac_rfl
    have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 (2 * k)) 2 =
        some (Int.ofBytes [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)]) := by
      rw [haddr, hm, load_chunk _ _ (2 * k) 2 (2 * T) h_some (by omega)]
      have : (List.range 2).map (fun j => byteAt s.dmem A (2 * k + j)) =
          [byteAt s.dmem A (2 * k), byteAt s.dmem A (2 * k + 1)] := rfl
      rw [this]
    -- Directive 105: .label "uncompressed_scalar_loop"
    sstep
    refine Program.loopCont_of_le (j := 106) (by rw [h_prog_len]; omega) ?_
    -- Directive 106: movzxw 16(str, temp_offset, 2), temp_mask
    sstep
    simp only [addr_sib2_disp', ofInt_signed_mul2, ofNat_mul2, hstr, h_off]
    have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
    rw [this]
    have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + BitVec.ofNat 64 (2 * k) := by ac_rfl
    rw [h_addr_match, hload]
    dsimp only []
    rw [word_of_bytes, h_data (2 * k) (by omega), h_data (2 * k + 1) (by omega)]
    refine Program.loopCont_of_le (j := 107) (by rw [h_prog_len]; omega) ?_
    have h_search32 : BitVec.setWidth 32 (t.regs.get64 search_value) = ch := by
      rw [← get_low32, h_search]
    -- Directive 107: cmpl temp_mask, search_value
    sstep
    simp only [hd_search_mask, ↓reduceIte]
    refine Program.loopCont_of_le (j := 108) (by rw [h_prog_len]; omega) ?_
    -- Directive 108: je uncompressed_scalar_found
    sstep
    by_cases heq : (chars.get ⟨k, by omega⟩).zeroExtend 32 = ch
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = true := by
        rw [h_search32, sub_beq_zero, beq_iff_eq]
        have := h_chars k (by omega)
        rw [← this]
        exact heq.symm
      simp only [hzf, addrOf_label hlab (H := H) (i := 113) rfl]
      refine Program.loopCont_of_le (j := 113) (by rw [h_prog_len]; omega) ?_
      have hspec : indexOfSpec chars ch fromIndex = BitVec.ofNat 32 k := by
        dsimp only [indexOfSpec]
        rw [h_from_eq]
        have h_char_k : ((chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
        have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
          (chars.drop from_k) (k - from_k) (by rw [List.length_drop, h_len]; omega)
          (by simp only [decide_eq_true_iff, h_char_k])
          (by intro i hi; simp only [decide_eq_false_iff_not]; exact hpre i hi)
        rw [h_find]
        dsimp only []
        have : from_k + (k - from_k) = k := by omega
        rw [this]
      refine ret_uncompressed_scalar_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm1 ymm2
        h_distinct hlab H s _ chars ch fromIndex (BitVec.ofNat 32 k) hspec hm ?_ hz ?_
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h_mask : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h_mask, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with h | h | h | h | h
          · exact hr_out.1 h
          · exact hr_out.2.1 h
          · exact hr_out.2.2.1 h
          · exact hr_out.2.2.2.1 h
          · exact hr_out.2.2.2.2 h)
      · simp only [get64_set64, hd_offset_mask, ↓reduceIte, h_off]
        apply BitVec.eq_of_toNat_eq
        simp
    · have hzf : (BitVec.setWidth 32 (t.regs.get64 search_value) -
          ((d.getD (2 * k) 0).toBitVec.zeroExtend 16 ||| ((d.getD (2 * k + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 == 0#32) = false := by
        rw [h_search32, sub_beq_zero, beq_eq_false_iff_ne]
        intro h
        apply heq
        rw [h_chars k (by omega)]
        exact h.symm
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 109) (by rw [h_prog_len]; omega) ?_
      -- Directive 109: addq $1, temp_offset
      sstep
      refine Program.loopCont_of_le (j := 110) (by rw [h_prog_len]; omega) ?_
      -- Directive 110: subl $1, %ecx
      sstep
      refine Program.loopCont_of_le (j := 111) (by rw [h_prog_len]; omega) ?_
      -- Directive 111: jnz uncompressed_scalar_loop
      sstep
      have hzf_sub : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) - 1#32 == 0#32) = false := by
        rw [h_rcx]
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [hd_rcx_offset, hd_rcx_mask, hzf_sub, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 105) rfl]
      refine Program.loopCont_of_le (j := 105) (by rw [h_prog_len]; omega) ?_
      have hpre_step : ∀ (i : Nat) (hi : i < k + 1 - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        by_cases hi_lt : i < k - from_k
        · exact hpre i hi_lt
        · have hi_eq : i = k - from_k := by omega
          subst hi_eq
          have : (chars.drop from_k).get ⟨k - from_k, by rw [List.length_drop, h_len]; omega⟩ =
              chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ := List.getElem_drop
          rw [this]
          have h_fin : (⟨from_k + (k - from_k), by rw [h_len]; omega⟩ : Fin chars.length) = ⟨k, by rw [h_len]; omega⟩ := by
            ext; exact Nat.add_sub_of_le h_from_k
          have : chars.get ⟨from_k + (k - from_k), by rw [h_len]; omega⟩ = chars.get ⟨k, by rw [h_len]; omega⟩ := by
            congr 1
          rw [this]
          exact heq
      refine ih (k + 1) _ hm ?_ hz ?_ ?_ ?_ (by omega) (by omega) hpre_step
      · intro r hr_out
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
        have h1 : r ≠ out := hr_out.1
        have h2 : r ≠ Reg64.rcx := hr_out.2.1
        have h3 : r ≠ temp_len := hr_out.2.2.1
        have h4 : r ≠ temp_offset := hr_out.2.2.2.1
        have h5 : r ≠ temp_mask := hr_out.2.2.2.2
        simp only [get64_set64, h2, h4, h5, ↓reduceIte]
        exact hr r (by
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
          · exact h3 rfl
          · exact h4 rfl
          · exact h5 rfl)
      · rw [get_low32]
        simp only [get64_set64, hd_search_rcx, hd_search_offset, hd_search_mask, ↓reduceIte]
        exact h_search32
      · simp only [get64_set64, Ne.symm hd_rcx_offset, hd_offset_mask, ↓reduceIte, h_off]
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 by rfl, ofNat_add_lit]
      · simp only [get64_set64, sw32_64, ↓reduceIte, h_rcx]
        rw [ofNat_succ_sub_one (m + 1)]



theorem toNat_and_of_setWidth {x : BitVec 8} {y : BitVec 32} {m : Nat} (hm : m < 256)
    (h : (x &&& BitVec.ofNat 8 m).setWidth 32 = y) : x.toNat &&& m = y.toNat := by
  rw [← h, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := (x &&& BitVec.ofNat 8 m).isLt; omega), BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

theorem shr_count_ne_zero_32 (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 32#32) :
    (BitVec.setWidth 8 (32#32 - r) &&& 31#8 == 0#8) = false := by
  bv_decide

theorem shr_count_ne_zero_32_nat (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 32#32) :
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -r))).toNat &&& 31 == 0) = false := by
  have h1 : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -r)) = BitVec.setWidth 8 (32#32 - r) := by
    bv_decide
  rw [h1]
  let y : BitVec 32 := (BitVec.setWidth 8 (32#32 - r) &&& 31#8).zeroExtend 32
  have hy : (BitVec.setWidth 8 (32#32 - r) &&& BitVec.ofNat 8 31).setWidth 32 = y := by
    bv_decide
  have h_toNat := toNat_and_of_setWidth (x := BitVec.setWidth 8 (32#32 - r)) (y := y) (m := 31) (by decide) hy
  rw [h_toNat]
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hy0 : y = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simpa using h
  have hy_ne : y ≠ 0#32 := by
    dsimp [y]
    apply beq_eq_false_iff_ne.mp
    have : ((BitVec.setWidth 8 (32#32 - r) &&& 31#8).zeroExtend 32 == 0#32) =
        (BitVec.setWidth 8 (32#32 - r) &&& 31#8 == 0#8) := by
      bv_decide
    rw [this]
    apply shr_count_ne_zero_32 (hr0 := hr0) (hr_lt := hr_lt)
  exact hy_ne hy0

theorem shr_count_ne_zero_uncompressed (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 16#32) :
    (BitVec.setWidth 8 (32#32 - (r <<< 1)) &&& 31#8 == 0#8) = false := by
  bv_decide

theorem shr_count_ne_zero_uncompressed_nat (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 16#32) :
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(r <<< 1)))).toNat &&& 31 == 0) = false := by
  have h1 : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(r <<< 1))) = BitVec.setWidth 8 (32#32 - (r <<< 1)) := by
    bv_decide
  rw [h1]
  let y : BitVec 32 := (BitVec.setWidth 8 (32#32 - (r <<< 1)) &&& 31#8).zeroExtend 32
  have hy : (BitVec.setWidth 8 (32#32 - (r <<< 1)) &&& BitVec.ofNat 8 31).setWidth 32 = y := by
    bv_decide
  have h_toNat := toNat_and_of_setWidth (x := BitVec.setWidth 8 (32#32 - (r <<< 1))) (y := y) (m := 31) (by decide) hy
  rw [h_toNat]
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hy0 : y = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simpa using h
  have hy_ne : y ≠ 0#32 := by
    dsimp [y]
    apply beq_eq_false_iff_ne.mp
    have : ((BitVec.setWidth 8 (32#32 - (r <<< 1)) &&& 31#8).zeroExtend 32 == 0#32) =
        (BitVec.setWidth 8 (32#32 - (r <<< 1)) &&& 31#8 == 0#8) := by
      bv_decide
    rw [this]
    apply shr_count_ne_zero_uncompressed (hr0 := hr0) (hr_lt := hr_lt)
  exact hy_ne hy0

theorem test_and_lt (n : Nat) : n &&& 31 < 32 := by
  have : n &&& 31 ≤ 31 := by
    rw [Nat.and_comm]
    exact @Nat.and_le_left 31 n
  omega

theorem pmovmskb_pcmpeqb_zero (ch : BitVec 8) (mem : BitVec 256) :
    BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 ch) mem) = 0#32 ↔
      (mem.lane 8 0 ≠ ch ∧ mem.lane 8 1 ≠ ch ∧ mem.lane 8 2 ≠ ch ∧ mem.lane 8 3 ≠ ch ∧
       mem.lane 8 4 ≠ ch ∧ mem.lane 8 5 ≠ ch ∧ mem.lane 8 6 ≠ ch ∧ mem.lane 8 7 ≠ ch ∧
       mem.lane 8 8 ≠ ch ∧ mem.lane 8 9 ≠ ch ∧ mem.lane 8 10 ≠ ch ∧ mem.lane 8 11 ≠ ch ∧
       mem.lane 8 12 ≠ ch ∧ mem.lane 8 13 ≠ ch ∧ mem.lane 8 14 ≠ ch ∧ mem.lane 8 15 ≠ ch ∧
       mem.lane 8 16 ≠ ch ∧ mem.lane 8 17 ≠ ch ∧ mem.lane 8 18 ≠ ch ∧ mem.lane 8 19 ≠ ch ∧
       mem.lane 8 20 ≠ ch ∧ mem.lane 8 21 ≠ ch ∧ mem.lane 8 22 ≠ ch ∧ mem.lane 8 23 ≠ ch ∧
       mem.lane 8 24 ≠ ch ∧ mem.lane 8 25 ≠ ch ∧ mem.lane 8 26 ≠ ch ∧ mem.lane 8 27 ≠ ch ∧
       mem.lane 8 28 ≠ ch ∧ mem.lane 8 29 ≠ ch ∧ mem.lane 8 30 ≠ ch ∧ mem.lane 8 31 ≠ ch) := by
  simp only [BitVec.pmovmskb, BitVec.pcmpeqb, BitVec.broadcastb, BitVec.ofLanes, BitVec.lane,
    List.range, List.range.loop, List.foldl, Nat.reduceDiv, beq_iff_eq]
  bv_decide

theorem pmovmskb_pcmpeqw_zero (ch : BitVec 16) (mem : BitVec 256) :
    BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 ch) mem) = 0#32 ↔
      (mem.lane 16 0 ≠ ch ∧ mem.lane 16 1 ≠ ch ∧ mem.lane 16 2 ≠ ch ∧ mem.lane 16 3 ≠ ch ∧
       mem.lane 16 4 ≠ ch ∧ mem.lane 16 5 ≠ ch ∧ mem.lane 16 6 ≠ ch ∧ mem.lane 16 7 ≠ ch ∧
       mem.lane 16 8 ≠ ch ∧ mem.lane 16 9 ≠ ch ∧ mem.lane 16 10 ≠ ch ∧ mem.lane 16 11 ≠ ch ∧
       mem.lane 16 12 ≠ ch ∧ mem.lane 16 13 ≠ ch ∧ mem.lane 16 14 ≠ ch ∧ mem.lane 16 15 ≠ ch) := by
  simp only [BitVec.pmovmskb, BitVec.pcmpeqw, BitVec.broadcastw, BitVec.ofLanes, BitVec.lane,
    List.range, List.range.loop, List.foldl, Nat.reduceDiv, beq_iff_eq]
  bv_decide



theorem indexOfSpec_tail_not_found {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (from_k T r_left : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (h_len : chars.length = T)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (hr0 : r_left = 0) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  dsimp only [indexOfSpec]
  rw [h_from_eq]
  have h_none : ∀ (i : Nat) (hi : i < (chars.drop from_k).length),
      decide (((chars.drop from_k).get ⟨i, hi⟩).zeroExtend 32 = ch) = false := by
    intro i hi
    rw [List.length_drop, h_len] at hi
    simp only [decide_eq_false_iff_not]
    have : i < T - r_left - from_k := by omega
    exact hpre i this
  rw [findIdx?_eq_none _ _ h_none]

theorem indexOfSpec_tail_match {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (from_k T r_left b : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (h_len : chars.length = T)
    (hr_T : r_left ≤ T)
    (h_from_k : from_k ≤ T - r_left)
    (hb : b < r_left)
    (h_match : ((chars.drop from_k).get ⟨(T - r_left + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (hpre_tail : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch) :
    indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (T - r_left + b) := by
  dsimp only [indexOfSpec]
  rw [h_from_eq]
  have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
    (chars.drop from_k) ((T - r_left + b) - from_k) (by rw [List.length_drop, h_len]; omega)
    (by simp only [decide_eq_true_iff, h_match])
    (by
      intro i hi
      simp only [decide_eq_false_iff_not]
      by_cases hi_pre : i < T - r_left - from_k
      · exact hpre i hi_pre
      · have hm : i - (T - r_left - from_k) < b := by omega
        have := hpre_tail (i - (T - r_left - from_k)) hm
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨T - r_left + (i - (T - r_left - from_k)) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext
          dsimp only []
          omega
        rw [hext]
        exact this)
  rw [h_find]
  dsimp only []
  congr 1
  omega

theorem indexOfSpec_tail_none {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (from_k T r_left : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (h_len : chars.length = T)
    (hr_T : r_left ≤ T)
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (hpre_tail : ∀ (i : Nat) (hi : i < r_left),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  dsimp only [indexOfSpec]
  rw [h_from_eq]
  have h_find := findIdx?_eq_none (fun c => decide (c.zeroExtend 32 = ch))
    (chars.drop from_k) (by
      intro i hi
      simp only [decide_eq_false_iff_not]
      by_cases hi_pre : i < T - r_left - from_k
      · exact hpre i hi_pre
      · have hm : i - (T - r_left - from_k) < r_left := by
          rw [List.length_drop, h_len] at hi; omega
        have := hpre_tail (i - (T - r_left - from_k)) hm
        have hext : (⟨i, hi⟩ : Fin (chars.drop from_k).length) =
            ⟨T - r_left + (i - (T - r_left - from_k)) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext; dsimp only []; omega
        rw [hext]
        exact this)
  rw [h_find]

theorem indexOfSpec_avx_match {chars : List (BitVec 16)} {ch fromIndex : BitVec 32}
    (from_k T k b : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (h_len : chars.length = T)
    (hk_T : k + b < T)
    (h_from_k : from_k ≤ k)
    (h_match : ((chars.drop from_k).get ⟨(k + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch)
    (hpre : ∀ (i : Nat) (hi : i < k - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (hpre_chunk : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch) :
    indexOfSpec chars ch fromIndex = BitVec.ofNat 32 (k + b) := by
  dsimp only [indexOfSpec]
  rw [h_from_eq]
  have h_find := findIdx?_eq_some (fun c => decide (c.zeroExtend 32 = ch))
    (chars.drop from_k) ((k + b) - from_k) (by rw [List.length_drop, h_len]; omega)
    (by simp only [decide_eq_true_iff, h_match])
    (by
      intro i hi
      simp only [decide_eq_false_iff_not]
      by_cases hi_pre : i < k - from_k
      · exact hpre i hi_pre
      · have hm : i - (k - from_k) < b := by omega
        have := hpre_chunk (i - (k - from_k)) hm
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨k + (i - (k - from_k)) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext
          dsimp only []
          omega
        rw [hext]
        exact this)
  rw [h_find]
  dsimp only []
  congr 1
  omega

theorem findSome?_range_spec {α : Type} (f : Nat → Option α) (w : Nat) (v : α) :
    (List.range w).findSome? f = some v →
    ∃ i < w, f i = some v ∧ ∀ j < i, f j = none := by
  intro h
  induction w with
  | zero =>
    simp at h
  | succ w ih =>
    rw [List.range_succ, List.findSome?_append] at h
    cases h1 : (List.range w).findSome? f with
    | some v1 =>
      rw [h1] at h
      injection h with hv; subst hv
      obtain ⟨i, hi, hfi, hfj⟩ := ih h1
      exact ⟨i, by omega, hfi, hfj⟩
    | none =>
      rw [h1] at h
      dsimp [List.findSome?] at h
      cases h2 : f w with
      | none =>
        rw [h2] at h; simp at h
      | some v2 =>
        rw [h2] at h
        injection h with hv; subst hv
        refine ⟨w, by omega, h2, ?_⟩
        intro j hj
        have : (List.range w).findSome? f = none := h1
        have hj_in : j ∈ List.range w := by simp; omega
        have h_none := List.findSome?_eq_none_iff.mp this j hj_in
        exact h_none

theorem bsf_spec {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
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
        have hi_in : i ∈ List.range w := by simp; omega
        have := List.findSome?_eq_none_iff.mp h i hi_in
        cases h_lsb : x.getLsbD i
        · rfl
        · simp [h_lsb] at this
      have hx0 : x = 0#w := by
        ext i hi
        change x.getLsbD i = (0#w).getLsbD i
        rw [h_all i hi]
        simp
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

theorem bsf_toNat {w : Nat} (x : BitVec w) (hw2 : w < 2 ^ w) (hx : x ≠ 0#w) :
    ∃ i < w, (BitVec.bsf x).toNat = i ∧
             x.getLsbD i = true ∧
             ∀ j < i, x.getLsbD j = false := by
  obtain ⟨i, hi, h_bsf, h_true, h_false⟩ := bsf_spec x hx
  rw [h_bsf]
  have : (BitVec.ofNat w i).toNat = i := by
    simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    omega
  refine ⟨i, hi, this, h_true, h_false⟩

theorem shr_zero_bit (m : BitVec 32) (cnt i : Nat) (hz : m >>> cnt = 0#32) :
    m.getLsbD (cnt + i) = false := by
  have : (m >>> cnt).getLsbD i = false := by
    rw [hz]
    simp
  rw [← BitVec.getLsbD_ushiftRight]
  exact this

theorem sw_ofNat_add_bsf (k : Nat) (m : BitVec 32) (b : Nat) (hb : (BitVec.bsf m).toNat = b) :
    BitVec.setWidth 32 (BitVec.ofNat 64 k + (BitVec.bsf m).zeroExtend 64) = BitVec.ofNat 32 (k + b) := by
  apply BitVec.eq_of_toNat_eq
  have h_ze : (BitVec.bsf m).zeroExtend 64 = BitVec.setWidth 64 (BitVec.bsf m) := rfl
  rw [h_ze]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [hb]
  omega

theorem toBytes_succ (n : Nat) (v : Int) :
    Int.toBytes (n + 1) v = ((v.take 8).toNat.toUInt8) :: Int.toBytes n (v / 256) := rfl

theorem toBytes_get_zero (n : Nat) (v : Int) :
    (Int.toBytes (n + 1) v).get ⟨0, by rw [Int.toBytes_length]; omega⟩ =
      ((v.take 8).toNat.toUInt8) := rfl

theorem toBytes_get_succ (n : Nat) (v : Int) (i : Nat) (hi : i < n) :
    (Int.toBytes (n + 1) v).get ⟨i + 1, by rw [Int.toBytes_length]; omega⟩ =
      (Int.toBytes n (v / 256)).get ⟨i, by rw [Int.toBytes_length]; omega⟩ := by
  rfl

theorem toBytes_getElem_formula (n : Nat) (v : Int) (i : Nat) (hi : i < n) :
    ((Int.toBytes n v).get ⟨i, by rw [Int.toBytes_length]; omega⟩).toBitVec =
      BitVec.ofInt 8 (v / (256 : Int) ^ i) := by
  induction i generalizing n v with
  | zero =>
    cases n with
    | zero => contradiction
    | succ n =>
      simp only [toBytes_get_zero, Int.pow_zero, Int.ediv_one]
      apply BitVec.eq_of_toNat_eq
      dsimp [UInt8.toNat, UInt8.toBitVec, Int.take]
      simp only [BitVec.toNat_ofInt]
      have : ((2 : Nat) ^ 8 : Int) = 256 := by decide
      change (v % 256).toNat % 256 = (v % ((2 : Nat) ^ 8 : Int)).toNat
      rw [this]
      have h_mod : (v % 256).toNat % 256 = (v % 256).toNat := by
        apply Nat.mod_eq_of_lt
        omega
      rw [h_mod]
  | succ i ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      have hi' : i < n := by omega
      rw [toBytes_get_succ (hi := hi')]
      have h_rec := ih n (v / 256) hi'
      rw [h_rec]
      congr 1
      rw [Int.pow_succ]
      have h_ediv := @Int.ediv_ediv v 256 (256 ^ i)
      simp only [show ¬ (256 : Int) < 0 by decide, false_and, ↓reduceIte, Int.sub_zero] at h_ediv
      rw [h_ediv, Int.mul_comm]

theorem toBytes_getElem (bs : List UInt8) (n : Nat) (h_len : bs.length = n) (i : Nat) (hi : i < n) :
    bs.get ⟨i, by omega⟩ = (Int.toBytes n (Int.ofBytes bs)).get ⟨i, by rw [Int.toBytes_length]; omega⟩ := by
  have h : bs = Int.toBytes n (Int.ofBytes bs) := by
    have h_tob := (Int.toBytes_ofBytes n bs (by omega)).symm
    rw [List.take_of_length_le (by omega)] at h_tob
    exact h_tob
  have h_get := congrArg (fun l => l[i]?) h
  have h1 : bs[i]? = some (bs.get ⟨i, by omega⟩) := List.getElem?_eq_getElem (by omega)
  have h2 : (Int.toBytes n (Int.ofBytes bs))[i]? =
      some ((Int.toBytes n (Int.ofBytes bs)).get ⟨i, by rw [Int.toBytes_length]; omega⟩) :=
    List.getElem?_eq_getElem (by rw [Int.toBytes_length]; omega)
  rw [h1, h2] at h_get
  exact Option.some.inj h_get

theorem test_mod (x : Int) (hx : 0 ≤ x) :
    x.toNat % 256 = (x % 256).toNat := by
  have : (256 : Int) = (256 : Nat) := rfl
  rw [this]
  rw [Int.toNat_emod hx (by decide)]
  rfl

theorem ofBytes_pow_pos (i : Nat) : 0 ≤ (256 : Int) ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Int.pow_succ]
    exact Int.mul_nonneg ih (by decide)

theorem ofBytes_lane8 (bs : List UInt8) (n : Nat) (h_len : bs.length = n) (i : Nat) (hi : i < n) :
    (BitVec.ofInt (8 * n) (Int.ofBytes bs)).lane 8 i = (bs.get ⟨i, by omega⟩).toBitVec := by
  rw [toBytes_getElem bs n h_len i hi]
  rw [toBytes_getElem_formula n (Int.ofBytes bs) i hi]
  dsimp [BitVec.lane, BitVec.extractLsb']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have h_pow : ((2 ^ (8 * n) : Nat) : Int) = (256 : Int) ^ n := by
    rw [show (256 : Int) = (2 : Int) ^ 8 by decide, ← Int.pow_mul]
    exact (Int.natCast_pow 2 (8 * n)).symm
  have h_lt : Int.ofBytes bs < ((2 ^ (8 * n) : Nat) : Int) := by
    rw [h_pow, ← h_len]
    exact Int.ofBytes_lt bs
  have h_ge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have h_mod : Int.ofBytes bs % ((2 ^ (8 * n) : Nat) : Int) = Int.ofBytes bs := Int.emod_eq_of_lt h_ge h_lt
  rw [h_mod]
  have h_pow8 : 2 ^ (8 * i) = (256 : Nat) ^ i := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [Nat.shiftRight_eq_div_pow, h_pow8]
  have h_ediv_ge : 0 ≤ Int.ofBytes bs / (256 : Int) ^ i :=
    Int.ediv_nonneg h_ge (ofBytes_pow_pos i)
  have h_toNat : (Int.ofBytes bs).toNat / 256 ^ i = (Int.ofBytes bs / (256 : Int) ^ i).toNat := by
    obtain ⟨m, hm⟩ : ∃ m : Nat, Int.ofBytes bs = (m : Int) := ⟨(Int.ofBytes bs).toNat, (Int.toNat_of_nonneg h_ge).symm⟩
    rw [hm]
    rw [show (256 : Int) ^ i = ((256 ^ i : Nat) : Int) from (Int.natCast_pow 256 i).symm]
    rw [← Int.natCast_ediv]
    rw [Int.toNat_natCast, Int.toNat_natCast]
  rw [h_toNat]
  exact test_mod (Int.ofBytes bs / (256 : Int) ^ i) h_ediv_ge

macro "bv_bit" : tactic => `(tactic| (
  simp only [BitVec.pmovmskb, BitVec.pcmpeqb, BitVec.broadcastb, BitVec.ofLanes, BitVec.lane,
    List.range, List.range.loop, List.foldl, Nat.reduceDiv, beq_iff_eq]
  bv_decide))

theorem pcmpeqb_pmovmskb_bit (ch : BitVec 8) (mem : BitVec 256) (j : Nat) (hj : j < 32) :
    (BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 ch) mem)).getLsbD j = (mem.lane 8 j == ch) := by
  revert hj
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  cases j with | zero => intro _; bv_bit | succ j => ?_
  intro hj; omega

theorem ch_eq_bv (ch : BitVec 32) (h : ch < 128#32) : ch = (ch.setWidth 8).zeroExtend 32 := by
  bv_decide

theorem byteAt_zero_ext_eq (b : UInt8) (ch : BitVec 32) (h_ch : ch.toNat ≤ 127) :
    (b.toBitVec.zeroExtend 32 = ch) ↔ (b.toBitVec = BitVec.setWidth 8 ch) := by
  have h_lt : ch < 128#32 := by
    change ch.toNat < (128#32).toNat
    simp only [BitVec.toNat_ofNat]
    omega
  have hch : ch = (BitVec.setWidth 8 ch).zeroExtend 32 := ch_eq_bv ch h_lt
  constructor
  · intro h
    rw [hch] at h
    have h1 := congrArg (BitVec.extractLsb' 0 8) h
    revert h1
    bv_decide
  · intro h
    rw [h, ← hch]

theorem compressed_avx_pre_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (from_k : Nat)
    (t' : MachineData) (ymm_target : AvxReg .W256)
    (h_target : t'.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
    (k : Nat) (hk32 : k + 32 ≤ T) (hfrom : from_k ≤ k)
    (h_zero : (BitVec.pmovmskb (BitVec.pcmpeqb (t'.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))))) == 0#32) :
    ∀ (i : Nat) (hi : i < 32), ((chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
  intro i hi h_eq
  have h_drop_get : (chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
      chars.get ⟨k + i, by omega⟩ := by
    have h_len' : (k + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
    have h1 : (chars.drop from_k).get ⟨(k + i) - from_k, h_len'⟩ = (chars.drop from_k)[(k + i) - from_k] := List.get_eq_getElem
    rw [h1]
    rw [List.getElem_drop]
    have h2 : chars.get ⟨k + i, by omega⟩ = chars[k + i] := List.get_eq_getElem
    rw [h2]
    congr 1
    omega
  rw [h_drop_get] at h_eq
  have h_char_val := h_chars (k + i) (by omega)
  rw [h_char_val] at h_eq
  have h_data_val := h_data (k + i) (by omega)
  rw [← h_data_val] at h_eq
  have h_byte_eq := (byteAt_zero_ext_eq (byteAt s.dmem A (k + i)) ch h_ch).mp h_eq
  let bs := List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : bs.get ⟨i, by omega⟩ = byteAt s.dmem A (k + i) := by
    dsimp [bs]
    simp
  have h_lane := ofBytes_lane8 bs 32 h_bs_len i hi
  rw [h_bs_get] at h_lane
  have h_bit := pcmpeqb_pmovmskb_bit (BitVec.setWidth 8 ch) (BitVec.ofInt 256 (Int.ofBytes bs)) i hi
  rw [h_lane] at h_bit
  have h_beq : ((byteAt s.dmem A (k + i)).toBitVec == BitVec.setWidth 8 ch) = true := by
    simp [h_byte_eq]
  rw [h_beq] at h_bit
  have h_mask_bit : (BitVec.pmovmskb (BitVec.pcmpeqb (t'.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes bs)))).getLsbD i = true := by
    rw [h_target]
    exact h_bit
  have h_zero_bit : (BitVec.pmovmskb (BitVec.pcmpeqb (t'.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes bs)))).getLsbD i = false := by
    have h_mask_eq : (BitVec.pmovmskb (BitVec.pcmpeqb (t'.zmms.get ymm_target)
        (BitVec.ofInt 256 (Int.ofBytes bs)))) = 0#32 := by
      exact beq_iff_eq.mp h_zero
    rw [h_mask_eq]
    simp
  rw [h_zero_bit] at h_mask_bit
  contradiction

theorem compressed_avx_match_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (k : Nat) (hk32 : k + 32 ≤ T) (hfrom : from_k ≤ k)
    (hpre : ∀ (i : Nat) (hi : i < k - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (mask : BitVec 32)
    (h_mask : mask = (BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))))))
    (h_ne : mask ≠ 0#32) :
    indexOfSpec chars ch fromIndex = BitVec.setWidth 32 (.ofNat 64 k + (BitVec.bsf mask).zeroExtend 64) := by
  obtain ⟨b, hb_lt, hb_bsf, hb_true, hb_false⟩ := bsf_toNat mask (by decide) h_ne
  let bs := List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : ∀ i (hi : i < 32), bs.get ⟨i, by omega⟩ = byteAt s.dmem A (k + i) := by
    intro i hi; dsimp [bs]; simp
  have h_bit : ∀ i (hi : i < 32), mask.getLsbD i = ((byteAt s.dmem A (k + i)).toBitVec == BitVec.setWidth 8 ch) := by
    intro i hi
    rw [h_mask]
    have h_p := pcmpeqb_pmovmskb_bit (BitVec.setWidth 8 ch) (BitVec.ofInt 256 (Int.ofBytes bs)) i hi
    have h_l := ofBytes_lane8 bs 32 h_bs_len i hi
    rw [h_bs_get i hi] at h_l
    rw [h_l] at h_p
    exact h_p
  have h_match : ((chars.drop from_k).get ⟨(k + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
    have h_drop_get : (chars.drop from_k).get ⟨(k + b) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨k + b, by omega⟩ := by
      have h_len' : (k + b) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(k + b) - from_k, h_len'⟩ = (chars.drop from_k)[(k + b) - from_k] := List.get_eq_getElem
      rw [h1]
      rw [List.getElem_drop]
      have h2 : chars.get ⟨k + b, by omega⟩ = chars[k + b] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get]
    have h_char_val := h_chars (k + b) (by omega)
    rw [h_char_val]
    have h_data_val := h_data (k + b) (by omega)
    rw [← h_data_val]
    have hb_bit := h_bit b hb_lt
    rw [hb_true] at hb_bit
    have h_beq : (byteAt s.dmem A (k + b)).toBitVec = BitVec.setWidth 8 ch := by
      have := hb_bit.symm
      simpa using this
    exact (byteAt_zero_ext_eq (byteAt s.dmem A (k + b)) ch h_ch).mpr h_beq
  have hpre_chunk : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨k + i, by omega⟩ := by
      have h_len' : (k + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(k + i) - from_k, h_len'⟩ = (chars.drop from_k)[(k + i) - from_k] := List.get_eq_getElem
      rw [h1]
      rw [List.getElem_drop]
      have h2 : chars.get ⟨k + i, by omega⟩ = chars[k + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_char_val := h_chars (k + i) (by omega)
    rw [h_char_val] at h_eq
    have h_data_val := h_data (k + i) (by omega)
    rw [← h_data_val] at h_eq
    have h_byte_eq := (byteAt_zero_ext_eq (byteAt s.dmem A (k + i)) ch h_ch).mp h_eq
    have hi_bit := h_bit i (by omega)
    have hi_false := hb_false i hi
    rw [hi_false] at hi_bit
    have h_beq : ((byteAt s.dmem A (k + i)).toBitVec == BitVec.setWidth 8 ch) = true := by
      simp [h_byte_eq]
    rw [h_beq] at hi_bit
    contradiction
  have h_spec := indexOfSpec_avx_match from_k T k b h_from_eq h_len (by omega) hfrom h_match hpre hpre_chunk
  rw [h_spec]
  exact (sw_ofNat_add_bsf k mask b hb_bsf).symm


@[expose] public def compressed_tail_mask (t s : MachineData) (A : BitVec 64) (ymm_target : AvxReg .W256) (T : Nat) : BitVec 32 :=
  (BitVec.pcmpeqb (t.zmms.get ymm_target)
    (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31)

theorem ushiftRight_getLsbD {w : Nat} (x : BitVec w) (n i : Nat) :
    (x.ushiftRight n).getLsbD i = x.getLsbD (n + i) := by
  change (x >>> n).getLsbD i = _
  rw [BitVec.getLsbD_ushiftRight]

theorem getLsbD_ge {w : Nat} (x : BitVec w) (i : Nat) (h : w ≤ i) : x.getLsbD i = false := by
  dsimp [BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  have h1 : x.toNat < 2 ^ w := x.isLt
  have h2 : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
  omega

theorem tail_shift_bv (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 32#32) :
    BitVec.setWidth 8 (32#32 - r) &&& 31#8 = BitVec.setWidth 8 (32#32 - r) := by
  bv_decide

theorem tail_shift_cnt (r : BitVec 32) (hr0 : r ≠ 0#32) (hr_lt : r < 32#32) :
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -r))).toNat &&& 31) =
      (BitVec.setWidth 8 (32#32 - r)).toNat := by
  have h1 : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -r)) = BitVec.setWidth 8 (32#32 - r) := by
    bv_decide
  rw [h1]
  have h31 : (31 : Nat) = (31#8).toNat := rfl
  rw [h31, ← BitVec.toNat_and, tail_shift_bv r hr0 hr_lt]

theorem ofNat8_sub (r_left : Nat) (hr32 : r_left ≤ 32) :
    (32#8 : BitVec 8) - BitVec.ofNat 8 r_left = BitVec.ofNat 8 (32 - r_left) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : r_left % 256 = r_left := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : 256 - r_left + 32 = 256 + (32 - r_left) := by omega
  rw [h2]
  rw [Nat.add_mod_left]

theorem tail_shift_cnt_nat (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 32) :
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -BitVec.ofNat 32 r_left))).toNat &&& 31) = 32 - r_left := by
  have hr0_bv : BitVec.ofNat 32 r_left ≠ 0#32 := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hr_lt_bv : BitVec.ofNat 32 r_left < 32#32 := by
    change (BitVec.ofNat 32 r_left).toNat < (32#32 : BitVec 32).toNat
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [tail_shift_cnt (BitVec.ofNat 32 r_left) hr0_bv hr_lt_bv]
  have : BitVec.setWidth 8 (32#32 - BitVec.ofNat 32 r_left) = 32#8 - BitVec.setWidth 8 (BitVec.ofNat 32 r_left) := by
    bv_decide
  rw [this]
  have h_w8 : BitVec.setWidth 8 (BitVec.ofNat 32 r_left) = BitVec.ofNat 8 r_left := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : 2 ^ 8 = 256 := rfl
    have h1 : r_left % 2 ^ 32 = r_left := Nat.mod_eq_of_lt (by omega)
    have h2 : r_left % 256 = r_left := Nat.mod_eq_of_lt (by omega)
    rw [this, h1, h2]
  rw [h_w8]
  rw [ofNat8_sub r_left (by omega)]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem compressed_tail_none_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData) (ymm_target : AvxReg .W256)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
    (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 32) (hr_T : r_left ≤ T) (hT32 : 32 ≤ T)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_zero : compressed_tail_mask t s A ymm_target T == 0#32) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  have hpre_tail : ∀ (i : Nat) (hi : i < r_left),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + i, by omega⟩ := by
      have h_len' : (T - r_left + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + i) - from_k] := List.get_eq_getElem
      rw [h1]
      rw [List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + i, by omega⟩ = chars[T - r_left + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_char_val := h_chars (T - r_left + i) (by omega)
    rw [h_char_val] at h_eq
    have h_data_val := h_data (T - r_left + i) (by omega)
    rw [← h_data_val] at h_eq
    have h_byte_eq := (byteAt_zero_ext_eq (byteAt s.dmem A (T - r_left + i)) ch h_ch).mp h_eq
    let bs := List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)
    have h_bs_len : bs.length = 32 := by simp [bs]
    have h_lt : (32 - r_left) + i < 32 := by omega
    have h_bs_get : bs.get ⟨(32 - r_left) + i, by simp [bs]; omega⟩ = byteAt s.dmem A (T - r_left + i) := by
      dsimp [bs]
      simp
      have : T - 32 + (32 - r_left + i) = T - r_left + i := by omega
      rw [this]
    have h_lane := ofBytes_lane8 bs 32 h_bs_len ((32 - r_left) + i) h_lt
    rw [h_bs_get] at h_lane
    have h_bit := pcmpeqb_pmovmskb_bit (BitVec.setWidth 8 ch) (BitVec.ofInt 256 (Int.ofBytes bs)) ((32 - r_left) + i) h_lt
    rw [h_lane] at h_bit
    have h_beq : ((byteAt s.dmem A (T - r_left + i)).toBitVec == BitVec.setWidth 8 ch) = true := by
      simp [h_byte_eq]
    rw [h_beq] at h_bit
    have h_mask_bit : (compressed_tail_mask t s A ymm_target T).getLsbD i = true := by
      unfold compressed_tail_mask
      rw [ushiftRight_getLsbD]
      rw [h_rcx]
      rw [tail_shift_cnt_nat r_left hr0 hr_left]
      rw [h_target]
      exact h_bit
    have h_zero_bit : (compressed_tail_mask t s A ymm_target T).getLsbD i = false := by
      have h_eq0 : compressed_tail_mask t s A ymm_target T = 0#32 := beq_iff_eq.mp h_zero
      rw [h_eq0]
      apply BitVec.getLsbD_zero
    rw [h_zero_bit] at h_mask_bit
    contradiction
  exact indexOfSpec_tail_none from_k T r_left h_from_eq h_len hr_T h_from_k hpre hpre_tail

theorem compressed_tail_match_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData) (ymm_target : AvxReg .W256)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
    (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 32) (hr_T : r_left ≤ T) (hT32 : 32 ≤ T)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (mask : BitVec 32)
    (h_mask : mask = compressed_tail_mask t s A ymm_target T)
    (h_ne : mask ≠ 0#32) :
    indexOfSpec chars ch fromIndex = BitVec.setWidth 32 (.ofNat 64 (T - r_left) + (BitVec.bsf mask).zeroExtend 64) := by
  obtain ⟨b, hb_lt, hb_bsf, hb_true, hb_false⟩ := bsf_toNat mask (by decide) h_ne
  let bs := List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : ∀ i (hi : i < 32), bs.get ⟨i, by simp [bs]; omega⟩ = byteAt s.dmem A (T - 32 + i) := by
    intro i hi
    dsimp [bs]
    simp
  have h_mask_bit_eq : ∀ i, mask.getLsbD i =
      (BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
        (BitVec.ofInt 256 (Int.ofBytes bs)))).getLsbD ((32 - r_left) + i) := by
    intro i
    rw [h_mask]
    unfold compressed_tail_mask
    rw [ushiftRight_getLsbD]
    rw [h_rcx, tail_shift_cnt_nat r_left hr0 hr_left, h_target]
  have hb_r_left : b < r_left := by
    by_cases hb : b < r_left
    · exact hb
    · have h_ge' : r_left ≤ b := by omega
      have h_out : 32 ≤ (32 - r_left) + b := by omega
      have h_bit_false : mask.getLsbD b = false := by
        rw [h_mask_bit_eq]
        exact getLsbD_ge _ _ h_out
      rw [hb_true] at h_bit_false
      contradiction
  have h_bit : ∀ i (hi : i < r_left), mask.getLsbD i = ((byteAt s.dmem A (T - r_left + i)).toBitVec == BitVec.setWidth 8 ch) := by
    intro i hi
    rw [h_mask_bit_eq]
    have h_lt : (32 - r_left) + i < 32 := by omega
    have h_p := pcmpeqb_pmovmskb_bit (BitVec.setWidth 8 ch) (BitVec.ofInt 256 (Int.ofBytes bs)) ((32 - r_left) + i) h_lt
    have h_l := ofBytes_lane8 bs 32 h_bs_len ((32 - r_left) + i) h_lt
    have h_bs_val := h_bs_get ((32 - r_left) + i) h_lt
    rw [h_bs_val] at h_l
    have h_idx : T - 32 + ((32 - r_left) + i) = T - r_left + i := by omega
    rw [h_idx] at h_l
    rw [h_l] at h_p
    exact h_p
  have h_match : ((chars.drop from_k).get ⟨(T - r_left + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + b) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + b, by omega⟩ := by
      have h_len' : (T - r_left + b) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + b) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + b) - from_k] := List.get_eq_getElem
      rw [h1]
      rw [List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + b, by omega⟩ = chars[T - r_left + b] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get]
    have h_char_val := h_chars (T - r_left + b) (by omega)
    rw [h_char_val]
    have h_data_val := h_data (T - r_left + b) (by omega)
    rw [← h_data_val]
    have hb_bit := h_bit b hb_r_left
    rw [hb_true] at hb_bit
    have h_beq : (byteAt s.dmem A (T - r_left + b)).toBitVec = BitVec.setWidth 8 ch := by
      have := hb_bit.symm
      simpa using this
    exact (byteAt_zero_ext_eq (byteAt s.dmem A (T - r_left + b)) ch h_ch).mpr h_beq
  have hpre_chunk : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + i, by omega⟩ := by
      have h_len' : (T - r_left + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + i) - from_k] := List.get_eq_getElem
      rw [h1]
      rw [List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + i, by omega⟩ = chars[T - r_left + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_char_val := h_chars (T - r_left + i) (by omega)
    rw [h_char_val] at h_eq
    have h_data_val := h_data (T - r_left + i) (by omega)
    rw [← h_data_val] at h_eq
    have h_byte_eq := (byteAt_zero_ext_eq (byteAt s.dmem A (T - r_left + i)) ch h_ch).mp h_eq
    have hi_bit := h_bit i (by omega)
    have hi_false := hb_false i hi
    rw [hi_false] at hi_bit
    have h_beq : ((byteAt s.dmem A (T - r_left + i)).toBitVec == BitVec.setWidth 8 ch) = true := by
      simp [h_byte_eq]
    rw [h_beq] at hi_bit
    contradiction
  have h_spec := indexOfSpec_avx_match from_k T (T - r_left) b h_from_eq h_len (by omega) h_from_k h_match hpre hpre_chunk
  rw [h_spec]
  exact (sw_ofNat_add_bsf (T - r_left) mask b hb_bsf).symm

theorem zmms_get_set_of_ne (z : RegZmms) (r1 r2 : RegMm) (v1 v2 : BitVec 256)
    (h : r1 ≠ r2) :
    ((z.set (.ymm r1) v1).set (.ymm r2) v2).get (.ymm r1) = v1 := by
  dsimp [RegZmms.get, RegZmms.set, AvxReg.base]
  have hdiff : ((z.set512 r1 (BitVec.setWidth 512 v1)).set512 r2 (BitVec.setWidth 512 v2)).get512 r1 =
      (z.set512 r1 (BitVec.setWidth 512 v1)).get512 r1 := by
    cases r1 <;> cases r2 <;> (try contradiction) <;> rfl
  rw [hdiff]
  have hsame : (z.set512 r1 (BitVec.setWidth 512 v1)).get512 r1 = BitVec.setWidth 512 v1 := by
    cases r1 <;> rfl
  rw [hsame]
  dsimp [BitVec.take]
  bv_decide

theorem zmms_get_target (z : RegZmms) (ymm_target ymm_match : AvxReg .W256) (v1 v2 : BitVec 256)
    (h : ymm_target ≠ ymm_match) :
    ((z.set ymm_target v1).set ymm_match v2).get ymm_target = v1 := by
  cases ymm_target with | ymm r1 =>
  cases ymm_match with | ymm r2 =>
  have h_ne : r1 ≠ r2 := by intro heq; subst heq; contradiction
  exact zmms_get_set_of_ne z r1 r2 v1 v2 h_ne

theorem zmms_set_comm (z : RegZmms) (r1 r2 : RegMm) (v1 v2 : BitVec 256)
    (h : r1 ≠ r2) :
    ((z.set (.ymm r1) v1).set (.ymm r2) v2) = ((z.set (.ymm r2) v2).set (.ymm r1) v1) := by
  dsimp [RegZmms.set, AvxReg.base]
  cases z
  cases r1 <;> cases r2 <;> (try contradiction) <;> rfl

theorem zmms_set_set_of_ne (z : RegZmms) (ymm1 ymm2 : AvxReg .W256) (v1 v2 : BitVec 256)
    (h : ymm1 ≠ ymm2) :
    ((z.set ymm1 v1).set ymm2 v2) = ((z.set ymm2 v2).set ymm1 v1) := by
  cases ymm1 with | ymm r1 =>
  cases ymm2 with | ymm r2 =>
  have h_ne : r1 ≠ r2 := by intro heq; subst heq; contradiction
  exact zmms_set_comm z r1 r2 v1 v2 h_ne

theorem compressed_tail_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT32 : 32 ≤ T)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm_target v1).set ymm_match v2)
    (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
    (r_left : Nat) (hr_left : r_left < 32)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_off : t.regs.get64 temp_offset = .ofNat 64 (T - r_left))
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 29)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  -- Directive 29: .label compressed_tail
  sstep
  refine Program.loopCont_of_le (j := 30) (by rw [h_prog_len]; omega) ?_
  -- Directive 30: testl %ecx, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 31) (by rw [h_prog_len]; omega) ?_
  -- Directive 31: je not_found_vzero
  sstep
  have h_and_self : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) &&& BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) =
      (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hr0 : r_left = 0
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = true := by
      rw [h_rcx, hr0]; rfl
    simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
    refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
    have hspec := indexOfSpec_tail_not_found from_k T r_left h_from_eq h_len hpre hr0
    exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ chars ch fromIndex hspec hm hr hz
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = false := by
      rw [h_rcx]
      have : (BitVec.ofNat 32 r_left == 0#32) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact hr0 this
      exact this
    simp only [hzf, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 32) (by rw [h_prog_len]; omega) ?_
    have haddr_tail : t.regs.get64 str + t.regs.get64 temp_len + -16#64 = A + .ofNat 64 (T - 32) + 16#64 := by
      rw [hstr, h_len_reg]
      have : (BitVec.ofNat 64 T : BitVec 64) = BitVec.ofNat 64 (T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    have hload : t.dmem.loadInt (t.regs.get64 str + t.regs.get64 temp_len + -16#64) 32 =
        some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (T - 32 + j))) := by
      rw [haddr_tail, hm]
      exact load_chunk s.dmem A (T - 32) 32 T h_some (by omega)
    sstep
    rw [hload]
    dsimp only []
    refine Program.loopCont_of_le (j := 33) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 34) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 35) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 36) (by rw [h_prog_len]; omega) ?_
    sstep
    have h_set_rcx : ∀ (regs : Reg64s) (v : BitVec 64), (regs.set64 Reg64.rcx v).rcx = UInt64.ofBitVec v := fun _ _ => rfl
    simp only [h_set_rcx, UInt64.toBitVec_ofBitVec]
    have h_rcx_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    have h_mask_ne : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
    simp only [h_rcx_ne, h_mask_ne, Bool.false_eq_true, ↓reduceIte]
    have h_rcx_w32 : BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) = BitVec.ofNat 32 r_left := h_rcx
    have h_cond : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 == 0) = false := by
      rw [h_rcx_w32]
      apply Proof.shr_count_ne_zero_32_nat (hr0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega) (hr_lt := by
        have : (BitVec.ofNat 32 r_left).toNat < (32#32 : BitVec 32).toNat := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        exact this)
    simp only [h_cond, Bool.false_eq_true, ↓reduceIte]
    have h_lt : (BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 < 32 := by
      exact Proof.test_and_lt _
    simp only [h_lt, ↓reduceIte]
    intro af
    let shifted_mask := (BitVec.pcmpeqb (t.zmms.get ymm_target)
        (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
        ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31)
    by_cases h_one : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 == 1) = true
    · simp only [h_one, ↓reduceIte]
      refine Program.loopCont_of_le (j := 37) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 38) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
        refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (compressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre (by exact hzf)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 39) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := BitVec.bsf shifted_mask
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_compressed_tail_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (compressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)
    · simp only [h_one, Bool.false_eq_true, ↓reduceIte]
      intro of
      refine Program.loopCont_of_le (j := 37) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 38) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
        refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (compressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre (by exact hzf)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 39) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := BitVec.bsf shifted_mask
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_compressed_tail_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (compressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)


theorem compressed_tail_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT32 : 32 ≤ T)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm_target v1).set ymm_match v2)
    (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
    (r_left : Nat) (hr_left : r_left < 32)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_off : t.regs.get64 temp_offset = .ofNat 64 (T - r_left))
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 33)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  -- Directive 29: .label compressed_tail
  sstep
  refine Program.loopCont_of_le (j := 34) (by rw [h_prog_len]; omega) ?_
  -- Directive 30: testl %ecx, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 35) (by rw [h_prog_len]; omega) ?_
  -- Directive 31: je not_found_vzero
  sstep
  have h_and_self : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) &&& BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) =
      (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hr0 : r_left = 0
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = true := by
      rw [h_rcx, hr0]; rfl
    simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
    refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
    have hspec := indexOfSpec_tail_not_found from_k T r_left h_from_eq h_len hpre hr0
    exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ chars ch fromIndex hspec hm hr hz
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = false := by
      rw [h_rcx]
      have : (BitVec.ofNat 32 r_left == 0#32) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact hr0 this
      exact this
    simp only [hzf, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 36) (by rw [h_prog_len]; omega) ?_
    have haddr_tail : t.regs.get64 str + t.regs.get64 temp_len + -16#64 = A + .ofNat 64 (T - 32) + 16#64 := by
      rw [hstr, h_len_reg]
      have : (BitVec.ofNat 64 T : BitVec 64) = BitVec.ofNat 64 (T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    have hload : t.dmem.loadInt (t.regs.get64 str + t.regs.get64 temp_len + -16#64) 32 =
        some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (T - 32 + j))) := by
      rw [haddr_tail, hm]
      exact load_chunk s.dmem A (T - 32) 32 T h_some (by omega)
    sstep
    rw [hload]
    dsimp only []
    refine Program.loopCont_of_le (j := 37) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 38) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 39) (by rw [h_prog_len]; omega) ?_
    sstep
    refine Program.loopCont_of_le (j := 40) (by rw [h_prog_len]; omega) ?_
    sstep
    have h_set_rcx : ∀ (regs : Reg64s) (v : BitVec 64), (regs.set64 Reg64.rcx v).rcx = UInt64.ofBitVec v := fun _ _ => rfl
    simp only [h_set_rcx, UInt64.toBitVec_ofBitVec]
    have h_rcx_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    have h_mask_ne : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
    simp only [h_rcx_ne, h_mask_ne, Bool.false_eq_true, ↓reduceIte]
    have h_rcx_w32 : BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) = BitVec.ofNat 32 r_left := h_rcx
    have h_cond : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 == 0) = false := by
      rw [h_rcx_w32]
      apply Proof.shr_count_ne_zero_32_nat (hr0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega) (hr_lt := by
        have : (BitVec.ofNat 32 r_left).toNat < (32#32 : BitVec 32).toNat := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        exact this)
    simp only [h_cond, Bool.false_eq_true, ↓reduceIte]
    have h_lt : (BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 < 32 := by
      exact Proof.test_and_lt _
    simp only [h_lt, ↓reduceIte]
    intro af
    let shifted_mask := (BitVec.pcmpeqb (t.zmms.get ymm_target)
        (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
        ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31)
    by_cases h_one : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -BitVec.setWidth 32 (t.regs.get64 Reg64.rcx)))).toNat &&& 31 == 1) = true
    · simp only [h_one, ↓reduceIte]
      refine Program.loopCont_of_le (j := 41) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 42) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
        refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (compressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre (by exact hzf)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 43) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := BitVec.bsf shifted_mask
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_compressed_tail_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (compressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)
    · simp only [h_one, Bool.false_eq_true, ↓reduceIte]
      intro of
      refine Program.loopCont_of_le (j := 41) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 42) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
        refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (compressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre (by exact hzf)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 43) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := BitVec.bsf shifted_mask
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_compressed_tail_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (compressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT32 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) hm (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)


macro "bv_bit_w" : tactic => `(tactic| (
  simp only [BitVec.pmovmskb, BitVec.pcmpeqw, BitVec.broadcastw, BitVec.ofLanes, BitVec.lane,
    List.range, List.range.loop, List.foldl, Nat.reduceDiv, beq_iff_eq]
  bv_decide))

theorem pcmpeqw_pmovmskb_bit (ch : BitVec 16) (mem : BitVec 256) (j : Nat) (hj : j < 32) :
    (BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 ch) mem)).getLsbD j = (mem.lane 16 (j / 2) == ch) := by
  revert hj
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  cases j with | zero => intro _; bv_bit_w | succ j => ?_
  intro hj; omega

theorem bsf_mask_word (ch : BitVec 16) (mem : BitVec 256)
    (mask : BitVec 32)
    (h_mask : mask = BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 ch) mem))
    (h_ne : mask ≠ 0#32) :
    ∃ b < 16,
      mem.lane 16 b = ch ∧
      (∀ i < b, mem.lane 16 i ≠ ch) ∧
      (BitVec.bsf mask).toNat = 2 * b ∧
      ((BitVec.bsf mask) >>> 1).toNat = b := by
  obtain ⟨j, hj_lt, hj_bsf, hj_true, hj_false⟩ := bsf_toNat mask (by decide) h_ne
  have h_bit : ∀ k < 32, mask.getLsbD k = (mem.lane 16 (k / 2) == ch) := by
    intro k hk
    rw [h_mask]
    exact pcmpeqw_pmovmskb_bit ch mem k hk
  let b := j / 2
  have hb16 : b < 16 := by omega
  have hj_even : j = 2 * b := by
    by_cases hj_is : j = 2 * b
    · exact hj_is
    · exfalso
      have : j = 2 * b + 1 := by omega
      have h_lt : 2 * b < j := by omega
      have h_k_lt : 2 * b < 32 := by omega
      have h_false_at := hj_false (2 * b) h_lt
      have h_bit_val := h_bit (2 * b) h_k_lt
      have h_div : (2 * b) / 2 = b := by omega
      rw [h_div] at h_bit_val
      have h_j_bit := h_bit j hj_lt
      rw [h_j_bit] at hj_true
      have : (j / 2) = b := rfl
      rw [this] at hj_true
      rw [hj_true] at h_bit_val
      rw [h_bit_val] at h_false_at
      contradiction
  have h_match : mem.lane 16 b = ch := by
    have hj_bit := h_bit j hj_lt
    rw [hj_bit] at hj_true
    have : j / 2 = b := rfl
    rw [this] at hj_true
    exact beq_iff_eq.mp hj_true
  have h_prev : ∀ i < b, mem.lane 16 i ≠ ch := by
    intro i hi heq
    have hi2_lt : 2 * i < j := by omega
    have hi2_32 : 2 * i < 32 := by omega
    have h_false := hj_false (2 * i) hi2_lt
    have h_bit_val := h_bit (2 * i) hi2_32
    have : (2 * i) / 2 = i := by omega
    rw [this, heq, beq_self_eq_true] at h_bit_val
    rw [h_bit_val] at h_false
    contradiction
  have hb_bsf : (BitVec.bsf mask).toNat = 2 * b := by rw [hj_bsf, hj_even]
  have hb_shift : ((BitVec.bsf mask) >>> 1).toNat = b := by
    simp [BitVec.toNat_ushiftRight, hb_bsf]
    rw [Nat.shiftRight_eq_div_pow]
    have : 2 * b / 2 ^ 1 = b := by omega
    rw [this]
  refine ⟨b, hb16, h_match, h_prev, hb_bsf, hb_shift⟩

theorem lane16_eq_lane8 (mem : BitVec 256) (i : Nat) (hi : i < 16) :
    mem.lane 16 i = (mem.lane 8 (2 * i)).zeroExtend 16 ||| ((mem.lane 8 (2 * i + 1)).zeroExtend 16 <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk16
  dsimp [BitVec.lane, BitVec.zeroExtend]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  have hdec16 : (decide (k < 16)) = true := decide_eq_true hk16
  simp only [hdec16, Bool.true_and]
  by_cases hk8 : k < 8
  · have hdec8 : (decide (k < 8)) = true := decide_eq_true hk8
    simp only [hdec8, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
    have : 8 * (2 * i) + k = 16 * i + k := by omega
    rw [this]
  · have hdec8 : (decide (k < 8)) = false := decide_eq_false hk8
    simp only [hdec8, Bool.false_and, Bool.false_or]
    have hk_ge : 8 ≤ k := by omega
    have hdec_ge : (decide (8 ≤ k)) = true := decide_eq_true hk_ge
    have hk_sub : k - 8 < 8 := by omega
    have hdec_sub : (decide (k - 8 < 8)) = true := decide_eq_true hk_sub
    have hk_sub16 : k - 8 < 16 := by omega
    have hdec_sub16 : (decide (k - 8 < 16)) = true := decide_eq_true hk_sub16
    simp only [hdec_ge, hdec_sub, hdec_sub16, Bool.true_and, Bool.not_false]
    have : 8 * (2 * i + 1) + (k - 8) = 16 * i + k := by omega
    rw [this]

theorem test_ch_eq (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535) (c : BitVec 16) :
    (c.zeroExtend 32 = ch) ↔ (c = ch.setWidth 16) := by
  constructor
  · intro h
    have h1 := congrArg (BitVec.extractLsb' 0 16) h
    revert h1
    bv_decide
  · intro h
    rw [h]
    have h_eq : ch = (ch.setWidth 16).zeroExtend 32 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth]
      have h1 : ch.toNat < 65536 := by omega
      have h2 : ch.toNat < 4294967296 := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    exact h_eq.symm

theorem zeroExtend32_inj (x y : BitVec 16) (h : x.zeroExtend 32 = y.zeroExtend 32) : x = y := by
  have h1 := congrArg (BitVec.setWidth 16) h
  revert h1
  bv_decide

theorem sw_add_ze (k : BitVec 64) (x : BitVec 32) :
    BitVec.setWidth 32 (k + x.zeroExtend 64) = BitVec.setWidth 32 k + x := by
  bv_decide

theorem sw_ofNat_add_bsf_uncomp (k b : Nat) (mask : BitVec 32) (hb : (BitVec.bsf mask).toNat = 2 * b) (hb16 : b < 16) :
    BitVec.setWidth 32 (BitVec.ofNat 64 k + ((BitVec.bsf mask) >>> 1).zeroExtend 64) = BitVec.ofNat 32 (k + b) := by
  rw [sw_add_ze]
  have : BitVec.setWidth 32 (BitVec.ofNat 64 k) = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [this]
  have hb_vec : (BitVec.bsf mask) >>> 1 = BitVec.ofNat 32 b := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, hb]
    rw [Nat.shiftRight_eq_div_pow]
    have : (2 * b) / 2 ^ 1 = b := by omega
    rw [this]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hb_vec]
  apply BitVec.eq_of_toNat_eq
  simp

theorem rcx_shl1 (r_left : Nat) (hr_left : r_left < 16) (rcx : BitVec 64)
    (h_rcx : rcx.setWidth 32 = .ofNat 32 r_left) :
    rcx.setWidth 32 <<< 1 = .ofNat 32 (2 * r_left) := by
  rw [h_rcx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have h1 : r_left % 4294967296 = r_left := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 * r_left % 4294967296 = 2 * r_left := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  dsimp [HShiftLeft.hShiftLeft, ShiftLeft.shiftLeft, Nat.shiftLeft]
  omega

theorem uncompressed_tail_shift_cnt_nat (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 16) (rcx : BitVec 64)
    (h_rcx : rcx.setWidth 32 = .ofNat 32 r_left) :
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(rcx.setWidth 32 <<< 1)))).toNat &&& 31) = 32 - 2 * r_left := by
  rw [rcx_shl1 r_left hr_left rcx h_rcx]
  exact tail_shift_cnt_nat (2 * r_left) (by omega) (by omega)

theorem uncompressed_avx_pre_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (k : Nat) (hk16 : k + 16 ≤ T) (hfrom : from_k ≤ k)
    (h_zero : (BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))))) == 0#32) :
    ∀ (i : Nat) (hi : i < 16),
      ((chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
  intro i hi h_eq
  have h_drop_get : (chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
      chars.get ⟨k + i, by omega⟩ := by
    have h_len' : (k + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
    have h1 : (chars.drop from_k).get ⟨(k + i) - from_k, h_len'⟩ = (chars.drop from_k)[(k + i) - from_k] := List.get_eq_getElem
    rw [h1, List.getElem_drop]
    have h2 : chars.get ⟨k + i, by omega⟩ = chars[k + i] := List.get_eq_getElem
    rw [h2]
    congr 1
    omega
  rw [h_drop_get] at h_eq
  have h_eq16 := (test_ch_eq ch h_ch (chars.get ⟨k + i, by omega⟩)).mp h_eq
  have h_chars_val := h_chars (k + i) (by omega)
  have h_chars16 := zeroExtend32_inj (chars.get ⟨k + i, by omega⟩) _ h_chars_val
  rw [h_chars16] at h_eq16
  have h2k0 : 2 * (k + i) = 2 * k + 2 * i := by omega
  have h2k1 : 2 * (k + i) + 1 = 2 * k + 2 * i + 1 := by omega
  rw [h2k0] at h_eq16
  have h_d0 := h_data (2 * k + 2 * i) (by omega)
  have h_d1 := h_data (2 * k + 2 * i + 1) (by omega)
  rw [← h_d0] at h_eq16
  rw [← h_d1] at h_eq16
  let bs := List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : ∀ j (hj : j < 32), bs.get ⟨j, by simp [bs]; omega⟩ = byteAt s.dmem A (2 * k + j) := by
    intro j hj; dsimp [bs]; simp
  have h_l0 := ofBytes_lane8 bs 32 h_bs_len (2 * i) (by omega)
  have h_l1 := ofBytes_lane8 bs 32 h_bs_len (2 * i + 1) (by omega)
  have h_bs0 := h_bs_get (2 * i) (by omega)
  have h_bs1 := h_bs_get (2 * i + 1) (by omega)
  rw [h_bs0] at h_l0
  rw [h_bs1] at h_l1
  have h_add : 2 * k + (2 * i + 1) = 2 * k + 2 * i + 1 := by omega
  rw [h_add] at h_l1
  rw [← h_l0, ← h_l1] at h_eq16
  have h_lane16 := lane16_eq_lane8 (BitVec.ofInt 256 (Int.ofBytes bs)) i (by omega)
  rw [← h_lane16] at h_eq16
  let mask := BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16)) (BitVec.ofInt 256 (Int.ofBytes bs)))
  have h_bit : mask.getLsbD (2 * i) = ((BitVec.ofInt 256 (Int.ofBytes bs)).lane 16 i == ch.setWidth 16) := by
    have : (2 * i) / 2 = i := by omega
    have h := pcmpeqw_pmovmskb_bit (ch.setWidth 16) (BitVec.ofInt 256 (Int.ofBytes bs)) (2 * i) (by omega)
    rw [this] at h
    exact h
  have h_true : mask.getLsbD (2 * i) = true := by
    rw [h_bit, h_eq16, beq_self_eq_true]
  have h_false : mask.getLsbD (2 * i) = false := by
    have h0 : mask = 0#32 := beq_iff_eq.mp h_zero
    rw [h0]
    apply BitVec.getLsbD_zero
  rw [h_false] at h_true
  contradiction

theorem uncompressed_avx_match_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (k : Nat) (hk16 : k + 16 ≤ T) (hfrom : from_k ≤ k)
    (hpre : ∀ (i : Nat) (hi : i < k - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (mask : BitVec 32)
    (h_mask : mask = (BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))))))
    (h_ne : mask ≠ 0#32) :
    indexOfSpec chars ch fromIndex = BitVec.setWidth 32 (.ofNat 64 k + ((BitVec.bsf mask) >>> 1).zeroExtend 64) := by
  let bs := List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : ∀ j (hj : j < 32), bs.get ⟨j, by simp [bs]; omega⟩ = byteAt s.dmem A (2 * k + j) := by
    intro j hj; dsimp [bs]; simp
  obtain ⟨b, hb16, hb_match, hb_prev, hb_bsf, hb_shift⟩ := bsf_mask_word (ch.setWidth 16) (BitVec.ofInt 256 (Int.ofBytes bs)) mask h_mask h_ne
  have h_word_char : ∀ i (hi : i < 16),
      (BitVec.ofInt 256 (Int.ofBytes bs)).lane 16 i = chars.get ⟨k + i, by omega⟩ := by
    intro i hi
    have h_lt0 : 2 * i < 32 := by omega
    have h_lt1 : 2 * i + 1 < 32 := by omega
    have h_l0 := ofBytes_lane8 bs 32 h_bs_len (2 * i) h_lt0
    have h_l1 := ofBytes_lane8 bs 32 h_bs_len (2 * i + 1) h_lt1
    have h_bs0 := h_bs_get (2 * i) h_lt0
    have h_bs1 := h_bs_get (2 * i + 1) h_lt1
    rw [h_bs0] at h_l0
    rw [h_bs1] at h_l1
    have h_add : 2 * k + (2 * i + 1) = 2 * k + 2 * i + 1 := by omega
    rw [h_add] at h_l1
    have h_idx0 : 2 * k + 2 * i = 2 * (k + i) := by omega
    have h_idx1 : 2 * k + 2 * i + 1 = 2 * (k + i) + 1 := by omega
    rw [h_idx0] at h_l0
    rw [h_idx1] at h_l1
    have h_d0 := h_data (2 * (k + i)) (by omega)
    have h_d1 := h_data (2 * (k + i) + 1) (by omega)
    have h_lane16 := lane16_eq_lane8 (BitVec.ofInt 256 (Int.ofBytes bs)) i (by omega)
    rw [h_lane16, h_l0, h_l1, h_d0, h_d1]
    have h_chars_val := h_chars (k + i) (by omega)
    exact (zeroExtend32_inj _ _ h_chars_val).symm
  have h_match : ((chars.drop from_k).get ⟨(k + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
    have h_drop_get : (chars.drop from_k).get ⟨(k + b) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨k + b, by omega⟩ := by
      have h_len' : (k + b) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(k + b) - from_k, h_len'⟩ = (chars.drop from_k)[(k + b) - from_k] := List.get_eq_getElem
      rw [h1, List.getElem_drop]
      have h2 : chars.get ⟨k + b, by omega⟩ = chars[k + b] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get]
    have h_wc := h_word_char b hb16
    rw [← h_wc]
    rw [hb_match]
    exact ((test_ch_eq ch h_ch _).mpr rfl)
  have hpre_chunk : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(k + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨k + i, by omega⟩ := by
      have h_len' : (k + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(k + i) - from_k, h_len'⟩ = (chars.drop from_k)[(k + i) - from_k] := List.get_eq_getElem
      rw [h1, List.getElem_drop]
      have h2 : chars.get ⟨k + i, by omega⟩ = chars[k + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_eq16 := (test_ch_eq ch h_ch _).mp h_eq
    have h_wc := h_word_char i (by omega)
    have h_prev_i := hb_prev i hi
    rw [h_wc] at h_prev_i
    exact h_prev_i h_eq16
  have h_spec := indexOfSpec_avx_match from_k T k b h_from_eq h_len (by omega) hfrom h_match hpre hpre_chunk
  rw [h_spec]
  exact (sw_ofNat_add_bsf_uncomp k b mask hb_bsf hb16).symm

@[expose] public def uncompressed_tail_mask (t s : MachineData) (A : BitVec 64) (ymm_target : AvxReg .W256) (T : Nat) : BitVec 32 :=
  (BitVec.pcmpeqw (t.zmms.get ymm_target)
    (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
    ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31)

theorem uncompressed_tail_none_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData) (ymm_target : AvxReg .W256)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16))
    (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 16) (hr_T : r_left ≤ T) (hT16 : 16 ≤ T)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_zero : uncompressed_tail_mask t s A ymm_target T == 0#32) :
    indexOfSpec chars ch fromIndex = -1#32 := by
  have hpre_tail : ∀ (i : Nat) (hi : i < r_left),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + i, by omega⟩ := by
      have h_len' : (T - r_left + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + i) - from_k] := List.get_eq_getElem
      rw [h1, List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + i, by omega⟩ = chars[T - r_left + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_eq16 := (test_ch_eq ch h_ch (chars.get ⟨T - r_left + i, by omega⟩)).mp h_eq
    have h_chars_val := h_chars (T - r_left + i) (by omega)
    have h_chars16 := zeroExtend32_inj (chars.get ⟨T - r_left + i, by omega⟩) _ h_chars_val
    rw [h_chars16] at h_eq16
    let bs := List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)
    have h_bs_len : bs.length = 32 := by simp [bs]
    have h_bs_get : ∀ j (hj : j < 32), bs.get ⟨j, by simp [bs]; omega⟩ = byteAt s.dmem A (2 * T - 32 + j) := by
      intro j hj; dsimp [bs]; simp
    have h_lt0 : 2 * (16 - r_left + i) < 32 := by omega
    have h_lt1 : 2 * (16 - r_left + i) + 1 < 32 := by omega
    have h_l0 := ofBytes_lane8 bs 32 h_bs_len (2 * (16 - r_left + i)) h_lt0
    have h_l1 := ofBytes_lane8 bs 32 h_bs_len (2 * (16 - r_left + i) + 1) h_lt1
    have h_bs0 := h_bs_get (2 * (16 - r_left + i)) h_lt0
    have h_bs1 := h_bs_get (2 * (16 - r_left + i) + 1) h_lt1
    rw [h_bs0] at h_l0
    rw [h_bs1] at h_l1
    have h_idx0 : 2 * T - 32 + 2 * (16 - r_left + i) = 2 * (T - r_left + i) := by omega
    have h_idx1 : 2 * T - 32 + (2 * (16 - r_left + i) + 1) = 2 * (T - r_left + i) + 1 := by omega
    rw [h_idx0] at h_l0
    rw [h_idx1] at h_l1
    have h_d0 := h_data (2 * (T - r_left + i)) (by omega)
    have h_d1 := h_data (2 * (T - r_left + i) + 1) (by omega)
    rw [← h_d0, ← h_d1] at h_eq16
    rw [← h_l0, ← h_l1] at h_eq16
    have h_lane16 := lane16_eq_lane8 (BitVec.ofInt 256 (Int.ofBytes bs)) (16 - r_left + i) (by omega)
    rw [← h_lane16] at h_eq16
    let full_mask := BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16)) (BitVec.ofInt 256 (Int.ofBytes bs)))
    have h_bit : full_mask.getLsbD (2 * (16 - r_left + i)) = ((BitVec.ofInt 256 (Int.ofBytes bs)).lane 16 (16 - r_left + i) == ch.setWidth 16) := by
      have : (2 * (16 - r_left + i)) / 2 = 16 - r_left + i := by omega
      have h := pcmpeqw_pmovmskb_bit (ch.setWidth 16) (BitVec.ofInt 256 (Int.ofBytes bs)) (2 * (16 - r_left + i)) (by omega)
      rw [this] at h
      exact h
    have h_mask_bit : (uncompressed_tail_mask t s A ymm_target T).getLsbD (2 * i) = true := by
      unfold uncompressed_tail_mask
      rw [ushiftRight_getLsbD]
      rw [uncompressed_tail_shift_cnt_nat r_left hr0 hr_left (t.regs.get64 Reg64.rcx) h_rcx]
      rw [h_target]
      have : 32 - 2 * r_left + 2 * i = 2 * (16 - r_left + i) := by omega
      rw [this]
      rw [h_bit, h_eq16, beq_self_eq_true]
    have h_zero_bit : (uncompressed_tail_mask t s A ymm_target T).getLsbD (2 * i) = false := by
      have h0 : uncompressed_tail_mask t s A ymm_target T = 0#32 := beq_iff_eq.mp h_zero
      rw [h0]
      apply BitVec.getLsbD_zero
    rw [h_zero_bit] at h_mask_bit
    contradiction
  exact indexOfSpec_tail_none from_k T r_left h_from_eq h_len hr_T h_from_k hpre hpre_tail

theorem uncompressed_tail_match_step (s : MachineData) (A : BitVec 64) (T : Nat) (d : List UInt8)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16)) (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (from_k : Nat) (fromIndex : BitVec 32)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData) (ymm_target : AvxReg .W256)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16))
    (r_left : Nat) (hr0 : 0 < r_left) (hr_left : r_left < 16) (hr_T : r_left ≤ T) (hT16 : 16 ≤ T)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (mask : BitVec 32)
    (h_mask : mask = uncompressed_tail_mask t s A ymm_target T)
    (h_ne : mask ≠ 0#32) :
    indexOfSpec chars ch fromIndex = BitVec.setWidth 32 (.ofNat 64 (T - r_left) + ((BitVec.bsf mask) >>> 1).zeroExtend 64) := by
  obtain ⟨j, hj_lt, hj_bsf, hj_true, hj_false⟩ := bsf_toNat mask (by decide) h_ne
  let bs := List.map (fun m => byteAt s.dmem A (2 * T - 32 + m)) (List.range 32)
  have h_bs_len : bs.length = 32 := by simp [bs]
  have h_bs_get : ∀ m (hm : m < 32), bs.get ⟨m, by simp [bs]; omega⟩ = byteAt s.dmem A (2 * T - 32 + m) := by
    intro m hm; dsimp [bs]; simp
  have h_mask_bit_eq : ∀ i, mask.getLsbD i =
      (BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
        (BitVec.ofInt 256 (Int.ofBytes bs)))).getLsbD ((32 - 2 * r_left) + i) := by
    intro i
    rw [h_mask]
    unfold uncompressed_tail_mask
    rw [ushiftRight_getLsbD]
    rw [uncompressed_tail_shift_cnt_nat r_left hr0 hr_left (t.regs.get64 Reg64.rcx) h_rcx, h_target]
  have hj_2r : j < 2 * r_left := by
    by_cases hj : j < 2 * r_left
    · exact hj
    · have h_out : 32 ≤ (32 - 2 * r_left) + j := by omega
      have h_bit_false : mask.getLsbD j = false := by
        rw [h_mask_bit_eq]
        exact getLsbD_ge _ _ h_out
      rw [hj_true] at h_bit_false
      contradiction
  let b := j / 2
  have hb_r_left : b < r_left := by omega
  have hb16 : b < 16 := by omega
  have h_underlying_bit : ∀ k < 32,
      (BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
        (BitVec.ofInt 256 (Int.ofBytes bs)))).getLsbD k =
      ((BitVec.ofInt 256 (Int.ofBytes bs)).lane 16 (k / 2) == ch.setWidth 16) := by
    intro k hk
    exact pcmpeqw_pmovmskb_bit (ch.setWidth 16) (BitVec.ofInt 256 (Int.ofBytes bs)) k hk
  have hj_even : j = 2 * b := by
    by_cases hj_is : j = 2 * b
    · exact hj_is
    · exfalso
      have : j = 2 * b + 1 := by omega
      have h_lt : 2 * b < j := by omega
      have h_false_at := hj_false (2 * b) h_lt
      rw [h_mask_bit_eq (2 * b)] at h_false_at
      rw [h_mask_bit_eq j] at hj_true
      have h_idx_b : (32 - 2 * r_left) + 2 * b = 2 * (16 - r_left + b) := by omega
      have h_idx_j : (32 - 2 * r_left) + j = 2 * (16 - r_left + b) + 1 := by omega
      rw [h_idx_b] at h_false_at
      rw [h_idx_j] at hj_true
      have h_b_32 : 2 * (16 - r_left + b) < 32 := by omega
      have h_j_32 : 2 * (16 - r_left + b) + 1 < 32 := by omega
      have hb_val := h_underlying_bit (2 * (16 - r_left + b)) h_b_32
      have hj_val := h_underlying_bit (2 * (16 - r_left + b) + 1) h_j_32
      have h_div_b : 2 * (16 - r_left + b) / 2 = 16 - r_left + b := by omega
      have h_div_j : (2 * (16 - r_left + b) + 1) / 2 = 16 - r_left + b := by omega
      rw [hb_val] at h_false_at
      rw [hj_val] at hj_true
      rw [h_div_b] at h_false_at
      rw [h_div_j] at hj_true
      rw [hj_true] at h_false_at
      contradiction
  have h_word_char : ∀ i (hi : i < r_left),
      (BitVec.ofInt 256 (Int.ofBytes bs)).lane 16 (16 - r_left + i) = chars.get ⟨T - r_left + i, by omega⟩ := by
    intro i hi
    have h_lt0 : 2 * (16 - r_left + i) < 32 := by omega
    have h_lt1 : 2 * (16 - r_left + i) + 1 < 32 := by omega
    have h_l0 := ofBytes_lane8 bs 32 h_bs_len (2 * (16 - r_left + i)) h_lt0
    have h_l1 := ofBytes_lane8 bs 32 h_bs_len (2 * (16 - r_left + i) + 1) h_lt1
    have h_bs0 := h_bs_get (2 * (16 - r_left + i)) h_lt0
    have h_bs1 := h_bs_get (2 * (16 - r_left + i) + 1) h_lt1
    rw [h_bs0] at h_l0
    rw [h_bs1] at h_l1
    have h_idx0 : 2 * T - 32 + 2 * (16 - r_left + i) = 2 * (T - r_left + i) := by omega
    have h_idx1 : 2 * T - 32 + (2 * (16 - r_left + i) + 1) = 2 * (T - r_left + i) + 1 := by omega
    rw [h_idx0] at h_l0
    rw [h_idx1] at h_l1
    have h_d0 := h_data (2 * (T - r_left + i)) (by omega)
    have h_d1 := h_data (2 * (T - r_left + i) + 1) (by omega)
    have h_lane16 := lane16_eq_lane8 (BitVec.ofInt 256 (Int.ofBytes bs)) (16 - r_left + i) (by omega)
    rw [h_lane16, h_l0, h_l1, h_d0, h_d1]
    have h_chars_val := h_chars (T - r_left + i) (by omega)
    exact (zeroExtend32_inj _ _ h_chars_val).symm
  have h_match : ((chars.drop from_k).get ⟨(T - r_left + b) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 = ch := by
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + b) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + b, by omega⟩ := by
      have h_len' : (T - r_left + b) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + b) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + b) - from_k] := List.get_eq_getElem
      rw [h1, List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + b, by omega⟩ = chars[T - r_left + b] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get]
    have h_mask_b : mask.getLsbD (2 * b) = true := by rw [← hj_even]; exact hj_true
    rw [h_mask_bit_eq (2 * b)] at h_mask_b
    have h_idx_b : (32 - 2 * r_left) + 2 * b = 2 * (16 - r_left + b) := by omega
    rw [h_idx_b] at h_mask_b
    have hb_32 : 2 * (16 - r_left + b) < 32 := by omega
    have hb_val := h_underlying_bit (2 * (16 - r_left + b)) hb_32
    have : (2 * (16 - r_left + b)) / 2 = 16 - r_left + b := by omega
    rw [hb_val, this] at h_mask_b
    have h_wc := h_word_char b hb_r_left
    rw [h_wc] at h_mask_b
    have h_eq16 := beq_iff_eq.mp h_mask_b
    exact (test_ch_eq ch h_ch _).mpr h_eq16
  have hpre_chunk : ∀ (i : Nat) (hi : i < b),
      ((chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi h_eq
    have h_drop_get : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, by rw [List.length_drop, h_len]; omega⟩ =
        chars.get ⟨T - r_left + i, by omega⟩ := by
      have h_len' : (T - r_left + i) - from_k < (chars.drop from_k).length := by rw [List.length_drop, h_len]; omega
      have h1 : (chars.drop from_k).get ⟨(T - r_left + i) - from_k, h_len'⟩ = (chars.drop from_k)[(T - r_left + i) - from_k] := List.get_eq_getElem
      rw [h1, List.getElem_drop]
      have h2 : chars.get ⟨T - r_left + i, by omega⟩ = chars[T - r_left + i] := List.get_eq_getElem
      rw [h2]
      congr 1
      omega
    rw [h_drop_get] at h_eq
    have h_eq16 := (test_ch_eq ch h_ch _).mp h_eq
    have hi_lt_j : 2 * i < j := by omega
    have hi_false := hj_false (2 * i) hi_lt_j
    rw [h_mask_bit_eq (2 * i)] at hi_false
    have h_idx_i : (32 - 2 * r_left) + 2 * i = 2 * (16 - r_left + i) := by omega
    rw [h_idx_i] at hi_false
    have hi_32 : 2 * (16 - r_left + i) < 32 := by omega
    have hi_val := h_underlying_bit (2 * (16 - r_left + i)) hi_32
    have : (2 * (16 - r_left + i)) / 2 = 16 - r_left + i := by omega
    rw [hi_val, this] at hi_false
    have h_wc := h_word_char i (by omega)
    rw [h_wc, h_eq16, beq_self_eq_true] at hi_false
    contradiction
  have h_spec := indexOfSpec_avx_match from_k T (T - r_left) b h_from_eq h_len (by omega) h_from_k h_match hpre hpre_chunk
  rw [h_spec]
  have hb_bsf : (BitVec.bsf mask).toNat = 2 * b := by rw [hj_bsf, hj_even]
  exact (sw_ofNat_add_bsf_uncomp (T - r_left) b mask hb_bsf hb16).symm

theorem uncompressed_tail_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT16 : 16 ≤ T)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm_target v1).set ymm_match v2)
    (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
    (r_left : Nat) (hr_left : r_left < 16)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_off : t.regs.get64 temp_offset = .ofNat 64 (T - r_left))
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16)) :
    Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 77)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  -- Directive 77: .label uncompressed_tail
  sstep
  refine Program.loopCont_of_le (j := 78) (by rw [h_prog_len]; omega) ?_
  -- Directive 78: testl %ecx, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 79) (by rw [h_prog_len]; omega) ?_
  -- Directive 79: je not_found_vzero
  sstep
  have h_and_self : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) &&& BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) =
      (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hr0 : r_left = 0
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = true := by
      rw [h_rcx, hr0]; rfl
    simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
    refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
    have hspec := indexOfSpec_tail_not_found from_k T r_left h_from_eq h_len hpre hr0
    exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ chars ch fromIndex hspec hm hr hz
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = false := by
      rw [h_rcx]
      have : (BitVec.ofNat 32 r_left == 0#32) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact hr0 this
      exact this
    simp only [hzf, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 80) (by rw [h_prog_len]; omega) ?_
    have haddr_tail : t.regs.get64 str + BitVec.ofInt 64 ((t.regs.get64 temp_len).signed * 2) + -16#64 =
        A + .ofNat 64 (2 * T - 32) + 16#64 := by
      rw [hstr, h_len_reg, ofInt_signed_mul2, ofNat_mul2]
      have : (BitVec.ofNat 64 (2 * T) : BitVec 64) = BitVec.ofNat 64 (2 * T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    have hload : t.dmem.loadInt (t.regs.get64 str + BitVec.ofInt 64 ((t.regs.get64 temp_len).signed * 2) + -16#64) 32 =
        some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (2 * T - 32 + j))) := by
      rw [haddr_tail, hm]
      exact load_chunk s.dmem A (2 * T - 32) 32 (2 * T) h_some (by omega)
    -- Directive 80: vpcmpeqw
    sstep
    have h_addr := addr_sib2_disp' t.regs str temp_len (-16) (Host.addrOf (H.start + 80)...Host.addrOf (H.start + 81))
    rw [h_addr]
    simp only [ofInt_signed_mul2, ofNat_mul2, hstr, h_len_reg]
    have : (Int64.toBitVec (-16) : BitVec 64) = -16#64 := rfl
    rw [this]
    have : A + BitVec.ofNat 64 (2 * T) + -16#64 = A + BitVec.ofNat 64 (2 * T - 32) + 16#64 := by
      have : (BitVec.ofNat 64 (2 * T) : BitVec 64) = BitVec.ofNat 64 (2 * T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    rw [this, hm, load_chunk s.dmem A (2 * T - 32) 32 (2 * T) h_some (by omega)]
    dsimp only []
    refine Program.loopCont_of_le (j := 81) (by rw [h_prog_len]; omega) ?_
    -- Directive 81: vpmovmskb
    sstep
    refine Program.loopCont_of_le (j := 82) (by rw [h_prog_len]; omega) ?_
    -- Directive 82: shll , %ecx
    sstep
    intro _
    refine Program.loopCont_of_le (j := 83) (by rw [h_prog_len]; omega) ?_
    -- Directive 83: negl %ecx
    sstep
    refine Program.loopCont_of_le (j := 84) (by rw [h_prog_len]; omega) ?_
    -- Directive 84: addl 2, %ecx
    sstep
    refine Program.loopCont_of_le (j := 85) (by rw [h_prog_len]; omega) ?_
    -- Directive 85: shrl %cl, temp_mask
    sstep
    have h_set_rcx : ∀ (regs : Reg64s) (v : BitVec 64), (regs.set64 Reg64.rcx v).rcx = UInt64.ofBitVec v := fun _ _ => rfl
    simp only [h_set_rcx, UInt64.toBitVec_ofBitVec]
    have h_rcx_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    have h_mask_ne : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
    simp only [h_rcx_ne, h_mask_ne, Bool.false_eq_true, ↓reduceIte]
    have h_rcx_w32 : BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) = BitVec.ofNat 32 r_left := h_rcx
    have h_cond : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 == 0) = false := by
      rw [h_rcx_w32]
      apply Proof.shr_count_ne_zero_uncompressed_nat (hr0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega) (hr_lt := by
        have : (BitVec.ofNat 32 r_left).toNat < (16#32 : BitVec 32).toNat := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        exact this)
    simp only [h_cond, Bool.false_eq_true, ↓reduceIte]
    have h_lt : (BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 < 32 := by
      exact Proof.test_and_lt _
    simp only [h_lt, ↓reduceIte]
    intro af
    let shifted_mask := (BitVec.pcmpeqw (t.zmms.get ymm_target)
        (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
        ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31)
    by_cases h_one : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 == 1) = true
    · simp only [h_one, ↓reduceIte]
      refine Program.loopCont_of_le (j := 86) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 87) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
        refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (uncompressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre (by exact hzf)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 88) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := (BitVec.bsf shifted_mask) >>> 1
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_uncompressed_tail_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (uncompressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)
    · simp only [h_one, Bool.false_eq_true, ↓reduceIte]
      intro of
      refine Program.loopCont_of_le (j := 86) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 87) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 112) rfl]
        refine Program.loopCont_of_le (j := 112) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (uncompressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre (by exact hzf)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 88) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := (BitVec.bsf shifted_mask) >>> 1
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_uncompressed_tail_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (uncompressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)


theorem uncompressed_tail_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT16 : 16 ≤ T)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k)
    (t : MachineData)
    (hm : t.dmem = s.dmem)
    (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
    (hz : ∃ v1 v2, t.zmms = (s.zmms.set ymm_target v1).set ymm_match v2)
    (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
    (r_left : Nat) (hr_left : r_left < 16)
    (h_rcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r_left)
    (h_off : t.regs.get64 temp_offset = .ofNat 64 (T - r_left))
    (h_from_k : from_k ≤ T - r_left)
    (hpre : ∀ (i : Nat) (hi : i < T - r_left - from_k),
      ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch)
    (h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16)) :
    Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match) H
      (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
      (StringIndexOfSlow slow ch s)
      ⟨t, Host.addrOf (H.start + 81)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  -- Directive 77: .label uncompressed_tail
  sstep
  refine Program.loopCont_of_le (j := 82) (by rw [h_prog_len]; omega) ?_
  -- Directive 78: testl %ecx, %ecx
  sstep
  intro _
  refine Program.loopCont_of_le (j := 83) (by rw [h_prog_len]; omega) ?_
  -- Directive 79: je not_found_vzero
  sstep
  have h_and_self : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) &&& BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) =
      (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hr0 : r_left = 0
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = true := by
      rw [h_rcx, hr0]; rfl
    simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
    refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
    have hspec := indexOfSpec_tail_not_found from_k T r_left h_from_eq h_len hpre hr0
    exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ chars ch fromIndex hspec hm hr hz
  · have hzf : (BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) == 0#32) = false := by
      rw [h_rcx]
      have : (BitVec.ofNat 32 r_left == 0#32) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact hr0 this
      exact this
    simp only [hzf, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 84) (by rw [h_prog_len]; omega) ?_
    have haddr_tail : t.regs.get64 str + BitVec.ofInt 64 ((t.regs.get64 temp_len).signed * 2) + -16#64 =
        A + .ofNat 64 (2 * T - 32) + 16#64 := by
      rw [hstr, h_len_reg, ofInt_signed_mul2, ofNat_mul2]
      have : (BitVec.ofNat 64 (2 * T) : BitVec 64) = BitVec.ofNat 64 (2 * T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    have hload : t.dmem.loadInt (t.regs.get64 str + BitVec.ofInt 64 ((t.regs.get64 temp_len).signed * 2) + -16#64) 32 =
        some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (2 * T - 32 + j))) := by
      rw [haddr_tail, hm]
      exact load_chunk s.dmem A (2 * T - 32) 32 (2 * T) h_some (by omega)
    -- Directive 80: vpcmpeqw
    sstep
    have h_addr := addr_sib2_disp' t.regs str temp_len (-16) (Host.addrOf (H.start + 84)...Host.addrOf (H.start + 85))
    rw [h_addr]
    simp only [ofInt_signed_mul2, ofNat_mul2, hstr, h_len_reg]
    have : (Int64.toBitVec (-16) : BitVec 64) = -16#64 := rfl
    rw [this]
    have : A + BitVec.ofNat 64 (2 * T) + -16#64 = A + BitVec.ofNat 64 (2 * T - 32) + 16#64 := by
      have : (BitVec.ofNat 64 (2 * T) : BitVec 64) = BitVec.ofNat 64 (2 * T - 32) + 32#64 := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [this]
      bv_decide
    rw [this, hm, load_chunk s.dmem A (2 * T - 32) 32 (2 * T) h_some (by omega)]
    dsimp only []
    refine Program.loopCont_of_le (j := 85) (by rw [h_prog_len]; omega) ?_
    -- Directive 81: vpmovmskb
    sstep
    refine Program.loopCont_of_le (j := 86) (by rw [h_prog_len]; omega) ?_
    -- Directive 82: shll , %ecx
    sstep
    intro _
    refine Program.loopCont_of_le (j := 87) (by rw [h_prog_len]; omega) ?_
    -- Directive 83: negl %ecx
    sstep
    refine Program.loopCont_of_le (j := 88) (by rw [h_prog_len]; omega) ?_
    -- Directive 84: addl 2, %ecx
    sstep
    refine Program.loopCont_of_le (j := 89) (by rw [h_prog_len]; omega) ?_
    -- Directive 85: shrl %cl, temp_mask
    sstep
    have h_set_rcx : ∀ (regs : Reg64s) (v : BitVec 64), (regs.set64 Reg64.rcx v).rcx = UInt64.ofBitVec v := fun _ _ => rfl
    simp only [h_set_rcx, UInt64.toBitVec_ofBitVec]
    have h_rcx_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    have h_mask_ne : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
    simp only [h_rcx_ne, h_mask_ne, Bool.false_eq_true, ↓reduceIte]
    have h_rcx_w32 : BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) = BitVec.ofNat 32 r_left := h_rcx
    have h_cond : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 == 0) = false := by
      rw [h_rcx_w32]
      apply Proof.shr_count_ne_zero_uncompressed_nat (hr0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega) (hr_lt := by
        have : (BitVec.ofNat 32 r_left).toNat < (16#32 : BitVec 32).toNat := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        exact this)
    simp only [h_cond, Bool.false_eq_true, ↓reduceIte]
    have h_lt : (BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 < 32 := by
      exact Proof.test_and_lt _
    simp only [h_lt, ↓reduceIte]
    intro af
    let shifted_mask := (BitVec.pcmpeqw (t.zmms.get ymm_target)
        (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32))))).pmovmskb.ushiftRight
        ((BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31)
    by_cases h_one : ((BitVec.extractLsb' 0 8
          (BitVec.setWidth 64 (32#32 + -(BitVec.setWidth 32 (t.regs.get64 Reg64.rcx) <<< 1)))).toNat &&& 31 == 1) = true
    · simp only [h_one, ↓reduceIte]
      refine Program.loopCont_of_le (j := 90) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 91) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
        refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (uncompressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre (by exact hzf)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 92) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := (BitVec.bsf shifted_mask) >>> 1
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_uncompressed_tail_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (uncompressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)
    · simp only [h_one, Bool.false_eq_true, ↓reduceIte]
      intro of
      refine Program.loopCont_of_le (j := 90) (by rw [h_prog_len]; omega) ?_
      sstep
      intro _
      refine Program.loopCont_of_le (j := 91) (by rw [h_prog_len]; omega) ?_
      sstep
      have h_and_self : ∀ (x : BitVec 32), (x &&& x == 0#32) = (x == 0#32) := fun x => by bv_decide
      simp only [h_and_self]
      change Effects.All _ (if (shifted_mask == 0#32) = true then _ else _)
      by_cases hzf : (shifted_mask == 0#32) = true
      · simp only [hzf, addrOf_label hlab (H := H) (i := 116) rfl]
        refine Program.loopCont_of_le (j := 116) (by rw [h_prog_len]; omega) ?_
        exact ret_not_found_vzero_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ chars ch fromIndex (uncompressed_tail_none_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre (by exact hzf)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _)
      · simp only [hzf, Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 92) (by rw [h_prog_len]; omega) ?_
        let b : BitVec 32 := (BitVec.bsf shifted_mask) >>> 1
        let idx : BitVec 32 := BitVec.setWidth 32 (.ofNat 64 (T - r_left) + b.zeroExtend 64)
        have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
        have h_toff_mask : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
        have h_mask_ne32 : shifted_mask ≠ 0#32 := by
          intro h
          simp [h] at hzf
        exact ret_uncompressed_tail_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s _ chars ch fromIndex idx (uncompressed_tail_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq t ymm_target h_target r_left (by omega) hr_left (by omega) hT16 h_rcx h_from_k hpre shifted_mask rfl (by exact h_mask_ne32)) rfl (by
            intro r hr_out
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr_out
            simp only [get64_set64, hr_out.2.2.2.2, hr_out.2.1, ↓reduceIte]
            exact hr r (by
              intro h_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
              rcases h_in with h | h | h | h | h
              · exact hr_out.1 h
              · exact hr_out.2.1 h
              · exact hr_out.2.2.1 h
              · exact hr_out.2.2.2.1 h
              · exact hr_out.2.2.2.2 h)) (by
            obtain ⟨v1, v2, hv⟩ := hz
            refine ⟨v1, ?_⟩
            refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
              (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * T - 32 + j)) (List.range 32)))), ?_⟩
            rw [hv]
            dsimp only []
            exact zmms_set_set (s.zmms.set ymm_target v1) ymm_match v2 _) (by
            simp only [get64_set64, ite_true, sw32_64]
            exact h_mask_ne32) (by
            simp only [get64_set64, h_toff_mask, h_toff_rcx, sw32_64, ↓reduceIte, h_off]
            rfl)




theorem bv_and_self_zero (x : BitVec 32) : (x &&& x == 0#32) = (x == 0#32) := by bv_decide





theorem compressed_avx_loop_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT32 : 32 ≤ T)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ r k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : ∃ v2, t.zmms = (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))).set ymm_match v2)
      (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
      (hoff : t.regs.get64 temp_offset = .ofNat 64 k)
      (hrcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r)
      (hkr : k + r = T)
      (hr32 : 32 ≤ r)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 20)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t hm hr hz h_len_reg hoff hrcx hkr hr32 h_from_k hpre
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
  have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 32 =
      some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (k + j))) := by
    rw [haddr, hm]
    exact load_chunk _ _ k 32 T h_some (by omega)
  have h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch) := by
    obtain ⟨v2, hv⟩ := hz
    rw [hv]
    exact zmms_get_target s.zmms ymm_target ymm_match (BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) v2 h_ymm_diff
  -- Directive 20: .label "compressed_avx_loop"
  sstep
  refine Program.loopCont_of_le (j := 21) (by rw [h_prog_len]; omega) ?_
  -- Directive 21: vpcmpeqb 16(str, temp_offset, 1), ymm_target, ymm_match
  sstep
  simp only [hstr, hoff]
  rw [← haddr, hload]
  dsimp only []
  refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
  -- Directive 22: vpmovmskb ymm_match, temp_mask
  sstep
  refine Program.loopCont_of_le (j := 23) (by rw [h_prog_len]; omega) ?_
  -- Directive 23: testl temp_mask, temp_mask
  sstep
  intro _
  refine Program.loopCont_of_le (j := 24) (by rw [h_prog_len]; omega) ?_
  -- Directive 24: jnz compressed_match_found
  sstep
  let chunk_mask := (BitVec.pcmpeqb (t.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32))))).pmovmskb
  have h_and_self := bv_and_self_zero chunk_mask
  change Effects.All _ (if (!chunk_mask &&& chunk_mask == 0#32) = true then _ else _)
  rw [h_and_self]
  by_cases h_zero : (chunk_mask == 0#32) = true
  · simp only [h_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 25) (by rw [h_prog_len]; omega) ?_
    -- Directive 25: addq $32, temp_offset
    sstep
    simp only [hd_offset_mask, ↓reduceIte, hoff]
    rw [← BitVec.ofNat_add]
    refine Program.loopCont_of_le (j := 26) (by rw [h_prog_len]; omega) ?_
    -- Directive 26: subl $32, %ecx
    sstep
    have h_rcx_toff : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
    have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
    have h_rcx_mask : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    simp only [h_rcx_toff, h_toff_rcx, h_rcx_mask, get64_set64, Bool.false_eq_true, ↓reduceIte, hrcx]
    have h32 : (32#32 : BitVec 32) = BitVec.ofNat 32 32 := rfl
    rw [h32, ofNat32_sub_lit (show 32 ≤ r by omega)]
    refine Program.loopCont_of_le (j := 27) (by rw [h_prog_len]; omega) ?_
    -- Directive 27: cmpl $32, %ecx
    sstep
    refine Program.loopCont_of_le (j := 28) (by rw [h_prog_len]; omega) ?_
    -- Directive 28: jae compressed_avx_loop
    sstep
    have hr_sub_lt : r - 32 < 2 ^ 32 := by omega
    have h32 : (32#32 : BitVec 32) = BitVec.ofNat 32 32 := rfl
    simp only [h32, cf_ofNat32 (x := r - 32) (c := 32) hr_sub_lt (by decide)]
    have hpre_extended : ∀ (i : Nat) (hi : i < (k + 32) - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
      intro i hi
      by_cases hi_old : i < k - from_k
      · exact hpre i hi_old
      · have hj : i - (k - from_k) < 32 := by omega
        have h_step := compressed_avx_pre_step s A T d h_data ch h_ch chars h_len h_chars from_k t ymm_target h_target k (by omega) h_from_k h_zero (i - (k - from_k)) hj
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨(k + (i - (k - from_k))) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext; dsimp only []; omega
        rw [hext]
        exact h_step
    by_cases hlt : r - 32 < 32
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 29) (by rw [h_prog_len]; omega) ?_
      have hT_sub : T - (r - 32) = k + 32 := by omega
      have h_from_k_le : from_k ≤ T - (r - 32) := by omega
      have hpre_tail_in : ∀ (i : Nat) (hi : i < T - (r - 32) - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        rw [hT_sub] at hi
        exact hpre_extended i hi
      exact compressed_tail_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct hlab H s c d A T hA hT hT32 h_data h_some ch h_ch chars h_len h_chars fromIndex from_k h_from_eq
        _ hm (by
          intro r' hr'
          have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            intro h_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
            rcases h_in with rfl | rfl | rfl | rfl | rfl
            · exact hr'.1 rfl
            · exact hr'.2.1 rfl
            · exact hr'.2.2.1 rfl
            · exact hr'.2.2.2.1 rfl
            · exact hr'.2.2.2.2 rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
          exact hr r' hr_not_in) (by
          obtain ⟨v2, hv⟩ := hz
          refine ⟨BitVec.broadcastb 256 (BitVec.setWidth 8 ch), ?_⟩
          refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
            (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
          rw [hv]
          dsimp only []
          exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))) ymm_match v2 _) (by
          simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (r - 32) hlt (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, hT_sub, Nat.add_comm])
        h_from_k_le hpre_tail_in (by
          obtain ⟨v2, hv⟩ := hz
          rw [hv, zmms_set_set]
          exact zmms_get_target s.zmms ymm_target ymm_match _ _ h_ymm_diff)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 20) rfl]
      refine Program.loopCont_of_le (j := 20) (by rw [h_prog_len]; omega) ?_
      refine ih (r - 32) (by omega) (k + 32) _ hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
        rw [hv, zmms_set_set]) (by
        simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, Nat.add_comm])
        (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by omega) (by omega) (by omega) hpre_extended
  · simp only [h_zero, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 44) rfl]
    refine Program.loopCont_of_le (j := 44) (by rw [h_prog_len]; omega) ?_
    let idx := BitVec.setWidth 32 (.ofNat 64 k + (BitVec.bsf chunk_mask).zeroExtend 64)
    have h_mask_ne32 : chunk_mask ≠ 0#32 := by
      intro h
      simp [h] at h_zero
    have hspec_here : indexOfSpec chars ch fromIndex = idx := by
      have h_chunk_mask_eq : chunk_mask = BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32))))) := by
        dsimp [chunk_mask]
        rw [h_target]
      exact compressed_avx_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq k (by omega) h_from_k hpre chunk_mask h_chunk_mask_eq h_mask_ne32
    exact ret_compressed_avx_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct hlab H s _ chars ch fromIndex idx hspec_here hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.broadcastb 256 (BitVec.setWidth 8 ch), ?_⟩
        refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
        rw [hv]
        dsimp only []
        exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))) ymm_match v2 _) (by
        simp only [get64_set64, sw32_64, ite_true]
        exact h_mask_ne32) (by
        simp only [get64_set64, hd_offset_mask, ↓reduceIte, sw32_64, hoff]
        rfl)


theorem compressed_avx_loop_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT32 : 32 ≤ T)
    (h_data : ∀ i < T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 127)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ r k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : ∃ v2, t.zmms = (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))).set ymm_match v2)
      (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
      (hoff : t.regs.get64 temp_offset = .ofNat 64 k)
      (hrcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r)
      (hkr : k + r = T)
      (hr32 : 32 ≤ r)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 24)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t hm hr hz h_len_reg hoff hrcx hkr hr32 h_from_k hpre
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  have haddr : A + 16#64 + .ofNat 64 k = A + .ofNat 64 k + 16#64 := by ac_rfl
  have hload : t.dmem.loadInt (A + 16#64 + .ofNat 64 k) 32 =
      some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (k + j))) := by
    rw [haddr, hm]
    exact load_chunk _ _ k 32 T h_some (by omega)
  have h_target : t.zmms.get ymm_target = BitVec.broadcastb 256 (BitVec.setWidth 8 ch) := by
    obtain ⟨v2, hv⟩ := hz
    rw [hv]
    exact zmms_get_target s.zmms ymm_target ymm_match (BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) v2 h_ymm_diff
  -- Directive 24: .label "compressed_avx_loop"
  sstep
  refine Program.loopCont_of_le (j := 25) (by rw [h_prog_len]; omega) ?_
  -- Directive 25: vpcmpeqb 16(str, temp_offset, 1), ymm_target, ymm_match
  sstep
  simp only [hstr, hoff]
  rw [← haddr, hload]
  dsimp only []
  refine Program.loopCont_of_le (j := 26) (by rw [h_prog_len]; omega) ?_
  -- Directive 26: vpmovmskb ymm_match, temp_mask
  sstep
  refine Program.loopCont_of_le (j := 27) (by rw [h_prog_len]; omega) ?_
  -- Directive 27: testl temp_mask, temp_mask
  sstep
  intro _
  refine Program.loopCont_of_le (j := 28) (by rw [h_prog_len]; omega) ?_
  -- Directive 28: jnz compressed_match_found
  sstep
  let chunk_mask := (BitVec.pcmpeqb (t.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32))))).pmovmskb
  have h_and_self := bv_and_self_zero chunk_mask
  change Effects.All _ (if (!chunk_mask &&& chunk_mask == 0#32) = true then _ else _)
  rw [h_and_self]
  by_cases h_zero : (chunk_mask == 0#32) = true
  · simp only [h_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 29) (by rw [h_prog_len]; omega) ?_
    -- Directive 29: addq $32, temp_offset
    sstep
    simp only [hd_offset_mask, ↓reduceIte, hoff]
    rw [← BitVec.ofNat_add]
    refine Program.loopCont_of_le (j := 30) (by rw [h_prog_len]; omega) ?_
    -- Directive 30: subl $32, %ecx
    sstep
    have h_rcx_toff : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
    have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
    have h_rcx_mask : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    simp only [h_rcx_toff, h_toff_rcx, h_rcx_mask, get64_set64, Bool.false_eq_true, ↓reduceIte, hrcx]
    have h32 : (32#32 : BitVec 32) = BitVec.ofNat 32 32 := rfl
    rw [h32, ofNat32_sub_lit (show 32 ≤ r by omega)]
    refine Program.loopCont_of_le (j := 31) (by rw [h_prog_len]; omega) ?_
    -- Directive 31: cmpl $32, %ecx
    sstep
    refine Program.loopCont_of_le (j := 32) (by rw [h_prog_len]; omega) ?_
    -- Directive 32: jae compressed_avx_loop
    sstep
    have hr_sub_lt : r - 32 < 2 ^ 32 := by omega
    have h32 : (32#32 : BitVec 32) = BitVec.ofNat 32 32 := rfl
    simp only [h32, cf_ofNat32 (x := r - 32) (c := 32) hr_sub_lt (by decide)]
    have hpre_extended : ∀ (i : Nat) (hi : i < (k + 32) - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
      intro i hi
      by_cases hi_old : i < k - from_k
      · exact hpre i hi_old
      · have hj : i - (k - from_k) < 32 := by omega
        have h_step := compressed_avx_pre_step s A T d h_data ch h_ch chars h_len h_chars from_k t ymm_target h_target k (by omega) h_from_k h_zero (i - (k - from_k)) hj
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨(k + (i - (k - from_k))) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext; dsimp only []; omega
        rw [hext]
        exact h_step
    by_cases hlt : r - 32 < 32
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 33) (by rw [h_prog_len]; omega) ?_
      have hT_sub : T - (r - 32) = k + 32 := by omega
      have h_from_k_le : from_k ≤ T - (r - 32) := by omega
      have hpre_tail_in : ∀ (i : Nat) (hi : i < T - (r - 32) - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        rw [hT_sub] at hi
        exact hpre_extended i hi
      exact compressed_tail_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct hlab H s c d A T hA hT hT32 h_data h_some ch h_ch chars h_len h_chars fromIndex from_k h_from_eq
        _ hm (by
          intro r' hr'
          have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            intro h_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
            rcases h_in with rfl | rfl | rfl | rfl | rfl
            · exact hr'.1 rfl
            · exact hr'.2.1 rfl
            · exact hr'.2.2.1 rfl
            · exact hr'.2.2.2.1 rfl
            · exact hr'.2.2.2.2 rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
          exact hr r' hr_not_in) (by
          obtain ⟨v2, hv⟩ := hz
          refine ⟨BitVec.broadcastb 256 (BitVec.setWidth 8 ch), ?_⟩
          refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
            (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
          rw [hv]
          dsimp only []
          exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))) ymm_match v2 _) (by
          simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (r - 32) hlt (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, hT_sub, Nat.add_comm])
        h_from_k_le hpre_tail_in (by
          obtain ⟨v2, hv⟩ := hz
          rw [hv, zmms_set_set]
          exact zmms_get_target s.zmms ymm_target ymm_match _ _ h_ymm_diff)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 24) rfl]
      refine Program.loopCont_of_le (j := 24) (by rw [h_prog_len]; omega) ?_
      refine ih (r - 32) (by omega) (k + 32) _ hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
        rw [hv, zmms_set_set]) (by
        simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, Nat.add_comm])
        (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by omega) (by omega) (by omega) hpre_extended
  · simp only [h_zero, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 48) rfl]
    refine Program.loopCont_of_le (j := 48) (by rw [h_prog_len]; omega) ?_
    let idx := BitVec.setWidth 32 (.ofNat 64 k + (BitVec.bsf chunk_mask).zeroExtend 64)
    have h_mask_ne32 : chunk_mask ≠ 0#32 := by
      intro h
      simp [h] at h_zero
    have hspec_here : indexOfSpec chars ch fromIndex = idx := by
      have h_chunk_mask_eq : chunk_mask = BitVec.pmovmskb (BitVec.pcmpeqb (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32))))) := by
        dsimp [chunk_mask]
        rw [h_target]
      exact compressed_avx_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq k (by omega) h_from_k hpre chunk_mask h_chunk_mask_eq h_mask_ne32
    exact ret_compressed_avx_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct hlab H s _ chars ch fromIndex idx hspec_here hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.broadcastb 256 (BitVec.setWidth 8 ch), ?_⟩
        refine ⟨BitVec.pcmpeqb (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (k + j)) (List.range 32)))), ?_⟩
        rw [hv]
        dsimp only []
        exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastb 256 (BitVec.setWidth 8 ch))) ymm_match v2 _) (by
        simp only [get64_set64, sw32_64, ite_true]
        exact h_mask_ne32) (by
        simp only [get64_set64, hd_offset_mask, ↓reduceIte, sw32_64, hoff]
        rfl)


theorem uncompressed_avx_loop_lemma [Host] (slow : Label)
    (str search_value out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT16 : 16 ≤ T)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ r k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : ∃ v2, t.zmms = (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))).set ymm_match v2)
      (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
      (hoff : t.regs.get64 temp_offset = .ofNat 64 k)
      (hrcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r)
      (hkr : k + r = T)
      (hr16 : 16 ≤ r)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 68)⟩ := by
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match).length = 117 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t hm hr hz h_len_reg hoff hrcx hkr hr16 h_from_k hpre
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  have haddr : A + 16#64 + 2#64 * .ofNat 64 k = A + 2#64 * .ofNat 64 k + 16#64 := by ac_rfl
  have h_scale : 2#64 * (BitVec.ofNat 64 k) = BitVec.ofNat 64 (2 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mul_comm]
  have hload : t.dmem.loadInt (A + 16#64 + 2#64 * .ofNat 64 k) 32 =
      some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (2 * k + j))) := by
    rw [haddr, h_scale, hm]
    exact load_chunk _ _ (2 * k) 32 (2 * T) h_some (by omega)
  have h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16) := by
    obtain ⟨v2, hv⟩ := hz
    rw [hv]
    exact zmms_get_target s.zmms ymm_target ymm_match (BitVec.broadcastw 256 (ch.setWidth 16)) v2 h_ymm_diff
  -- Directive 68: .label "uncompressed_avx_loop"
  sstep
  refine Program.loopCont_of_le (j := 69) (by rw [h_prog_len]; omega) ?_
  -- Directive 69: vpcmpeqw 16(str, temp_offset, 2), ymm_target, ymm_match
  sstep
  have h_addr := addr_sib2_disp' t.regs str temp_offset 16 (Host.addrOf (H.start + 69)...Host.addrOf (H.start + 70))
  rw [h_addr]
  simp only [ofInt_signed_mul2, ofNat_mul2, hstr, hoff]
  have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
  rw [this]
  have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + 2#64 * BitVec.ofNat 64 k := by
    rw [h_scale]
    ac_rfl
  rw [h_addr_match, hload]
  dsimp only []
  refine Program.loopCont_of_le (j := 70) (by rw [h_prog_len]; omega) ?_
  -- Directive 70: vpmovmskb ymm_match, temp_mask
  sstep
  refine Program.loopCont_of_le (j := 71) (by rw [h_prog_len]; omega) ?_
  -- Directive 71: testl temp_mask, temp_mask
  sstep
  intro _
  refine Program.loopCont_of_le (j := 72) (by rw [h_prog_len]; omega) ?_
  -- Directive 72: jnz uncompressed_match_found
  sstep
  let chunk_mask := (BitVec.pcmpeqw (t.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32))))).pmovmskb
  have h_and_self := bv_and_self_zero chunk_mask
  change Effects.All _ (if (!chunk_mask &&& chunk_mask == 0#32) = true then _ else _)
  rw [h_and_self]
  by_cases h_zero : (chunk_mask == 0#32) = true
  · simp only [h_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 73) (by rw [h_prog_len]; omega) ?_
    -- Directive 73: addq $16, temp_offset
    sstep
    simp only [hd_offset_mask, ↓reduceIte, hoff]
    rw [← BitVec.ofNat_add]
    refine Program.loopCont_of_le (j := 74) (by rw [h_prog_len]; omega) ?_
    -- Directive 74: subl $16, %ecx
    sstep
    have h_rcx_toff : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
    have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
    have h_rcx_mask : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    simp only [h_rcx_toff, h_toff_rcx, h_rcx_mask, get64_set64, Bool.false_eq_true, ↓reduceIte, hrcx]
    have h16 : (16#32 : BitVec 32) = BitVec.ofNat 32 16 := rfl
    rw [h16, ofNat32_sub_lit (show 16 ≤ r by omega)]
    refine Program.loopCont_of_le (j := 75) (by rw [h_prog_len]; omega) ?_
    -- Directive 75: cmpl $16, %ecx
    sstep
    refine Program.loopCont_of_le (j := 76) (by rw [h_prog_len]; omega) ?_
    -- Directive 76: jae uncompressed_avx_loop
    sstep
    have hr_sub_lt : r - 16 < 2 ^ 32 := by omega
    have h16 : (16#32 : BitVec 32) = BitVec.ofNat 32 16 := rfl
    simp only [h16, cf_ofNat32 (x := r - 16) (c := 16) hr_sub_lt (by decide)]
    have hpre_extended : ∀ (i : Nat) (hi : i < (k + 16) - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
      intro i hi
      by_cases hi_old : i < k - from_k
      · exact hpre i hi_old
      · have hj : i - (k - from_k) < 16 := by omega
        have h_step := uncompressed_avx_pre_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex k (by omega) h_from_k (by
          rw [← h_target]
          exact h_zero) (i - (k - from_k)) hj
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨(k + (i - (k - from_k))) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext; dsimp only []; omega
        rw [hext]
        exact h_step
    by_cases hlt : r - 16 < 16
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 77) (by rw [h_prog_len]; omega) ?_
      have hT_sub : T - (r - 16) = k + 16 := by omega
      have h_from_k_le : from_k ≤ T - (r - 16) := by omega
      have hpre_tail_in : ∀ (i : Nat) (hi : i < T - (r - 16) - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        rw [hT_sub] at hi
        exact hpre_extended i hi
      exact uncompressed_tail_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct hlab H s c d A T hA hT (by omega) h_data h_some ch h_ch chars h_len h_chars fromIndex from_k h_from_eq
        _ hm (by
          intro r' hr'
          have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            intro h_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
            rcases h_in with rfl | rfl | rfl | rfl | rfl
            · exact hr'.1 rfl
            · exact hr'.2.1 rfl
            · exact hr'.2.2.1 rfl
            · exact hr'.2.2.2.1 rfl
            · exact hr'.2.2.2.2 rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
          exact hr r' hr_not_in) (by
          obtain ⟨v2, hv⟩ := hz
          refine ⟨BitVec.broadcastw 256 (ch.setWidth 16), ?_⟩
          refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
            (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
          rw [hv]
          dsimp only []
          exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))) ymm_match v2 _) (by
          simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (r - 16) hlt (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, hT_sub, Nat.add_comm])
        h_from_k_le hpre_tail_in (by
          obtain ⟨v2, hv⟩ := hz
          rw [hv, zmms_set_set]
          exact zmms_get_target s.zmms ymm_target ymm_match _ _ h_ymm_diff)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 68) rfl]
      refine Program.loopCont_of_le (j := 68) (by rw [h_prog_len]; omega) ?_
      refine ih (r - 16) (by omega) (k + 16) _ hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
        rw [hv, zmms_set_set]) (by
        simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, Nat.add_comm])
        (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by omega) (by omega) (by omega) hpre_extended
  · simp only [h_zero, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 94) rfl]
    refine Program.loopCont_of_le (j := 94) (by rw [h_prog_len]; omega) ?_
    let idx := BitVec.setWidth 32 (.ofNat 64 k + ((BitVec.bsf chunk_mask) >>> 1).zeroExtend 64)
    have h_mask_ne32 : chunk_mask ≠ 0#32 := by
      intro h
      simp [h] at h_zero
    have hspec_here : indexOfSpec chars ch fromIndex = idx := by
      have h_chunk_mask_eq : chunk_mask = BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32))))) := by
        dsimp [chunk_mask]
        rw [h_target]
      exact uncompressed_avx_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq k (by omega) h_from_k hpre chunk_mask h_chunk_mask_eq h_mask_ne32
    exact ret_uncompressed_avx_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct hlab H s _ chars ch fromIndex idx hspec_here hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.broadcastw 256 (ch.setWidth 16), ?_⟩
        refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
        rw [hv]
        dsimp only []
        exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))) ymm_match v2 _) (by
        simp only [get64_set64, sw32_64, ite_true]
        exact h_mask_ne32) (by
        simp only [get64_set64, hd_offset_mask, ↓reduceIte, sw32_64, hoff]
        rfl)


theorem uncompressed_avx_loop_lemma_after [Host] (slow : Label)
    (str search_value start_idx out temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (hlab : LabelsPlaced)
    (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match))
    (s : MachineData)
    (c : BitVec 32) (d : List UInt8)
    (A : BitVec 64) (T : Nat)
    (hA : A = s.regs.get64 str)
    (hT : T = (c >>> 1).toNat)
    (hT16 : 16 ≤ T)
    (h_data : ∀ i < 2 * T, byteAt s.dmem A i = d.getD i 0)
    (h_some : ∀ i < 2 * T, (s.dmem[A + 16#64 + .ofNat 64 i]?).isSome)
    (ch : BitVec 32) (h_ch : ch.toNat ≤ 65535)
    (chars : List (BitVec 16))
    (h_len : chars.length = T)
    (h_chars : ∀ (i : Nat) (hi : i < T), (chars.get ⟨i, by omega⟩).zeroExtend 32 =
      ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
        ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32)
    (fromIndex : BitVec 32) (from_k : Nat)
    (h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k) :
    ∀ r k (t : MachineData)
      (hm : t.dmem = s.dmem)
      (hr : ∀ r, r ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] → t.regs.get64 r = s.regs.get64 r)
      (hz : ∃ v2, t.zmms = (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))).set ymm_match v2)
      (h_len_reg : t.regs.get64 temp_len = .ofNat 64 T)
      (hoff : t.regs.get64 temp_offset = .ofNat 64 k)
      (hrcx : (t.regs.get64 Reg64.rcx).setWidth 32 = .ofNat 32 r)
      (hkr : k + r = T)
      (hr16 : 16 ≤ r)
      (h_from_k : from_k ≤ k)
      (hpre : ∀ (i : Nat) (hi : i < k - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch),
      Program.Loop (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match) H
        (StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match chars ch fromIndex s)
        (StringIndexOfSlow slow ch s)
        ⟨t, Host.addrOf (H.start + 72)⟩ := by
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match).length = 121 := rfl
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro k t hm hr hz h_len_reg hoff hrcx hkr hr16 h_from_k hpre
  have hstr : t.regs.get64 str = A := by
    rw [hA]
    exact hr str (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hd_str_out rfl
      · exact hd_str_rcx rfl
      · exact hd_str_len rfl
      · exact hd_str_offset rfl
      · exact hd_str_mask rfl)
  have haddr : A + 16#64 + 2#64 * .ofNat 64 k = A + 2#64 * .ofNat 64 k + 16#64 := by ac_rfl
  have h_scale : 2#64 * (BitVec.ofNat 64 k) = BitVec.ofNat 64 (2 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mul_comm]
  have hload : t.dmem.loadInt (A + 16#64 + 2#64 * .ofNat 64 k) 32 =
      some (Int.ofBytes ((List.range 32).map fun j => byteAt s.dmem A (2 * k + j))) := by
    rw [haddr, h_scale, hm]
    exact load_chunk _ _ (2 * k) 32 (2 * T) h_some (by omega)
  have h_target : t.zmms.get ymm_target = BitVec.broadcastw 256 (ch.setWidth 16) := by
    obtain ⟨v2, hv⟩ := hz
    rw [hv]
    exact zmms_get_target s.zmms ymm_target ymm_match (BitVec.broadcastw 256 (ch.setWidth 16)) v2 h_ymm_diff
  -- Directive 72: .label "uncompressed_avx_loop"
  sstep
  refine Program.loopCont_of_le (j := 73) (by rw [h_prog_len]; omega) ?_
  -- Directive 73: vpcmpeqw 16(str, temp_offset, 2), ymm_target, ymm_match
  sstep
  have h_addr := addr_sib2_disp' t.regs str temp_offset 16 (Host.addrOf (H.start + 73)...Host.addrOf (H.start + 74))
  rw [h_addr]
  simp only [ofInt_signed_mul2, ofNat_mul2, hstr, hoff]
  have : (Int64.toBitVec 16 : BitVec 64) = 16#64 := rfl
  rw [this]
  have h_addr_match : A + BitVec.ofNat 64 (2 * k) + 16#64 = A + 16#64 + 2#64 * BitVec.ofNat 64 k := by
    rw [h_scale]
    ac_rfl
  rw [h_addr_match, hload]
  dsimp only []
  refine Program.loopCont_of_le (j := 74) (by rw [h_prog_len]; omega) ?_
  -- Directive 74: vpmovmskb ymm_match, temp_mask
  sstep
  refine Program.loopCont_of_le (j := 75) (by rw [h_prog_len]; omega) ?_
  -- Directive 75: testl temp_mask, temp_mask
  sstep
  intro _
  refine Program.loopCont_of_le (j := 76) (by rw [h_prog_len]; omega) ?_
  -- Directive 76: jnz uncompressed_match_found
  sstep
  let chunk_mask := (BitVec.pcmpeqw (t.zmms.get ymm_target)
      (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32))))).pmovmskb
  have h_and_self := bv_and_self_zero chunk_mask
  change Effects.All _ (if (!chunk_mask &&& chunk_mask == 0#32) = true then _ else _)
  rw [h_and_self]
  by_cases h_zero : (chunk_mask == 0#32) = true
  · simp only [h_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 77) (by rw [h_prog_len]; omega) ?_
    -- Directive 77: addq $16, temp_offset
    sstep
    simp only [hd_offset_mask, ↓reduceIte, hoff]
    rw [← BitVec.ofNat_add]
    refine Program.loopCont_of_le (j := 78) (by rw [h_prog_len]; omega) ?_
    -- Directive 78: subl $16, %ecx
    sstep
    have h_rcx_toff : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
    have h_toff_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
    have h_rcx_mask : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
    simp only [h_rcx_toff, h_toff_rcx, h_rcx_mask, get64_set64, Bool.false_eq_true, ↓reduceIte, hrcx]
    have h16 : (16#32 : BitVec 32) = BitVec.ofNat 32 16 := rfl
    rw [h16, ofNat32_sub_lit (show 16 ≤ r by omega)]
    refine Program.loopCont_of_le (j := 79) (by rw [h_prog_len]; omega) ?_
    -- Directive 79: cmpl $16, %ecx
    sstep
    refine Program.loopCont_of_le (j := 80) (by rw [h_prog_len]; omega) ?_
    -- Directive 80: jae uncompressed_avx_loop
    sstep
    have hr_sub_lt : r - 16 < 2 ^ 32 := by omega
    have h16 : (16#32 : BitVec 32) = BitVec.ofNat 32 16 := rfl
    simp only [h16, cf_ofNat32 (x := r - 16) (c := 16) hr_sub_lt (by decide)]
    have hpre_extended : ∀ (i : Nat) (hi : i < (k + 16) - from_k),
        ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
      intro i hi
      by_cases hi_old : i < k - from_k
      · exact hpre i hi_old
      · have hj : i - (k - from_k) < 16 := by omega
        have h_step := uncompressed_avx_pre_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex k (by omega) h_from_k (by
          rw [← h_target]
          exact h_zero) (i - (k - from_k)) hj
        have hext : (⟨i, by rw [List.length_drop, h_len]; omega⟩ : Fin (chars.drop from_k).length) =
            ⟨(k + (i - (k - from_k))) - from_k, by rw [List.length_drop, h_len]; omega⟩ := by
          ext; dsimp only []; omega
        rw [hext]
        exact h_step
    by_cases hlt : r - 16 < 16
    · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 81) (by rw [h_prog_len]; omega) ?_
      have hT_sub : T - (r - 16) = k + 16 := by omega
      have h_from_k_le : from_k ≤ T - (r - 16) := by omega
      have hpre_tail_in : ∀ (i : Nat) (hi : i < T - (r - 16) - from_k),
          ((chars.drop from_k).get ⟨i, by rw [List.length_drop, h_len]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi
        rw [hT_sub] at hi
        exact hpre_extended i hi
      exact uncompressed_tail_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct hlab H s c d A T hA hT (by omega) h_data h_some ch h_ch chars h_len h_chars fromIndex from_k h_from_eq
        _ hm (by
          intro r' hr'
          have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            intro h_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
            rcases h_in with rfl | rfl | rfl | rfl | rfl
            · exact hr'.1 rfl
            · exact hr'.2.1 rfl
            · exact hr'.2.2.1 rfl
            · exact hr'.2.2.2.1 rfl
            · exact hr'.2.2.2.2 rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
          exact hr r' hr_not_in) (by
          obtain ⟨v2, hv⟩ := hz
          refine ⟨BitVec.broadcastw 256 (ch.setWidth 16), ?_⟩
          refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
            (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
          rw [hv]
          dsimp only []
          exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))) ymm_match v2 _) (by
          simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (r - 16) hlt (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, hT_sub, Nat.add_comm])
        h_from_k_le hpre_tail_in (by
          obtain ⟨v2, hv⟩ := hz
          rw [hv, zmms_set_set]
          exact zmms_get_target s.zmms ymm_target ymm_match _ _ h_ymm_diff)
    · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte,
        addrOf_label hlab (H := H) (i := 72) rfl]
      refine Program.loopCont_of_le (j := 72) (by rw [h_prog_len]; omega) ?_
      refine ih (r - 16) (by omega) (k + 16) _ hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.1, hr'.2.2.2.1, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
        rw [hv, zmms_set_set]) (by
        simp only [get64_set64, hd_len_mask, hd_len_offset, Ne.symm hd_rcx_len, ↓reduceIte, h_len_reg])
        (by simp only [get64_set64, h_toff_rcx, Bool.false_eq_true, ↓reduceIte, Nat.add_comm])
        (by simp only [get64_set64, sw32_64, ↓reduceIte])
        (by omega) (by omega) (by omega) hpre_extended
  · simp only [h_zero, Bool.not_false, ↓reduceIte, addrOf_label hlab (H := H) (i := 98) rfl]
    refine Program.loopCont_of_le (j := 98) (by rw [h_prog_len]; omega) ?_
    let idx := BitVec.setWidth 32 (.ofNat 64 k + ((BitVec.bsf chunk_mask) >>> 1).zeroExtend 64)
    have h_mask_ne32 : chunk_mask ≠ 0#32 := by
      intro h
      simp [h] at h_zero
    have hspec_here : indexOfSpec chars ch fromIndex = idx := by
      have h_chunk_mask_eq : chunk_mask = BitVec.pmovmskb (BitVec.pcmpeqw (BitVec.broadcastw 256 (ch.setWidth 16))
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32))))) := by
        dsimp [chunk_mask]
        rw [h_target]
      exact uncompressed_avx_match_step s A T d h_data ch h_ch chars h_len h_chars from_k fromIndex h_from_eq k (by omega) h_from_k hpre chunk_mask h_chunk_mask_eq h_mask_ne32
    exact ret_uncompressed_avx_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct hlab H s _ chars ch fromIndex idx hspec_here hm (by
        intro r' hr'
        have hr_not_in : r' ∉ [out, Reg64.rcx, temp_len, temp_offset, temp_mask] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          intro h_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h_in
          rcases h_in with rfl | rfl | rfl | rfl | rfl
          · exact hr'.1 rfl
          · exact hr'.2.1 rfl
          · exact hr'.2.2.1 rfl
          · exact hr'.2.2.2.1 rfl
          · exact hr'.2.2.2.2 rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp only [get64_set64, hr'.2.2.2.2, ↓reduceIte]
        exact hr r' hr_not_in) (by
        obtain ⟨v2, hv⟩ := hz
        refine ⟨BitVec.broadcastw 256 (ch.setWidth 16), ?_⟩
        refine ⟨BitVec.pcmpeqw (t.zmms.get ymm_target)
          (BitVec.ofInt 256 (Int.ofBytes (List.map (fun j => byteAt s.dmem A (2 * k + j)) (List.range 32)))), ?_⟩
        rw [hv]
        dsimp only []
        exact zmms_set_set (s.zmms.set ymm_target (BitVec.broadcastw 256 (ch.setWidth 16))) ymm_match v2 _) (by
        simp only [get64_set64, sw32_64, ite_true]
        exact h_mask_ne32) (by
        simp only [get64_set64, hd_offset_mask, ↓reduceIte, sw32_64, hoff]
        rfl)




theorem setWidth_ofNat (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp
  have : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt this]

theorem extractLsb_eq (ch : BitVec 32) :
    (BitVec.extractLsb' 0 8 (BitVec.setWidth 256 ch)) = BitVec.extractLsb' 0 8 (BitVec.setWidth 8 ch) := by
  bv_decide

theorem bcastb_eq (ch : BitVec 32) :
    BitVec.broadcastb 256 (BitVec.zeroExtend 256 ch) = BitVec.broadcastb 256 (BitVec.setWidth 8 ch) := by
  dsimp [BitVec.broadcastb, BitVec.lane]
  congr 1
  funext x
  exact extractLsb_eq ch

theorem extractLsb16_eq (ch : BitVec 32) :
    (BitVec.extractLsb' 0 16 (BitVec.setWidth 256 ch)) = BitVec.extractLsb' 0 16 (BitVec.setWidth 16 ch) := by
  bv_decide

theorem bcastw_eq (ch : BitVec 32) :
    BitVec.broadcastw 256 (BitVec.zeroExtend 256 ch) = BitVec.broadcastw 256 (BitVec.setWidth 16 ch) := by
  dsimp [BitVec.broadcastw, BitVec.lane]
  congr 1
  funext x
  exact extractLsb16_eq ch

theorem ofNat_sub32 (A B : Nat) (hBA : B ≤ A) (hA : A < 2 ^ 32) :
    BitVec.ofNat 32 A - BitVec.ofNat 32 B = BitVec.ofNat 32 (A - B) := by
  apply BitVec.eq_of_toNat_eq
  have hA_nat : (BitVec.ofNat 32 A).toNat = A := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
  have hB_nat : (BitVec.ofNat 32 B).toNat = B := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBA_bv : BitVec.ofNat 32 B ≤ BitVec.ofNat 32 A := by
    rw [BitVec.le_def, hA_nat, hB_nat]
    exact hBA
  rw [BitVec.toNat_sub_of_le hBA_bv, hA_nat, hB_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem cmovg32_eval (fromIndex : BitVec 32) :
    let v := fromIndex - 0#32
    let of := v.signed != fromIndex.signed - (0#32).signed
    let sf := v.msb
    let zf := v == 0#32
    let cond := !zf && (sf == of)
    (if cond then fromIndex else 0#32) = BitVec.ofNat 32 (if fromIndex.slt 0 then 0 else fromIndex.toNat) := by
  dsimp only [BitVec.signed]
  rw [cmovg_zero_eval]
  split
  · rfl
  · simp

theorem cmovg64_eval (fromIndex : BitVec 32) :
    let v := fromIndex - 0#32
    let of := v.signed != fromIndex.signed - (0#32).signed
    let sf := v.msb
    let zf := v == 0#32
    let cond := !zf && (sf == of)
    (BitVec.setWidth 64 (if cond then fromIndex else 0#32)) =
      BitVec.ofNat 64 (if fromIndex.slt 0 then 0 else fromIndex.toNat) := by
  dsimp only [BitVec.signed]
  rw [cmovg_zero_eval]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq; simp



theorem stringIndexOf_correct [Host] (slow : Label)
    (str search_value out : Reg64)
    (temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (hslow : ∀ (H : Embedding (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match)),
      IsSlowPathLabel (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match) H slow)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ (s.regs.get64 str).toNat + 16 < 2 ^ 32 ∧
        d.length = strByteLen c ∧
        (c.getLsbD 0 = false → ∀ b ∈ d, b < 0x80) ∧
        (c.getLsbD 0 = true → 0 < (c >>> 1).toNat) ∧
        ∃ R, (StringAt (s.regs.get64 str) c d ⋆ R) s.dmem ⦄
      (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match)
    ⦃ fun _ => StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match
          (strChars c d) (s₀.regs.get (Reg.low search_value Width.W32)) 0#32 s₀;
      fun pc s => StringIndexOfSlow slow (s₀.regs.get (Reg.low search_value Width.W32)) s₀ pc s ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hA32, hl, h_ascii, h_uncomp_pos, R, hmem⟩
  apply Program.wp_of_loop
  intro H
  have h_prog_len : (stringIndexOfProg slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match).length = 117 := rfl
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  let ch := BitVec.setWidth 32 (s.regs.get64 search_value)
  have hch_def : s.regs.get (Reg.low search_value Width.W32) = ch := by rw [get_low32]
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hd_mask_offset : (temp_mask = temp_offset) = false := by simp [Ne.symm hd_offset_mask]
  have hd_mask_len : (temp_mask = temp_len) = false := by simp [Ne.symm hd_len_mask]
  have hd_mask_rcx : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
  have hd_offset_mask' : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
  have hd_offset_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
  have hd_offset_len : (temp_offset = temp_len) = false := by simp [Ne.symm hd_len_offset]
  have hd_rcx_len_ne : (Reg64.rcx = temp_len) = false := by simp [hd_rcx_len]
  have hd_rcx_offset_ne : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
  have hd_rcx_mask_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
  have hd_len_offset' : (temp_len = temp_offset) = false := by simp [hd_len_offset]
  have hd_len_mask' : (temp_len = temp_mask) = false := by simp [hd_len_mask]
  have hd_len_rcx' : (temp_len = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_len]
  have hd_search_mask_ne : (search_value = temp_mask) = false := by simp [hd_search_mask]
  have hd_search_len_ne : (search_value = temp_len) = false := by simp [hd_search_len]
  have hd_search_offset_ne : (search_value = temp_offset) = false := by simp [hd_search_offset]
  have hd_search_rcx_ne : (search_value = Reg64.rcx) = false := by simp [hd_search_rcx]
  by_cases h_ch : ch.toNat > 65535
  · have hch_gt : ch.toNat > 65535 := h_ch
    have h_post : (s.regs.get (Reg.low search_value Width.W32)) = ch := hch_def
    rw [h_post]
    exact ret_slow slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      (strChars c d) 0#32 H s s ch hch_gt hch_def rfl rfl rfl (hslow H)
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
  -- Directive 0: cmp search_value, bashxFFFF
  sstep
  refine Program.loopCont_of_le (j := 1) (by rw [h_prog_len]; omega) ?_
  -- Directive 1: ja slow
  sstep
  have h_ch_subst : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
  rw [h_ch_subst, h_ja]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 2) (by rw [h_prog_len]; omega) ?_
  -- Directive 2: movl 8(str), temp_len
  have cA := fun i (hi : i < 4) => sep_get_l hmem (stringAt_cnt (i := i) hi)
  sstep
  rw [load_count s.dmem (s.regs.get64 str) c cA]
  simp only [cnt_val]
  refine Program.loopCont_of_le (j := 3) (by rw [h_prog_len]; omega) ?_
  -- Directive 3: testl temp_len, temp_len
  sstep
  intro _
  refine Program.loopCont_of_le (j := 4) (by rw [h_prog_len]; omega) ?_
  -- Directive 4: je not_found
  sstep
  have h_and_self : (c &&& c == 0#32) = (c == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hc0 : c = 0#32
  · rw [hc0, beq_self_eq_true]
    simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 114) rfl]
    refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
    have hd_nil : d = [] := by
      have : d.length = 0 := by rw [hl, hc0]; rfl
      exact List.eq_nil_of_length_eq_zero this
    have hchars_nil : strChars (0#32) d = [] := by
      unfold strChars; rw [hd_nil]; rfl
    have hspec : indexOfSpec (strChars (0#32) d) ch 0#32 = -1#32 := by
      rw [hchars_nil, indexOfSpec_empty]
    exact ret_not_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ (strChars (0#32) d) ch 0#32 hspec rfl (by
        intro r hr_out
        simp only [get64_set64]
        by_cases h1 : r = temp_len
        · subst h1; simp at hr_out
        · simp [h1]) (Or.inl rfl)
  · rw [beq_eq_false_iff_ne.mpr hc0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 5) (by rw [h_prog_len]; omega) ?_
    -- Directive 5: movl temp_len, temp_mask
    sstep
    refine Program.loopCont_of_le (j := 6) (by rw [h_prog_len]; omega) ?_
    -- Directive 6: shrl , temp_len
    sstep
    intro af
    simp only [↓reduceIte, beq_self_eq_true, Bool.false_eq_true]
    refine Program.loopCont_of_le (j := 7) (by rw [h_prog_len]; omega) ?_
    -- Directive 7: xorq temp_offset, temp_offset
    sstep
    intro _
    refine Program.loopCont_of_le (j := 8) (by rw [h_prog_len]; omega) ?_
    -- Directive 8: movl temp_len, %ecx
    sstep
    refine Program.loopCont_of_le (j := 9) (by rw [h_prog_len]; omega) ?_
    -- Directive 9: subl temp_offset, %ecx
    sstep
    refine Program.loopCont_of_le (j := 10) (by rw [h_prog_len]; omega) ?_
    -- Directive 10: testl , temp_mask
    sstep
    intro _
    refine Program.loopCont_of_le (j := 11) (by rw [h_prog_len]; omega) ?_
    -- Directive 11: jnz uncompressed_path
    sstep
    simp only [hd_mask_rcx, hd_mask_offset, hd_mask_len, Bool.false_eq_true, ↓reduceIte, sw32_64, lsb_and1 c, Bool.not_not]
    by_cases h_comp : c.getLsbD 0 = false
    · rw [h_comp]
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 12) (by rw [h_prog_len]; omega) ?_
      -- Directive 12: cmpl 27, search_value
      sstep
      simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 13) (by rw [h_prog_len]; omega) ?_
      -- Directive 13: jg not_found
      sstep
      by_cases h_ch127 : ch.toNat > 127
      · rw [jg_ch127_true h_ch127 h_ch_le]
        simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 114) rfl]
        refine Program.loopCont_of_le (j := 114) (by rw [h_prog_len]; omega) ?_
        have h_ascii' := strChars_compressed_ascii h_comp hl (h_ascii h_comp)
        have hspec : indexOfSpec (strChars c d) ch 0#32 = -1#32 :=
          indexOfSpec_compressed_gt127 h_ascii' h_ch127
        exact ret_not_found slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct H s _ (strChars c d) ch 0#32 hspec rfl (by
            intro r hr_out
            simp only [get64_set64]
            by_cases h1 : r = Reg64.rcx
            · subst h1; simp at hr_out
            · by_cases h2 : r = temp_offset
              · subst h2; simp at hr_out
              · by_cases h3 : r = temp_len
                · subst h3; simp at hr_out
                · by_cases h4 : r = temp_mask
                  · subst h4; simp at hr_out
                  · simp [h1, h2, h3, h4]) (Or.inl rfl)
      · have h_ch127_le : ch.toNat ≤ 127 := by omega
        rw [jg_ch127_false h_ch127_le]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 14) (by rw [h_prog_len]; omega) ?_
        -- Directive 14: cmpl 2, temp_len
        sstep
        refine Program.loopCont_of_le (j := 15) (by rw [h_prog_len]; omega) ?_
        -- Directive 15: jb compressed_scalar_loop
        sstep
        simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
        have h_eq : c.ushiftRight 1 = BitVec.ofNat 32 (c >>> 1).toNat := by
          apply BitVec.eq_of_toNat_eq
          simp
          rw [Nat.mod_eq_of_lt (by have := c.isLt; omega)]
        have h_cf : (BitVec.unsigned (c.ushiftRight 1 - 32#32) != (c.ushiftRight 1).unsigned - (32#32).unsigned) =
            decide ((c >>> 1).toNat < 32) := by
          conv => lhs; rw [h_eq]
          exact cf_ofNat32 (x := (c >>> 1).toNat) (c := 32) (c >>> 1).isLt (by decide)
        by_cases hT32 : (c >>> 1).toNat < 32
        · rw [h_cf, decide_eq_true_iff.mpr hT32]
          simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 50) rfl]
          refine Program.loopCont_of_le (j := 50) (by rw [h_prog_len]; omega) ?_
          have hinfo := string_info_of hmem hl
          have h_byte_len : strByteLen c = (c >>> 1).toNat := by
            unfold strByteLen; rw [h_comp]; simp
          have h_some : ∀ i < (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
            intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
          have h_data : ∀ i < (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
            intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
          have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
          have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
              ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32 := by
            intro i hi
            rw [strChars_compressed_get h_comp i hi]
            bv_decide
          have h_pos : 0 < (c >>> 1).toNat := pos_of_comp c hc0 h_comp
          let m := (c >>> 1).toNat - 1
          have hm1 : m + 1 = (c >>> 1).toNat := by omega
          refine compressed_scalar_loop_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
            h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl h_data h_some ch h_ch127_le
            (strChars c d) h_len_eq h_chars 0#32 0 rfl m 0 _ rfl ?_ (Or.inl rfl) ?_ ?_ ?_ (by omega) (by omega) (by intro i hi; omega)
          · intro r' hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
            simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
          · simp only [get_low32, get64_set64, hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, ↓reduceIte]
          · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
              Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
            have : c.ushiftRight 1 - 0#32 = c.ushiftRight 1 := by bv_decide
            rw [this, h_eq, hm1]
        · rw [h_cf, decide_eq_false_iff_not.mpr hT32]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Program.loopCont_of_le (j := 16) (by rw [h_prog_len]; omega) ?_
          -- Directive 16: vmovd search_value, ymm_match
          sstep
          refine Program.loopCont_of_le (j := 17) (by rw [h_prog_len]; omega) ?_
          -- Directive 17: vpbroadcastb ymm_match, ymm_target
          sstep
          refine Program.loopCont_of_le (j := 18) (by rw [h_prog_len]; omega) ?_
          -- Directive 18: cmpl 2, %ecx
          sstep
          refine Program.loopCont_of_le (j := 19) (by rw [h_prog_len]; omega) ?_
          -- Directive 19: jb compressed_tail
          sstep
          simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
            hd_len_rcx', hd_len_offset', hd_len_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          have : c.ushiftRight 1 - 0#32 = c.ushiftRight 1 := by bv_decide
          rw [this, h_cf, decide_eq_false_iff_not.mpr hT32]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Program.loopCont_of_le (j := 20) (by rw [h_prog_len]; omega) ?_
          have hinfo := string_info_of hmem hl
          have h_byte_len : strByteLen c = (c >>> 1).toNat := by
            unfold strByteLen; rw [h_comp]; simp
          have h_some : ∀ i < (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
            intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
          have h_data : ∀ i < (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
            intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
          have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
          have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
              ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32 := by
            intro i hi
            rw [strChars_compressed_get h_comp i hi]
            bv_decide
          have hT32_le : 32 ≤ (c >>> 1).toNat := by omega
          refine compressed_avx_loop_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
            h_distinct h_ymm_diff hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT32_le h_data h_some ch h_ch127_le
            (strChars c d) h_len_eq h_chars 0#32 0 rfl
            ((c >>> 1).toNat) 0 _ rfl ?hr ?hz ?hlen ?hoff ?hrcx (by omega) hT32_le (by omega) (by intro i hi; omega)
          · intro r' hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
            simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
          · refine ⟨BitVec.zeroExtend 256 ch, ?_⟩
            dsimp only []
            simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
            have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
            rw [hch_sub, bcastb_eq]
            exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) (Ne.symm h_ymm_diff)
          · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
            rw [h_eq, setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt]
          · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, ↓reduceIte]
          · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
              Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
            exact h_eq
    · have h_uncomp : c.getLsbD 0 = true := by
        revert h_comp
        cases c.getLsbD 0 <;> decide
      rw [h_uncomp]
      simp only [Bool.not_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 61) rfl]
      refine Program.loopCont_of_le (j := 61) (by rw [h_prog_len]; omega) ?_
      -- Directive 61: .label uncompressed_path
      sstep
      refine Program.loopCont_of_le (j := 62) (by rw [h_prog_len]; omega) ?_
      -- Directive 62: cmpl 6, temp_len
      sstep
      refine Program.loopCont_of_le (j := 63) (by rw [h_prog_len]; omega) ?_
      -- Directive 63: jb uncompressed_scalar_loop
      sstep
      simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
      have h_eq : c.ushiftRight 1 = BitVec.ofNat 32 (c >>> 1).toNat := by
        apply BitVec.eq_of_toNat_eq
        simp
        rw [Nat.mod_eq_of_lt (by have := c.isLt; omega)]
      have h_cf : (BitVec.unsigned (c.ushiftRight 1 - 16#32) != (c.ushiftRight 1).unsigned - (16#32).unsigned) =
          decide ((c >>> 1).toNat < 16) := by
        conv => lhs; rw [h_eq]
        exact cf_ofNat32 (x := (c >>> 1).toNat) (c := 16) (c >>> 1).isLt (by decide)
      by_cases hT16 : (c >>> 1).toNat < 16
      · rw [h_cf, decide_eq_true_iff.mpr hT16]
        simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 101) rfl]
        refine Program.loopCont_of_le (j := 101) (by rw [h_prog_len]; omega) ?_
        have hinfo := string_info_of hmem hl
        have h_byte_len : strByteLen c = 2 * (c >>> 1).toNat := by
          unfold strByteLen; rw [h_uncomp]; simp
        have h_some : ∀ i < 2 * (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
        have h_data : ∀ i < 2 * (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
        have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
        have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
            ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 =
              ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
                ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
          intro i hi
          exact congrArg (BitVec.zeroExtend 32) (strChars_uncompressed_get h_uncomp i hi)
        have h_pos : 0 < (c >>> 1).toNat := h_uncomp_pos h_uncomp
        let m := (c >>> 1).toNat - 1
        have hm1 : m + 1 = (c >>> 1).toNat := by omega
        refine uncompressed_scalar_loop_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl h_data h_some ch h_ch_le
          (strChars c d) h_len_eq h_chars 0#32 0 rfl m 0 _ rfl ?_ (Or.inl rfl) ?_ ?_ ?_ (by omega) (by omega) (by intro i hi; omega)
        · intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
          simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
        · simp only [get_low32, get64_set64, hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]; rfl
        · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, ↓reduceIte]
        · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          have : c.ushiftRight 1 - 0#32 = c.ushiftRight 1 := by bv_decide
          rw [this, h_eq, hm1]
      · rw [h_cf, decide_eq_false_iff_not.mpr hT16]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 64) (by rw [h_prog_len]; omega) ?_
        -- Directive 64: vmovd search_value, ymm_match
        sstep
        refine Program.loopCont_of_le (j := 65) (by rw [h_prog_len]; omega) ?_
        -- Directive 65: vpbroadcastw ymm_match, ymm_target
        sstep
        refine Program.loopCont_of_le (j := 66) (by rw [h_prog_len]; omega) ?_
        -- Directive 66: cmpl 6, %ecx
        sstep
        refine Program.loopCont_of_le (j := 67) (by rw [h_prog_len]; omega) ?_
        -- Directive 67: jb uncompressed_tail
        sstep
        simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
          hd_len_rcx', hd_len_offset', hd_len_mask',
          Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
        have : c.ushiftRight 1 - 0#32 = c.ushiftRight 1 := by bv_decide
        rw [this, h_cf, decide_eq_false_iff_not.mpr hT16]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 68) (by rw [h_prog_len]; omega) ?_
        have hinfo := string_info_of hmem hl
        have h_byte_len : strByteLen c = 2 * (c >>> 1).toNat := by
          unfold strByteLen; rw [h_uncomp]; simp
        have h_some : ∀ i < 2 * (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
        have h_data : ∀ i < 2 * (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
        have h_len_eq : (strChars c d).length = (c >>> 1).toNat := strChars_length c d
        have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
            ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 =
              ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
                ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
          intro i hi
          exact congrArg (BitVec.zeroExtend 32) (strChars_uncompressed_get h_uncomp i hi)
        have hT16_le : 16 ≤ (c >>> 1).toNat := by omega
        refine uncompressed_avx_loop_lemma slow str search_value out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct h_ymm_diff hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT16_le h_data h_some ch h_ch_le
          (strChars c d) h_len_eq h_chars 0#32 0 rfl
          ((c >>> 1).toNat) 0 _ rfl ?_ ?_ ?_ ?_ ?_ (by omega) hT16_le (by omega) (by intro i hi; omega)
        · intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
          simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
        · refine ⟨BitVec.zeroExtend 256 ch, ?_⟩
          dsimp only []
          simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
          have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
          rw [hch_sub, bcastw_eq]
          exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastw 256 (BitVec.setWidth 16 ch)) (Ne.symm h_ymm_diff)
        · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
          rw [h_eq, setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt]
        · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, ↓reduceIte]
        · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          exact h_eq

theorem stringIndexOfAfter_correct [Host] (slow : Label)
    (str search_value start_idx out : Reg64)
    (temp_len temp_offset temp_mask : Reg64)
    (ymm_target ymm_match : AvxReg .W256)
    (h_distinct : [str, search_value, start_idx, out, Reg64.rcx, temp_len, temp_offset, temp_mask].Nodup)
    (h_ymm_diff : ymm_target ≠ ymm_match)
    (c : BitVec 32) (d : List UInt8)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    (hslow : ∀ (H : Embedding (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match)),
      IsSlowPathLabel (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match) H slow)
    (s₀ : MachineData) :
    ⦃ fun s => s = s₀ ∧ (s.regs.get64 str).toNat + 16 < 2 ^ 32 ∧
        d.length = strByteLen c ∧
        (c.getLsbD 0 = false → ∀ b ∈ d, b < 0x80) ∧
        (c.getLsbD 0 = true → 0 < (c >>> 1).toNat) ∧
        ∃ R, (StringAt (s.regs.get64 str) c d ⋆ R) s.dmem ⦄
      (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match)
    ⦃ fun _ => StringIndexOfPost out [Reg64.rcx, temp_len, temp_offset, temp_mask] ymm_target ymm_match
          (strChars c d) (s₀.regs.get (Reg.low search_value Width.W32)) (s₀.regs.get (Reg.low start_idx Width.W32)) s₀;
      fun pc s => StringIndexOfSlow slow (s₀.regs.get (Reg.low search_value Width.W32)) s₀ pc s ⦄ := by
  rw [Program.triple_iff]
  rintro s ⟨rfl, hA32, hl, h_ascii, h_uncomp_pos, R, hmem⟩
  apply Program.wp_of_loop
  intro H
  have h_prog_len : (stringIndexOfAfterProg slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match).length = 121 := rfl
  change Program.Loop _ H _ _ ⟨s, Host.addrOf (H.start + 0)⟩
  let ch := BitVec.setWidth 32 (s.regs.get64 search_value)
  let fromIndex := BitVec.setWidth 32 (s.regs.get64 start_idx)
  have hch_def : s.regs.get (Reg.low search_value Width.W32) = ch := by rw [get_low32]
  have hfrom_def : s.regs.get (Reg.low start_idx Width.W32) = fromIndex := by rw [get_low32]
  rw [hch_def, hfrom_def]
  have hd := h_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hd_str_search, hd_str_start, hd_str_out, hd_str_rcx, hd_str_len, hd_str_offset, hd_str_mask⟩,
          ⟨hd_search_start, hd_search_out, hd_search_rcx, hd_search_len, hd_search_offset, hd_search_mask⟩,
          ⟨hd_start_out, hd_start_rcx, hd_start_len, hd_start_offset, hd_start_mask⟩,
          ⟨hd_out_rcx, hd_out_len, hd_out_offset, hd_out_mask⟩,
          ⟨hd_rcx_len, hd_rcx_offset, hd_rcx_mask⟩,
          ⟨hd_len_offset, hd_len_mask⟩,
          hd_offset_mask, -⟩ := hd
  have hd_start_len : start_idx ≠ temp_len := hd_start_len
  have hd_start_mask : start_idx ≠ temp_mask := hd_start_mask
  have hd_start_offset : start_idx ≠ temp_offset := hd_start_offset
  have hd_start_rcx : start_idx ≠ Reg64.rcx := hd_start_rcx
  have hd_len_mask : temp_len ≠ temp_mask := hd_len_mask
  have hd_mask_offset : (temp_mask = temp_offset) = false := by simp [Ne.symm hd_offset_mask]
  have hd_mask_len : (temp_mask = temp_len) = false := by simp [Ne.symm hd_len_mask]
  have hd_mask_rcx : (temp_mask = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_mask]
  have hd_offset_mask' : (temp_offset = temp_mask) = false := by simp [hd_offset_mask]
  have hd_offset_rcx : (temp_offset = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_offset]
  have hd_offset_len : (temp_offset = temp_len) = false := by simp [Ne.symm hd_len_offset]
  have hd_rcx_len_ne : (Reg64.rcx = temp_len) = false := by simp [hd_rcx_len]
  have hd_rcx_offset_ne : (Reg64.rcx = temp_offset) = false := by simp [hd_rcx_offset]
  have hd_rcx_mask_ne : (Reg64.rcx = temp_mask) = false := by simp [hd_rcx_mask]
  have hd_len_offset' : (temp_len = temp_offset) = false := by simp [hd_len_offset]
  have hd_len_mask' : (temp_len = temp_mask) = false := by simp [hd_len_mask]
  have hd_len_rcx' : (temp_len = Reg64.rcx) = false := by simp [Ne.symm hd_rcx_len]
  have hd_search_mask_ne : (search_value = temp_mask) = false := by simp [hd_search_mask]
  have hd_search_len_ne : (search_value = temp_len) = false := by simp [hd_search_len]
  have hd_search_offset_ne : (search_value = temp_offset) = false := by simp [hd_search_offset]
  have hd_search_rcx_ne : (search_value = Reg64.rcx) = false := by simp [hd_search_rcx]
  by_cases h_ch : ch.toNat > 65535
  · have hch_gt : ch.toNat > 65535 := h_ch
    exact ret_slow_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      (strChars c d) fromIndex H s s ch hch_gt hch_def rfl rfl rfl (hslow H)
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
  have h_ch_subst : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
  rw [h_ch_subst, h_ja]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 2) (by rw [h_prog_len]; omega) ?_
  -- Directive 2: movl 8(str), temp_len
  have cA := fun i (hi : i < 4) => sep_get_l hmem (stringAt_cnt (i := i) hi)
  sstep
  rw [load_count s.dmem (s.regs.get64 str) c cA]
  simp only [cnt_val]
  refine Program.loopCont_of_le (j := 3) (by rw [h_prog_len]; omega) ?_
  -- Directive 3: testl temp_len, temp_len
  sstep
  intro _
  refine Program.loopCont_of_le (j := 4) (by rw [h_prog_len]; omega) ?_
  -- Directive 4: je not_found
  sstep
  have h_and_self : (c &&& c == 0#32) = (c == 0#32) := by simp [BitVec.and_self]
  rw [h_and_self]
  by_cases hc0 : c = 0#32
  · rw [hc0, beq_self_eq_true]
    simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 118) rfl]
    refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
    have hd_nil : d = [] := by
      have : d.length = 0 := by rw [hl, hc0]; rfl
      exact List.eq_nil_of_length_eq_zero this
    have hchars_nil : strChars (0#32) d = [] := by
      unfold strChars; rw [hd_nil]; rfl
    have hspec : indexOfSpec (strChars (0#32) d) ch fromIndex = -1#32 := by
      rw [hchars_nil, indexOfSpec_empty]
    exact ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ (strChars (0#32) d) ch fromIndex hspec rfl (by
        intro r hr_out
        simp only [get64_set64]
        by_cases h1 : r = temp_len
        · subst h1; simp at hr_out
        · simp [h1]) (Or.inl rfl)
  rw [beq_eq_false_iff_ne.mpr hc0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 5) (by rw [h_prog_len]; omega) ?_
  -- Directive 5: movl temp_len, temp_mask
  sstep
  refine Program.loopCont_of_le (j := 6) (by rw [h_prog_len]; omega) ?_
  -- Directive 6: shrl $1, temp_len
  sstep
  intro af
  simp only [↓reduceIte, beq_self_eq_true]
  refine Program.loopCont_of_le (j := 7) (by rw [h_prog_len]; omega) ?_
  -- Directive 7: cmpl temp_len, start_idx
  sstep
  refine Program.loopCont_of_le (j := 8) (by rw [h_prog_len]; omega) ?_
  -- Directive 8: jge not_found
  sstep
  simp only [hd_start_len, hd_start_mask, hd_len_mask, ↓reduceIte]
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
    simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 118) rfl]
    refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
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
    refine ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
      h_distinct H s _ (strChars c d) ch fromIndex hspec rfl ?_ (Or.inl rfl)
    intro r hr_out
    simp only [get64_set64]
    by_cases h1 : r = temp_len
    · subst h1; simp at hr_out
    · by_cases h2 : r = temp_mask
      · subst h2; simp at hr_out
      · simp [h1, h2]
  dsimp only [v_ge] at hge
  have hnot_ge : v_ge = false := by
    cases h : v_ge
    · rfl
    · contradiction
  dsimp only [v_ge] at hnot_ge
  rw [hnot_ge]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Program.loopCont_of_le (j := 9) (by rw [h_prog_len]; omega) ?_
  -- Directive 9: xorq temp_offset, temp_offset
  sstep
  intro _
  refine Program.loopCont_of_le (j := 10) (by rw [h_prog_len]; omega) ?_
  -- Directive 10: cmpl $0, start_idx
  sstep
  simp only [hd_start_offset, hd_start_len, hd_start_mask, ↓reduceIte]
  refine Program.loopCont_of_le (j := 11) (by rw [h_prog_len]; omega) ?_
  -- Directive 11: cmovg start_idx, temp_offset
  sstep
  simp only [hd_start_offset, hd_start_len, hd_start_mask, ↓reduceIte]
  refine Program.loopCont_of_le (j := 12) (by rw [h_prog_len]; omega) ?_
  -- Directive 12: movl temp_len, %ecx
  sstep
  refine Program.loopCont_of_le (j := 13) (by rw [h_prog_len]; omega) ?_
  -- Directive 13: subl temp_offset, %ecx
  sstep
  refine Program.loopCont_of_le (j := 14) (by rw [h_prog_len]; omega) ?_
  -- Directive 14: testl $1, temp_mask
  sstep
  intro _
  refine Program.loopCont_of_le (j := 15) (by rw [h_prog_len]; omega) ?_
  -- Directive 15: jnz uncompressed_path
  sstep
  simp only [hd_mask_rcx, hd_mask_offset, hd_mask_len, Bool.false_eq_true, ↓reduceIte, sw32_64, lsb_and1 c, Bool.not_not]

  let from_k := if fromIndex.slt 0 then 0 else fromIndex.toNat
  have h_from_eq : (if fromIndex.slt 0 then 0 else fromIndex.toNat) = from_k := rfl
  have hT_pos : 0 < (c >>> 1).toNat := by
    by_cases hc : c.getLsbD 0 = false
    · exact pos_of_comp c hc0 hc
    · have : c.getLsbD 0 = true := by revert hc; cases c.getLsbD 0 <;> decide
      exact h_uncomp_pos this
  have hlen_eq_val : len_val = BitVec.ofNat 32 (c >>> 1).toNat := by
    dsimp [len_val]
    have : (c >>> 1).toNat < 2 ^ 32 := (c >>> 1).isLt
    rw [BitVec.ofNat_toNat]
    bv_decide
  have hstart_eq_val : start_val = fromIndex := rfl
  have h_from_lt : from_k < (c >>> 1).toNat := by
    dsimp [from_k]
    have h_not_ge' :
      let v := fromIndex - BitVec.ofNat 32 (c >>> 1).toNat
      let of := v.toInt != fromIndex.toInt - (BitVec.ofNat 32 (c >>> 1).toNat).toInt
      let sf := v.msb
      (sf == of) = false := by
      rw [← hstart_eq_val, ← hlen_eq_val]
      exact hnot_ge
    have hjge := not_jge_implies_lt fromIndex (BitVec.ofNat 32 (c >>> 1).toNat) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hT_pos) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hT_lt31) h_not_ge'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hjge
    exact hjge
  let r := (c >>> 1).toNat - from_k
  have h_rk : from_k + r = (c >>> 1).toNat := by omega
  have hr_pos : 0 < r := by omega
  let m := r - 1
  have hm1 : m + 1 = r := by omega
  have h_km : from_k + (m + 1) = (c >>> 1).toNat := by omega
  have h_from_le : from_k ≤ (c >>> 1).toNat - r := by omega
  have hpre_empty : ∀ (i : Nat) (hi : i < (c >>> 1).toNat - r - from_k),
    (((strChars c d).drop from_k).get ⟨i, by rw [List.length_drop, h_len_eq]; omega⟩).zeroExtend 32 ≠ ch := by
    intro i hi; omega

  by_cases h_comp : c.getLsbD 0 = false
  · rw [h_comp]
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 16) (by rw [h_prog_len]; omega) ?_
    -- Directive 16: cmpl $127, search_value
    sstep
    simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]
    refine Program.loopCont_of_le (j := 17) (by rw [h_prog_len]; omega) ?_
    -- Directive 17: jg not_found
    sstep
    by_cases h_ch127 : ch.toNat > 127
    · rw [jg_ch127_true h_ch127 h_ch_le]
      simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 118) rfl]
      refine Program.loopCont_of_le (j := 118) (by rw [h_prog_len]; omega) ?_
      have h_ascii' := strChars_compressed_ascii h_comp hl (h_ascii h_comp)
      have hspec : indexOfSpec (strChars c d) ch fromIndex = -1#32 :=
        indexOfSpec_compressed_gt127 h_ascii' h_ch127
      exact ret_not_found_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct H s _ (strChars c d) ch fromIndex hspec rfl (by
          intro r' hr_out
          simp only [get64_set64]
          by_cases h1 : r' = Reg64.rcx
          · subst h1; simp at hr_out
          · by_cases h2 : r' = temp_offset
            · subst h2; simp at hr_out
            · by_cases h3 : r' = temp_len
              · subst h3; simp at hr_out
              · by_cases h4 : r' = temp_mask
                · subst h4; simp at hr_out
                · simp [h1, h2, h3, h4]) (Or.inl rfl)
    · have h_ch127_le : ch.toNat ≤ 127 := by omega
      rw [jg_ch127_false h_ch127_le]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 18) (by rw [h_prog_len]; omega) ?_
      -- Directive 18: cmpl $32, temp_len
      sstep
      refine Program.loopCont_of_le (j := 19) (by rw [h_prog_len]; omega) ?_
      -- Directive 19: jb compressed_scalar_loop
      sstep
      simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
      have h_eq : c.ushiftRight 1 = BitVec.ofNat 32 (c >>> 1).toNat := by
        apply BitVec.eq_of_toNat_eq
        simp
        rw [Nat.mod_eq_of_lt (by have := c.isLt; omega)]
      have h_cf : (BitVec.unsigned (c.ushiftRight 1 - 32#32) != (c.ushiftRight 1).unsigned - (32#32).unsigned) =
          decide ((c >>> 1).toNat < 32) := by
        conv => lhs; rw [h_eq]
        exact cf_ofNat32 (x := (c >>> 1).toNat) (c := 32) (c >>> 1).isLt (by decide)
      by_cases hT32 : (c >>> 1).toNat < 32
      · rw [h_cf, decide_eq_true_iff.mpr hT32]
        simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 54) rfl]
        refine Program.loopCont_of_le (j := 54) (by rw [h_prog_len]; omega) ?_
        have hinfo := string_info_of hmem hl
        have h_byte_len : strByteLen c = (c >>> 1).toNat := by
          unfold strByteLen; rw [h_comp]; simp
        have h_some : ∀ i < (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
        have h_data : ∀ i < (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
        have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
            ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32 := by
          intro i hi
          rw [strChars_compressed_get h_comp i hi]
          apply BitVec.eq_of_toNat_eq; simp
        have h_chars_drop : ∀ (i : Nat) (hi : i < from_k - from_k),
            (((strChars c d).drop from_k).get ⟨i, by rw [List.length_drop, h_len_eq]; omega⟩).zeroExtend 32 ≠ ch := by
          intro i hi; omega
        refine compressed_scalar_loop_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl h_data h_some ch h_ch127_le
          (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq m from_k _ rfl ?_ (Or.inl rfl) ?_ ?_ ?_ h_km (by omega) h_chars_drop
        · intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
          simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
        · simp only [get_low32, get64_set64, hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]; rfl
        · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          exact cmovg_start_idx_eval fromIndex
        · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          have hstart_w : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
          rw [hstart_w]
          have hcmov32 := cmovg32_eval fromIndex
          rw [hcmov32]
          rw [h_eq, h_from_eq]
          rw [ofNat_sub32 (c >>> 1).toNat from_k (by omega) (c >>> 1).isLt]
          rw [hm1]
      · rw [h_cf, decide_eq_false_iff_not.mpr hT32]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 20) (by rw [h_prog_len]; omega) ?_
        -- Directive 20: vmovd search_value, ymm_match
        sstep
        refine Program.loopCont_of_le (j := 21) (by rw [h_prog_len]; omega) ?_
        -- Directive 21: vpbroadcastb ymm_match, ymm_target
        sstep
        refine Program.loopCont_of_le (j := 22) (by rw [h_prog_len]; omega) ?_
        -- Directive 22: cmpl $32, %ecx
        sstep
        refine Program.loopCont_of_le (j := 23) (by rw [h_prog_len]; omega) ?_
        -- Directive 23: jb compressed_tail
        sstep
        simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
          hd_len_rcx', hd_len_offset', hd_len_mask',
          Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
        have hstart_w : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
        rw [hstart_w]
        have hcmov32 := cmovg32_eval fromIndex
        rw [hcmov32]
        rw [h_eq, h_from_eq]
        rw [ofNat_sub32 (c >>> 1).toNat from_k (by omega) (c >>> 1).isLt]
        have hr_eq : BitVec.ofNat 32 ((c >>> 1).toNat - from_k) = BitVec.ofNat 32 r := rfl
        rw [hr_eq]
        have h_cf_r : (BitVec.unsigned (BitVec.ofNat 32 r - 32#32) != (BitVec.ofNat 32 r).unsigned - (32#32).unsigned) =
            decide (r < 32) := by
          have hr_lt : r < 2 ^ 32 := by omega
          exact cf_ofNat32 (x := r) (c := 32) hr_lt (by decide)
        have hinfo := string_info_of hmem hl
        have h_byte_len : strByteLen c = (c >>> 1).toNat := by
          unfold strByteLen; rw [h_comp]; simp
        have h_some : ∀ i < (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
        have h_data : ∀ i < (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
          intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
        have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
            ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 = (d.getD i 0).toBitVec.zeroExtend 32 := by
          intro i hi
          rw [strChars_compressed_get h_comp i hi]
          apply BitVec.eq_of_toNat_eq; simp
        have hT32_le : 32 ≤ (c >>> 1).toNat := by omega
        by_cases hr32 : r < 32
        · rw [h_cf_r, decide_eq_true_iff.mpr hr32]
          simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 33) rfl]
          refine Program.loopCont_of_le (j := 33) (by rw [h_prog_len]; omega) ?_
          refine compressed_tail_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
            h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT32_le h_data h_some ch h_ch127_le
            (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq _ rfl ?_ ?_ ?_ r hr32 ?_ ?_ h_from_le hpre_empty ?_
          · intro r' hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
            simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
          · refine ⟨BitVec.broadcastb 256 (BitVec.setWidth 8 ch), BitVec.zeroExtend 256 ch, ?_⟩
            dsimp only []
            simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
            have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
            rw [hch_sub, bcastb_eq]
            exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) (Ne.symm h_ymm_diff)
          · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
            exact setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt
          · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
              Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
            rw [setWidth_ofNat from_k (by omega)]
            have : (c >>> 1).toNat - r = from_k := by omega
            rw [this]
          · dsimp only []
            simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte, zmms_get_set]
            have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
            rw [hch_sub, bcastb_eq]
        · rw [h_cf_r, decide_eq_false_iff_not.mpr hr32]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Program.loopCont_of_le (j := 24) (by rw [h_prog_len]; omega) ?_
          have hr32_le : 32 ≤ r := by omega
          refine compressed_avx_loop_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
            h_distinct h_ymm_diff hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT32_le h_data h_some ch h_ch127_le
            (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq
            r from_k _ rfl ?_ ?_ ?_ ?_ ?_ h_rk hr32_le (by omega) (by intro i hi; omega)
          · intro r' hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
            simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
          · refine ⟨BitVec.zeroExtend 256 ch, ?_⟩
            dsimp only []
            simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
            have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
            rw [hch_sub, bcastb_eq]
            exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastb 256 (BitVec.setWidth 8 ch)) (Ne.symm h_ymm_diff)
          · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
            exact setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt
          · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
            exact setWidth_ofNat from_k (by omega)
          · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
              Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]

  · have h_uncomp : c.getLsbD 0 = true := by
      revert h_comp
      cases c.getLsbD 0 <;> decide
    rw [h_uncomp]
    simp only [Bool.not_true, ↓reduceIte, addrOf_label hlab (H := H) (i := 65) rfl]
    refine Program.loopCont_of_le (j := 65) (by rw [h_prog_len]; omega) ?_
    -- Directive 65: .label uncompressed_path
    sstep
    refine Program.loopCont_of_le (j := 66) (by rw [h_prog_len]; omega) ?_
    -- Directive 66: cmpl $16, temp_len
    sstep
    refine Program.loopCont_of_le (j := 67) (by rw [h_prog_len]; omega) ?_
    -- Directive 67: jb uncompressed_scalar_loop
    sstep
    simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
    have h_eq : c.ushiftRight 1 = BitVec.ofNat 32 (c >>> 1).toNat := by
      apply BitVec.eq_of_toNat_eq
      simp
      rw [Nat.mod_eq_of_lt (by have := c.isLt; omega)]
    have h_cf : (BitVec.unsigned (c.ushiftRight 1 - 16#32) != (c.ushiftRight 1).unsigned - (16#32).unsigned) =
        decide ((c >>> 1).toNat < 16) := by
      conv => lhs; rw [h_eq]
      exact cf_ofNat32 (x := (c >>> 1).toNat) (c := 16) (c >>> 1).isLt (by decide)
    by_cases hT16 : (c >>> 1).toNat < 16
    · rw [h_cf, decide_eq_true_iff.mpr hT16]
      simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 105) rfl]
      refine Program.loopCont_of_le (j := 105) (by rw [h_prog_len]; omega) ?_
      have hinfo := string_info_of hmem hl
      have h_byte_len : strByteLen c = 2 * (c >>> 1).toNat := by
        unfold strByteLen; rw [h_uncomp]; simp
      have h_some : ∀ i < 2 * (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
        intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
      have h_data : ∀ i < 2 * (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
        intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
      have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
          ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 =
            ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
              ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
        intro i hi
        exact congrArg (BitVec.zeroExtend 32) (strChars_uncompressed_get h_uncomp i hi)
      have h_chars_drop : ∀ (i : Nat) (hi : i < from_k - from_k),
          (((strChars c d).drop from_k).get ⟨i, by rw [List.length_drop, h_len_eq]; omega⟩).zeroExtend 32 ≠ ch := by
        intro i hi; omega
      refine uncompressed_scalar_loop_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
        h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl h_data h_some ch h_ch_le
        (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq m from_k _ rfl ?_ (Or.inl rfl) ?_ ?_ ?_ h_km (by omega) h_chars_drop
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
        simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
      · simp only [get_low32, get64_set64, hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
        rw [cmovg64_eval fromIndex, h_from_eq]
      · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
          Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
        have hstart_w : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
        rw [hstart_w]
        have hcmov32 := cmovg32_eval fromIndex
        rw [hcmov32]
        rw [h_eq, h_from_eq]
        rw [ofNat_sub32 (c >>> 1).toNat from_k (by omega) (c >>> 1).isLt]
        rw [hm1]
    · rw [h_cf, decide_eq_false_iff_not.mpr hT16]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Program.loopCont_of_le (j := 68) (by rw [h_prog_len]; omega) ?_
      -- Directive 68: vmovd search_value, ymm_match
      sstep
      refine Program.loopCont_of_le (j := 69) (by rw [h_prog_len]; omega) ?_
      -- Directive 69: vpbroadcastw ymm_match, ymm_target
      sstep
      refine Program.loopCont_of_le (j := 70) (by rw [h_prog_len]; omega) ?_
      -- Directive 70: cmpl $16, %ecx
      sstep
      refine Program.loopCont_of_le (j := 71) (by rw [h_prog_len]; omega) ?_
      -- Directive 71: jb uncompressed_tail
      sstep
      simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask',
        hd_len_rcx', hd_len_offset', hd_len_mask',
        Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
      have hstart_w : BitVec.setWidth 32 (s.regs.get64 start_idx) = fromIndex := rfl
      rw [hstart_w]
      have hcmov32 := cmovg32_eval fromIndex
      rw [hcmov32]
      rw [h_eq, h_from_eq]
      rw [ofNat_sub32 (c >>> 1).toNat from_k (by omega) (c >>> 1).isLt]
      have hr_eq : BitVec.ofNat 32 ((c >>> 1).toNat - from_k) = BitVec.ofNat 32 r := rfl
      rw [hr_eq]
      have h_cf_r : (BitVec.unsigned (BitVec.ofNat 32 r - 16#32) != (BitVec.ofNat 32 r).unsigned - (16#32).unsigned) =
          decide (r < 16) := by
        have hr_lt : r < 2 ^ 32 := by omega
        exact cf_ofNat32 (x := r) (c := 16) hr_lt (by decide)
      have hinfo := string_info_of hmem hl
      have h_byte_len : strByteLen c = 2 * (c >>> 1).toNat := by
        unfold strByteLen; rw [h_uncomp]; simp
      have h_some : ∀ i < 2 * (c >>> 1).toNat, (s.dmem[s.regs.get64 str + 16#64 + BitVec.ofNat 64 i]?).isSome := by
        intro i hi; rw [h_byte_len] at hinfo; exact hinfo.1 i hi
      have h_data : ∀ i < 2 * (c >>> 1).toNat, byteAt s.dmem (s.regs.get64 str) i = d.getD i 0 := by
        intro i hi; rw [h_byte_len] at hinfo; exact hinfo.2 i hi
      have h_chars : ∀ (i : Nat) (hi : i < (c >>> 1).toNat),
          ((strChars c d).get ⟨i, by rw [h_len_eq]; exact hi⟩).zeroExtend 32 =
            ((d.getD (2 * i) 0).toBitVec.zeroExtend 16 |||
              ((d.getD (2 * i + 1) 0).toBitVec.zeroExtend 16 <<< 8)).zeroExtend 32 := by
        intro i hi
        exact congrArg (BitVec.zeroExtend 32) (strChars_uncompressed_get h_uncomp i hi)
      have hT16_le : 16 ≤ (c >>> 1).toNat := by omega
      by_cases hr16 : r < 16
      · rw [h_cf_r, decide_eq_true_iff.mpr hr16]
        simp only [↓reduceIte, addrOf_label hlab (H := H) (i := 81) rfl]
        refine Program.loopCont_of_le (j := 81) (by rw [h_prog_len]; omega) ?_
        refine uncompressed_tail_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT16_le h_data h_some ch h_ch_le
          (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq _ rfl ?_ ?_ ?_ r hr16 ?_ ?_ h_from_le hpre_empty ?_
        · intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
          simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
        · refine ⟨BitVec.broadcastw 256 (BitVec.setWidth 16 ch), BitVec.zeroExtend 256 ch, ?_⟩
          dsimp only []
          simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
          have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
          rw [hch_sub, bcastw_eq]
          exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastw 256 (BitVec.setWidth 16 ch)) (Ne.symm h_ymm_diff)
        · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
          exact setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt
        · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
        · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          rw [setWidth_ofNat from_k (by omega)]
          have : (c >>> 1).toNat - r = from_k := by omega
          rw [this]
        · dsimp only []
          simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte, zmms_get_set]
          have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
          rw [hch_sub, bcastw_eq]
      · rw [h_cf_r, decide_eq_false_iff_not.mpr hr16]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Program.loopCont_of_le (j := 72) (by rw [h_prog_len]; omega) ?_
        have hr16_le : 16 ≤ r := by omega
        refine uncompressed_avx_loop_lemma_after slow str search_value start_idx out temp_len temp_offset temp_mask ymm_target ymm_match
          h_distinct h_ymm_diff hlab H s c d (s.regs.get64 str) (c >>> 1).toNat rfl rfl hT16_le h_data h_some ch h_ch_le
          (strChars c d) h_len_eq h_chars fromIndex from_k h_from_eq
          r from_k _ rfl ?_ ?_ ?_ ?_ ?_ h_rk hr16_le (by omega) (by intro i hi; omega)
        · intro r' hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          obtain ⟨hout_ne, hrcx_ne, hlen_ne, hoff_ne, hmask_ne⟩ := hr'
          simp only [get64_set64, hrcx_ne, hoff_ne, hlen_ne, hmask_ne, ↓reduceIte]
        · refine ⟨BitVec.zeroExtend 256 ch, ?_⟩
          dsimp only []
          simp only [hd_search_rcx_ne, hd_search_offset_ne, hd_search_len_ne, hd_search_mask_ne, get64_set64, get_low32, Bool.false_eq_true, ↓reduceIte]
          have hch_sub : BitVec.setWidth 32 (s.regs.get64 search_value) = ch := rfl
          rw [hch_sub, bcastw_eq]
          exact Proof.zmms_set_set_of_ne s.zmms ymm_match ymm_target (BitVec.zeroExtend 256 ch) (BitVec.broadcastw 256 (BitVec.setWidth 16 ch)) (Ne.symm h_ymm_diff)
        · simp only [get64_set64, sw32_64, hd_len_rcx', hd_len_offset', hd_len_mask', hd_search_len_ne, Bool.false_eq_true, ↓reduceIte]
          exact setWidth_ofNat (c >>> 1).toNat (c >>> 1).isLt
        · simp only [get64_set64, hd_offset_rcx, hd_offset_len, hd_offset_mask', Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]
          exact setWidth_ofNat from_k (by omega)
        · simp only [get64_set64, sw32_64, hd_offset_rcx, hd_offset_len, hd_offset_mask', hd_len_rcx', hd_len_offset', hd_len_mask',
            Bool.false_eq_true, BitVec.xor_self, BitVec.setWidth_zero, ↓reduceIte]


end Proof

end

end Kraken.X64.Art
