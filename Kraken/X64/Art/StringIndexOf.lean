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

open Std
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/--
AVX2 assembly template for `String.indexOf(ch)` (`start_at_zero = true`).
-/
def stringIndexOfProg (slow : Label)
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
def stringIndexOfAfterProg (slow : Label)
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

end

end Kraken.X64.Art
