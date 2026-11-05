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

end

end Kraken.X64.Art
