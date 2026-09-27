# Test: memory operands without a base register, as in FFmpeg's
# `lea -0x40(,%ecx,4),%rcx` (ff_vector_fmul_sse). At 32-bit address size the
# 32-bit result, which may wrap, is zero-extended into the destination. The
# index registers carry garbage in their upper halves, which a 32-bit address
# ignores.

movq $-1, %rdi
shlq $32, %rdi
orq $0x10, %rdi                 # edi = 16
leaq -0x40(,%edi,4), %r8        # 0
leaq 0x10(,%edi,8), %r9         # 0x90

movq $-1, %rsi
shlq $32, %rsi                  # esi = 0
leaq -0x40(,%esi,4), %r10       # wraps: 0xffffffc0

movl $0x80000000, %eax
leaq 7(,%eax,8), %r11           # wraps: 7
leaq -0x40(,%rax,4), %r12       # 64-bit address size: 0x1ffffffc0
leaq (,%rax,8), %r13            # 0x400000000

movl $-1, %edx
leaq 0x10(,%edx,4), %r14        # the index is signed: 12
leaq 0x10(,%rdx,4), %r15        # 0x40000000c

movq $-1, %rcx
shlq $32, %rcx
orq $0x40000020, %rcx           # len = 2^30 + 32
leaq -0x40(,%ecx,4), %rcx       # wraps: 0x40

cmpq %rcx, %r8                  # `or` and `shl` leave AF undefined
