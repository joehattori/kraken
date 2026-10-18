# MOVQ copies only the low 64 bits and preserves flags and vector registers.
# Intel SDM Vol. 2B, MOVD/MOVQ (REX.W + 66 0F 7E).
movabsq $0xfedcba9876543210, %rax
pushq %rax
movabsq $0x0123456789abcdef, %rax
pushq %rax
movups (%rsp), %xmm2
movups (%rsp), %xmm3
cmpq $1, %rax
movq %xmm2, %rbp
movq %xmm3, %r9
movq %xmm2, %rax
popq %rbx
popq %rcx
