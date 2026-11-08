# Test vpmovzxbw (register and memory forms, xmm and ymm destinations)
# Initialize 32 stack bytes with distinct values including >0x7F bytes.
movabsq $0x55aa33cc11ee00ff, %rax
pushq %rax
movabsq $0x123456789abcdef0, %rax
pushq %rax
movabsq $0xff807f421102fe01, %rax
pushq %rax
movabsq $0x99aabbccddeeff10, %rax
pushq %rax

# Set non-zero bits in %ymm0 and %ymm1 first to test upper-bit zeroing.
vmovdqu (%rsp), %ymm0
vmovdqu (%rsp), %ymm1
movq %rsp, %rdi

# Memory sources (only 8 bytes read for xmm dst; 16 bytes for ymm dst).
# 24(%rsp) reaches only bytes 24..31, testing the 8-byte m64 bound on xmm.
vpmovzxbw (%rdi), %xmm0
vpmovzxbw (%rdi), %ymm1
vpmovzxbw 24(%rsp), %xmm2
vpmovzxbw 8(%rsp), %ymm3

# Register sources (upper 128 bits of %ymm4/%ymm5 pre-populated)
vmovdqu (%rsp), %ymm4
vmovdqu (%rsp), %ymm5
vmovdqu (%rsp), %xmm6
vpmovzxbw %xmm6, %xmm4
vpmovzxbw %xmm6, %ymm5

popq %rax
popq %rax
popq %rax
popq %rax
