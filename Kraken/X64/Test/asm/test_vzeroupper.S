# Test: vzeroupper clears bits 255:128 of ymm0-15 and keeps bits 127:0.

subq $0x20, %rsp
movl $0x3f800000, 0(%rsp)
movl $0x40000000, 4(%rsp)
movl $0x40400000, 8(%rsp)
movl $0x40800000, 12(%rsp)
movl $0x40a00000, 16(%rsp)
movl $0x40c00000, 20(%rsp)
movl $0x40e00000, 24(%rsp)
movl $0x41000000, 28(%rsp)

vmovups 0(%rsp), %ymm0
vmovups 0(%rsp), %ymm1
vmovups 0(%rsp), %ymm2
vmovups 0(%rsp), %ymm3
vmovups 0(%rsp), %ymm4
vmovups 0(%rsp), %ymm5
vmovups 0(%rsp), %ymm6
vmovups 0(%rsp), %ymm7
vmovups 0(%rsp), %ymm8
vmovups 0(%rsp), %ymm9
vmovups 0(%rsp), %ymm10
vmovups 0(%rsp), %ymm11
vmovups 0(%rsp), %ymm12
vmovups 0(%rsp), %ymm13
vmovups 0(%rsp), %ymm14
vmovups 0(%rsp), %ymm15
vxorps %ymm1, %ymm0, %ymm1

vzeroupper

addq $0x20, %rsp
