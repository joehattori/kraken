# Test: VEX vxorps, vaddps, vmulps and vmovaps, on xmm and ymm registers and
# memory operands. A VEX write clears the bits of the destination above the
# operation width.

# The stack is 256-byte aligned, so the 64 bytes below are 32-byte aligned.
subq $0x40, %rsp
movl $0x3f800000, 0(%rsp)   # 1.0
movl $0x40000000, 4(%rsp)   # 2.0
movl $0x40400000, 8(%rsp)   # 3.0
movl $0x40800000, 12(%rsp)  # 4.0
movl $0x3f000000, 16(%rsp)  # 0.5
movl $0x3fc00000, 20(%rsp)  # 1.5
movl $0xbf800000, 24(%rsp)  # -1.0
movl $0x41200000, 28(%rsp)  # 10.0
movl $0x3dcccccd, 32(%rsp)  # 0.1
movl $0x3e4ccccd, 36(%rsp)  # 0.2
movl $0x3e99999a, 40(%rsp)  # 0.3
movl $0x3ecccccd, 44(%rsp)  # 0.4
movl $0x40490fdb, 48(%rsp)  # pi
movl $0xc02df854, 52(%rsp)  # -e
movl $0x7f7fffff, 56(%rsp)  # FLT_MAX
movl $0x00000001, 60(%rsp)  # the smallest subnormal

vmovups 0(%rsp), %ymm0
vmovups 32(%rsp), %ymm1

# Whole ymm registers
vaddps %ymm1, %ymm0, %ymm2
vxorps %ymm1, %ymm0, %ymm3
vmulps %ymm1, %ymm1, %ymm4      # FLT_MAX^2 overflows, subnormal^2 underflows

# Memory operands need no alignment in the VEX forms
vaddps 4(%rsp), %ymm1, %ymm5
vmulps 20(%rsp), %xmm1, %xmm6
vmulps 16(%rsp), %xmm1, %xmm7

# xmm destinations clear bits 255:128
vmovaps %ymm0, %ymm8
vaddps %xmm1, %xmm8, %xmm8
vmovups %ymm1, %ymm9
vxorps %xmm9, %xmm9, %xmm9
vmovups %ymm1, %ymm10
vmulps %xmm0, %xmm10, %xmm10

# vmovaps loads and stores (aligned)
vmovaps 32(%rsp), %xmm11
vmovaps 0(%rsp), %ymm12
vmovaps %xmm0, 48(%rsp)
movq 48(%rsp), %rax
movq 56(%rsp), %rbx

addq $0x40, %rsp
