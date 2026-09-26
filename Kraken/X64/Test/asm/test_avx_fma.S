# Test: VEX vfmadd231ps (dst := src1 * src2 + dst, rounded once), in register
# and memory forms, on xmm and ymm registers. Several lanes round differently
# when the multiply and the add are done separately (see vmulps/vaddps below).
# No lane produces a NaN: Kraken's NaN bit patterns differ from x86's.

subq $0xc0, %rsp

# Set 1: a at 0, b at 32, c at 64
movl $0x3f800800, 0(%rsp)    # (1+2^-12)^2 - 1 = 2^-11 + 2^-24 exactly
movl $0x3f800800, 32(%rsp)
movl $0xbf800000, 64(%rsp)
movl $0x40000000, 4(%rsp)    # 2 * 3 + 1
movl $0x40400000, 36(%rsp)
movl $0x3f800000, 68(%rsp)
movl $0x80000001, 8(%rsp)    # -tiny * tiny + 0 underflows to -0
movl $0x00000001, 40(%rsp)
movl $0x00000000, 72(%rsp)
movl $0x00000000, 12(%rsp)   # +0 * 5 + -0 = +0
movl $0x40a00000, 44(%rsp)
movl $0x80000000, 76(%rsp)
movl $0x3fc00000, 16(%rsp)   # 1.5 * 2 - 3 cancels exactly to +0
movl $0x40000000, 48(%rsp)
movl $0xc0400000, 80(%rsp)
movl $0x7f7fffff, 20(%rsp)   # FLT_MAX * 2 - FLT_MAX: no intermediate overflow
movl $0x40000000, 52(%rsp)
movl $0xff7fffff, 84(%rsp)
movl $0x00800000, 24(%rsp)   # 2^-126 * 0.5 + 2^-149 is subnormal
movl $0x3f000000, 56(%rsp)
movl $0x00000001, 88(%rsp)
movl $0x3f800001, 28(%rsp)   # (1+2^-23)(1-2^-24) - 1 = 2^-24 - 2^-47 exactly
movl $0x3f7fffff, 60(%rsp)
movl $0xbf800000, 92(%rsp)

# Set 2: a at 96, b at 128, c at 160
movl $0x3f800000, 96(%rsp)   # 1 * 1 + 2^-24 is a tie, rounds to even
movl $0x3f800000, 128(%rsp)
movl $0x33800000, 160(%rsp)
movl $0x3f800000, 100(%rsp)  # 1 * 1 + 2^-24(1+2^-23) rounds up
movl $0x3f800000, 132(%rsp)
movl $0x33800001, 164(%rsp)
movl $0x3f800001, 104(%rsp)  # (1+2^-23)^2 + 0 must still be rounded
movl $0x3f800001, 136(%rsp)
movl $0x00000000, 168(%rsp)
movl $0x3f800001, 108(%rsp)  # (1+2^-23)^2 + -0
movl $0x3f800001, 140(%rsp)
movl $0x80000000, 172(%rsp)
movl $0xc0000000, 112(%rsp)  # -2 * 3 - 1
movl $0x40400000, 144(%rsp)
movl $0xbf800000, 176(%rsp)
movl $0x7f800000, 116(%rsp)  # inf * 2 + 1
movl $0x40000000, 148(%rsp)
movl $0x3f800000, 180(%rsp)
movl $0x7149f2ca, 120(%rsp)  # 1e30 * 1e10 - inf
movl $0x501502f9, 152(%rsp)
movl $0xff800000, 184(%rsp)
movl $0x00000003, 124(%rsp)  # 3*2^-149 * 0.5 + 0 is a subnormal tie
movl $0x3f000000, 156(%rsp)
movl $0x00000000, 188(%rsp)

# Set 1, memory and register forms
vmovups 0(%rsp), %ymm0
vmovups 32(%rsp), %ymm2
vmovups 64(%rsp), %ymm1
vfmadd231ps 32(%rsp), %ymm0, %ymm1
vmovups 64(%rsp), %ymm3
vfmadd231ps %ymm2, %ymm0, %ymm3

# Set 1, unfused, for comparison
vmulps %ymm2, %ymm0, %ymm5
vaddps 64(%rsp), %ymm5, %ymm5

# Set 2
vmovups 96(%rsp), %ymm6
vmovups 128(%rsp), %ymm7
vmovups 160(%rsp), %ymm8
vfmadd231ps %ymm7, %ymm6, %ymm8
vmovups 160(%rsp), %ymm9
vfmadd231ps 128(%rsp), %ymm6, %ymm9

# xmm forms clear bits 255:128 of the destination
vmovups 160(%rsp), %ymm4
vfmadd231ps %xmm7, %xmm6, %xmm4
vmovups 64(%rsp), %ymm10
vfmadd231ps 32(%rsp), %xmm0, %xmm10

# Unaligned memory operand, added to zero
vxorps %ymm12, %ymm12, %ymm12
vfmadd231ps 4(%rsp), %ymm2, %ymm12

addq $0xc0, %rsp
