# Test: VEX vextractf128, vmovhlps, vmovss (register form), vshufps and
# vaddss. The xmm forms clear bits 255:128 of the destination.

subq $0x40, %rsp
movl $0x3f800000, 0(%rsp)   # 1.0
movl $0x40000000, 4(%rsp)   # 2.0
movl $0x40400000, 8(%rsp)   # 3.0
movl $0x40800000, 12(%rsp)  # 4.0
movl $0x40a00000, 16(%rsp)  # 5.0
movl $0x40c00000, 20(%rsp)  # 6.0
movl $0x40e00000, 24(%rsp)  # 7.0
movl $0x41000000, 28(%rsp)  # 8.0
movl $0x41100000, 32(%rsp)  # 9.0
movl $0x41200000, 36(%rsp)  # 10.0
movl $0x41300000, 40(%rsp)  # 11.0
movl $0x41400000, 44(%rsp)  # 12.0
movl $0x3dcccccd, 48(%rsp)  # 0.1
movl $0x3e4ccccd, 52(%rsp)  # 0.2
movl $0x3e99999a, 56(%rsp)  # 0.3
movl $0x3ecccccd, 60(%rsp)  # 0.4

vmovups 0(%rsp), %ymm0
vmovups 32(%rsp), %ymm1

# vextractf128
vextractf128 $1, %ymm0, %xmm2
vextractf128 $0, %ymm1, %xmm3
vmovups %ymm1, %ymm4
vextractf128 $1, %ymm0, %xmm4

# vmovhlps: dst[63:0] := src2[127:64], dst[127:64] := src1[127:64]
vmovups %ymm1, %ymm5
vmovhlps %xmm0, %xmm1, %xmm5

# vmovss: dst[31:0] := src2[31:0], dst[127:32] := src1[127:32]
vmovups %ymm1, %ymm6
vmovss %xmm0, %xmm1, %xmm6

# vshufps
vshufps $0x1, %xmm0, %xmm0, %xmm7
vshufps $0x1b, %xmm1, %xmm0, %xmm8
vshufps $0xe4, %ymm1, %ymm0, %ymm9
vshufps $0x93, 32(%rsp), %ymm0, %ymm10
vmovups %ymm0, %ymm11
vshufps $0xff, %xmm1, %xmm0, %xmm11

# vaddss: dst[31:0] := src1[31:0] + src2[31:0], dst[127:32] := src1[127:32]
vaddss %xmm1, %xmm0, %xmm12
vmovups %ymm0, %ymm13
vaddss %xmm1, %xmm13, %xmm13
vextractf128 $1, %ymm1, %xmm14
vaddss %xmm14, %xmm0, %xmm14   # 1.0 + 0.1 rounds

addq $0x40, %rsp
