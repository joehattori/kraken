# Test: FFmpeg's ff_scalarproduct_float_fma3 (libavutil/x86/float_dsp.asm), as
# disassembled from the object file, called on 4, 8, 16, 32, 60 and 100
# floats. Between them these lengths take every path through the routine. v2
# is v1 shifted by one float: the pointers are not `restrict`, and v2 need not
# be aligned. The dot products are saved in xmm8-xmm13.

  subq $0x1a0, %rsp               # 104 floats, 16-byte aligned
  xorl %ecx, %ecx
  movl $12345, %ebx
fill:
  imull $1103515245, %ebx, %ebx
  addl $12345, %ebx
  movl %ebx, %eax
  andl $0x807fffff, %eax          # a random sign and mantissa...
  orl $0x3f800000, %eax           # ...with the exponent of 1.0
  movl %eax, (%rsp,%rcx,4)
  addq $1, %rcx
  cmpq $104, %rcx
  jl fill

  movq %rsp, %rdi
  leaq 4(%rsp), %rsi
  movl $4, %edx                   # .l16 from the entry
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm8
  movl $8, %edx                   # .l32 from the entry, returns after .loop32
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm9
  movl $16, %edx                  # .l64 from the entry, returns after .loop64
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm10
  movl $32, %edx                  # .loop128 once, returns after it
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm11
  movl $60, %edx                  # .loop128, .loop64, .loop32, .loop16
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm12
  movl $100, %edx                 # .loop128 three times, then .loop16
  call ff_scalarproduct_float_fma3
  vmovaps %xmm0, %xmm13
  movq $0, %rdi                   # stack addresses differ between the runs
  movq $0, %rsi
  addq $0x1a0, %rsp
  jmp end

ff_scalarproduct_float_fma3:
    xor %r8,%r8
    vxorps %ymm0,%ymm0,%ymm0
    shl $0x2,%edx
    mov %rdx,%rcx
    cmp $0x20,%rcx
    jl .l16
    cmp $0x40,%rcx
    jl .l32
    vxorps %ymm1,%ymm1,%ymm1
    cmp $0x80,%rcx
    jl .l64
    and $0xffffffffffffff80,%rcx
    vxorps %ymm2,%ymm2,%ymm2
    vxorps %ymm3,%ymm3,%ymm3
.loop128:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vmovups 0x40(%rdi,%r8,1),%ymm6
    vmovups 0x60(%rdi,%r8,1),%ymm7
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    vfmadd231ps 0x40(%rsi,%r8,1),%ymm6,%ymm2
    vfmadd231ps 0x60(%rsi,%r8,1),%ymm7,%ymm3
    sub $0xffffffffffffff80,%r8
    cmp %rcx,%r8
    jl .loop128
    vaddps %ymm2,%ymm0,%ymm0
    vaddps %ymm3,%ymm1,%ymm1
    mov %rdx,%rcx
    and $0x7f,%rcx
    cmp $0x40,%rcx
    jge .l64
    vaddps %ymm1,%ymm0,%ymm0
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    ret
.l64:
    and $0xffffffffffffffc0,%rcx
    add %r8,%rcx
.loop64:
    vmovups (%rdi,%r8,1),%ymm4
    vmovups 0x20(%rdi,%r8,1),%ymm5
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1
    add $0x40,%r8
    cmp %rcx,%r8
    jl .loop64
    vaddps %ymm1,%ymm0,%ymm0
    mov %rdx,%rcx
    and $0x3f,%rcx
    cmp $0x20,%rcx
    jge .l32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    ret
.l32:
    and $0xffffffffffffffe0,%rcx
    add %r8,%rcx
.loop32:
    vmovups (%rdi,%r8,1),%ymm4
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0
    add $0x20,%r8
    cmp %rcx,%r8
    jl .loop32
    vextractf128 $0x1,%ymm0,%xmm2
    vaddps %xmm2,%xmm0,%xmm0
    mov %rdx,%rcx
    and $0x1f,%rcx
    cmp $0x10,%rcx
    jge .l16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    ret
.l16:
    and $0xfffffffffffffff0,%rcx
    add %r8,%rcx
.loop16:
    vmovaps (%rdi,%r8,1),%xmm1
    vmulps (%rsi,%r8,1),%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    add $0x10,%r8
    cmp %rcx,%r8
    jl .loop16
    vmovhlps %xmm0,%xmm1,%xmm1
    vaddps %xmm1,%xmm0,%xmm0
    vmovss %xmm0,%xmm1,%xmm1
    vshufps $0x1,%xmm0,%xmm0,%xmm0
    vaddss %xmm1,%xmm0,%xmm0
    vzeroupper
    ret
end:
