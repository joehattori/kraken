# Test: FFmpeg's ff_vector_fmul_sse (libavutil/x86/float_dsp.asm), as
# disassembled from the object file (with `ret` for its `repz ret`), called on
# 16, 32 and 48 floats. The pointers are not `restrict`: the calls use distinct
# arrays, dst == src0 (in place) and dst == src1. On the first call the upper
# half of rcx holds garbage, which the routine ignores. The harness does not
# compare memory, so parts of each output are reloaded into xmm8-xmm15.

  subq $0x300, %rsp               # three arrays of 64 floats, 16-byte aligned
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
  cmpq $192, %rcx
  jl fill

  leaq 0x200(%rsp), %rdi          # distinct arrays, 16 floats
  movq %rsp, %rsi
  leaq 0x100(%rsp), %rdx
  movq $-1, %rcx
  shlq $32, %rcx
  orq $16, %rcx
  call ff_vector_fmul_sse
  movaps 0x200(%rsp), %xmm8
  movaps 0x230(%rsp), %xmm9

  leaq 0x200(%rsp), %rdi          # distinct arrays, 32 floats
  movq %rsp, %rsi
  leaq 0x100(%rsp), %rdx
  movl $32, %ecx
  call ff_vector_fmul_sse
  movaps 0x240(%rsp), %xmm10
  movaps 0x270(%rsp), %xmm11

  movq %rsp, %rdi                 # in place (dst == src0), 48 floats
  movq %rsp, %rsi
  leaq 0x100(%rsp), %rdx
  movl $48, %ecx
  call ff_vector_fmul_sse
  movaps 0x00(%rsp), %xmm12
  movaps 0xb0(%rsp), %xmm13

  leaq 0x100(%rsp), %rdi          # dst == src1, 16 floats
  leaq 0x200(%rsp), %rsi
  leaq 0x100(%rsp), %rdx
  movl $16, %ecx
  call ff_vector_fmul_sse
  movaps 0x100(%rsp), %xmm14
  movaps 0x130(%rsp), %xmm15

  movq $0, %rdi                   # stack addresses differ between the runs
  movq $0, %rsi
  movq $0, %rdx
  addq $0x300, %rsp
  jmp end

ff_vector_fmul_sse:
    lea -0x40(,%ecx,4),%rcx
    nop
    nop
    nop
    nop
    nop
    nop
    nop
.loop:
    movaps (%rsi,%rcx,1),%xmm0
    movaps 0x10(%rcx,%rsi,1),%xmm1
    mulps (%rdx,%rcx,1),%xmm0
    mulps 0x10(%rcx,%rdx,1),%xmm1
    movaps %xmm0,(%rdi,%rcx,1)
    movaps %xmm1,0x10(%rcx,%rdi,1)
    movaps 0x20(%rcx,%rsi,1),%xmm0
    movaps 0x30(%rcx,%rsi,1),%xmm1
    mulps 0x20(%rcx,%rdx,1),%xmm0
    mulps 0x30(%rcx,%rdx,1),%xmm1
    movaps %xmm0,0x20(%rcx,%rdi,1)
    movaps %xmm1,0x30(%rcx,%rdi,1)
    sub $0x40,%rcx
    jge .loop
    ret
end:
