# Undefined flags: cf, pf, af, sf, of

# Test bsf. Every source is nonzero: with a zero source the destination is undefined.
movl $0x80, %eax
bsfl %eax, %ebx
movq $1, %rax
shlq $63, %rax
bsfq %rax, %rsi
subq $16, %rsp
movq $0x10000000100, %rcx
movq %rcx, (%rsp)
bsfl (%rsp), %ecx
bsfq (%rsp), %rdx
