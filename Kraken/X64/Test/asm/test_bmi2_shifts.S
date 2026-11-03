# Test: BMI2 shifts (shlx, shrx, sarx)
# The count is masked to 5 bits (32-bit) or 6 bits (64-bit), 32-bit results are zero-extended,
# and the flags are left unchanged.

# Set the flags to a known state (CF = SF = AF = 1) that the shifts must preserve
movq $1, %r15
subq $2, %r15                    # r15 = -1

# ----- 32-bit, count 35 & 0x1f = 3 -----
movq $-1, %rax
movl $0x80000001, %ebx
movl $35, %ecx
shlxl %ecx, %ebx, %eax           # rax = 0x0000000000000008
movq $-1, %rdx
sarx %ecx, %ebx, %edx            # rdx = 0x00000000f0000000
movq $-1, %rsi
shrxl %ecx, %ebx, %esi           # rsi = 0x0000000010000000

# ----- 64-bit, count 67 & 0x3f = 3 -----
movq $0x8000000000000001, %rdi
movq $67, %r8
shlxq %r8, %rdi, %r9             # r9 = 0x0000000000000008
sarxq %r8, %rdi, %r10            # r10 = 0xf000000000000000
shrx %r8, %rdi, %r11             # r11 = 0x1000000000000000

# ----- Aliasing: dst = src, dst = cnt -----
movq $5, %r12
movq $2, %r13
shlxq %r13, %r12, %r12           # r12 = 20
sarxq %r13, %r12, %r13           # r13 = 20 >> 2 = 5
movl $-64, %ecx
sarxl %ecx, %ecx, %ecx           # count -64 & 0x1f = 0: rcx = 0x00000000ffffffc0

# ----- Memory source (the stack is filled with 0xff) -----
shrxq %r13, -8(%rsp), %r14       # r14 = 0x07ffffffffffffff
