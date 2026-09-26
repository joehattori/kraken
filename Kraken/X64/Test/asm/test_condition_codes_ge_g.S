# Test: the signed condition codes ge and g (setge/setnl, setg/setnle,
# jge/jnl, jg/jnle), including cases where signed overflow makes sf differ
# from of.

  movq $0, %rax
  movq $0, %rbx
  movq $0, %rcx
  movq $0, %rdx
  movq $0, %rsi
  movq $0, %rdi
  movq $0, %r8
  movq $0, %r9
  movq $0, %r10
  movq $0, %r11
  movq $0, %r12
  movq $0, %r13

  # 1 - 2: sf=1, of=0, so neither ge nor g
  movq $1, %r14
  movq $2, %r15
  cmpq %r15, %r14
  setge %al
  setg %bl

  # 5 - 5: zf=1, so ge but not g
  movq $5, %r14
  movq $5, %r15
  cmpq %r15, %r14
  setnl %cl
  setnle %dl

  # INT64_MIN - 1 overflows to a positive value: sf=0, of=1, so neither
  movabsq $0x8000000000000000, %r14
  movq $1, %r15
  cmpq %r15, %r14
  setge %sil
  setg %dil

  # INT64_MAX - (-1) overflows to a negative value: sf=1, of=1, so both
  movabsq $0x7fffffffffffffff, %r14
  movq $-1, %r15
  cmpq %r15, %r14
  setge %r8b
  setg %r9b

  # 32-bit: 0x7fffffff - 0x80000000 overflows: sf=1, of=1, so both
  movl $0x7fffffff, %r14d
  movl $0x80000000, %r15d
  cmpl %r15d, %r14d
  setge %r10b
  setg %r11b

  # Branches: count the taken ones in r12 and the fallthroughs in r13
  movq $3, %r14
  movq $-7, %r15
  cmpq %r15, %r14      # 3 - (-7)
  jge l1
  addq $1, %r13
l1:
  addq $1, %r12
  cmpq %r14, %r15      # -7 - 3
  jg l2
  addq $1, %r13
l2:
  cmpq %r14, %r14
  jnl l3
  addq $100, %r13
l3:
  addq $1, %r12
  cmpq %r14, %r14
  jnle l4
  addq $1, %r13
l4:
  movabsq $0x8000000000000000, %r14
  movq $1, %r15
  cmpq %r15, %r14      # INT64_MIN - 1: less, despite sf=0
  jge l5
  addq $1, %r13
l5:
  movq $0, %r14
  movq $0, %r15
