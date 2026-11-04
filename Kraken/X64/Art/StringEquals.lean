module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
import Kraken.X64.Parser
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem

namespace Kraken.X64.Art

/-- ART `String.count_`: length << 1 | flag, flag 0 = compressed (1B/char), 1 = uncompressed (2B/char). -/
def strByteLen (count : BitVec 32) : Nat :=
  if count.getLsbD 0 then 2 * (count >>> 1).toNat else (count >>> 1).toNat

/-- Zero-padded byte count in the string object (`kObjectAlignment = 8`). -/
def padBytes (len : Nat) : Nat := (8 - (len % 8)) % 8

/-- Total allocated data bytes of the string, including 8-byte zero-padding. -/
def allocatedBytes (len : Nat) : Nat := len + padBytes len

/-- Logical bytes of the string at address `base`. -/
def StringBytes (base : BitVec 64) (len : Nat) (m : Mem 64) : List UInt8 :=
  (List.range len).map fun i => (m[base + 16#64 + .ofNat 64 i]?).getD (0 : UInt8)

/--
A valid ART String object in memory `m` at address `p`:
1. `count_` field at `p + 8` matches `count`.
2. The data payload of `len` logical bytes and `padBytes len` zero padding bytes are present in `m`.
3. The padding bytes are all zeroes.
-/
def StringAt (p : BitVec 64) (count : BitVec 32) (m : Mem 64) : Prop :=
  let len := strByteLen count
  let pad := padBytes len
  (∃ c, m.loadInt (p + 8#64) 4 = some c ∧ BitVec.ofInt 32 c = count) ∧
  (∀ i < len + pad, (m[p + 16#64 + .ofNat 64 i]?).isSome) ∧
  (∀ i, len ≤ i ∧ i < len + pad → m[p + 16#64 + .ofNat 64 i]? = some (0 : UInt8))

/-- Java `String.equals` specification: two strings are equal iff their count fields and logical bytes match. -/
def stringEquals (s₁ s₂ : BitVec 64) (c₁ c₂ : BitVec 32) (m : Mem 64) : Bool :=
  s₁ == s₂ || (c₁ == c₂ && (StringBytes s₁ (strByteLen c₁) m == StringBytes s₂ (strByteLen c₂) m))

/-- Frame preservation: all non-temp GPRs unchanged, low 128 bits of vector registers unchanged. -/
def Agree (_str _arg n off out : Reg64) (_ymm : AvxReg .W256) (s t : MachineData) : Prop :=
  (∀ r : Reg64, r ∉ [n, off, out] → t.regs.get64 r = s.regs.get64 r) ∧
  t.dmem = s.dmem ∧
  (∀ r : RegMm, (t.zmms.get512 r).take 128 = (s.zmms.get512 r).take 128)

/--
Parameterized assembly template for AVX2 String.equals.
Uses vector register `ymm` and core registers `str`, `arg`, `n`, `off`, `out`.
-/
def stringEqualsProg (str arg n off out : Reg64) (ymm : AvxReg .W256) : _root_.Program := parse("
    # 1. Reference equality check: if str == arg return true
    cmpl %❰.low arg .W32❱, %❰.low str .W32❱
    je return_true

    # 2. Load and compare count_ fields: if count(str) != count(arg) return false
    movl 8(%❰str❱), %❰.low n .W32❱
    cmpl 8(%❰arg❱), %❰.low n .W32❱
    jne return_false

    # 3. If count == 0 return true
    testl %❰.low n .W32❱, %❰.low n .W32❱
    je return_true

    # 4. Convert count to byte length n: if bit 0 is 1 (uncompressed) then n &= ~1 else n >>= 1
    testl $1, %❰.low n .W32❱
    jne uncompressed
    shrl $1, %❰.low n .W32❱
    jmp len_done
  uncompressed:
    andl $-2, %❰.low n .W32❱
  len_done:

    # 5. off = 0
    xorq %❰.low off .W64❱, %❰.low off .W64❱

    # 6. Check if n >= 32
    cmpl $32, %❰.low n .W32❱
    jb short

  # 7. AVX loop: compare 32 bytes per iteration
  avx_loop:
    vmovdqu 16(%❰str❱,%❰off❱,1), %❰ymm❱
    vpcmpeqb 16(%❰arg❱,%❰off❱,1), %❰ymm❱, %❰ymm❱
    vpmovmskb %❰ymm❱, %❰.low out .W32❱
    cmpl $-1, %❰.low out .W32❱
    jne return_false_vzero
    addq $32, %❰.low off .W64❱
    subl $32, %❰.low n .W32❱
    cmpl $32, %❰.low n .W32❱
    jae avx_loop

  # 8. Short tail: qwords remaining = (n + 7) / 8
  short:
    addl $7, %❰.low n .W32❱
    shrl $3, %❰.low n .W32❱
    je return_true_vzero

  qword_loop:
    movq 16(%❰str❱,%❰off❱,1), %❰.low out .W64❱
    cmpq 16(%❰arg❱,%❰off❱,1), %❰.low out .W64❱
    jne return_false_vzero
    addq $8, %❰.low off .W64❱
    subl $1, %❰.low n .W32❱
    jne qword_loop

  # 9. Return true with vzeroupper
  return_true_vzero:
    vzeroupper
  return_true:
    movl $1, %❰.low out .W32❱
    jmp end

  # 10. Return false with vzeroupper
  return_false_vzero:
    vzeroupper
  return_false:
    xorl %❰.low out .W32❱, %❰.low out .W32❱
  end:
")

/--
Correctness theorem: `stringEqualsProg` satisfies its specification on any `Host` program.
-/
theorem stringEquals_correct [Host]
    (str arg n off out : Reg64) (ymm : AvxReg .W256)
    (h_distinct : [str, arg, n, off, out].Nodup)
    (c₁ c₂ : BitVec 32)
    (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i) :
    ∀ s : MachineData,
      StringAt (s.regs.get64 str) c₁ s.dmem →
      StringAt (s.regs.get64 arg) c₂ s.dmem →
      (stringEqualsProg str arg n off out ymm).wp
        (fun t =>
          (t.regs.get (.low out .W32) = if stringEquals (s.regs.get64 str) (s.regs.get64 arg) c₁ c₂ s.dmem then 1#32 else 0#32) ∧
          Agree str arg n off out ymm s t)
        (fun _ _ => False)
        s := by
  sorry

end Kraken.X64.Art
