import Kraken.X64.Semantics

/-!
# Mathematical specification of `__bn_sqr8x_internal`

Let `N = x.length = modulus.length`, `A = limbsToNat x`, `M = limbsToNat modulus`,
and `R = 2^(64*N)`. The routine accepts positive multiples of eight limbs.
It computes a Montgomery **square**: multiplication of `A` by itself, followed
by division by `R` modulo `M`. It has no second independent multiplicand.

The exact equation is `R * Y = A * A + M * Q` with `0 ≤ Q < R`.
`Y` includes the `N` output limbs and the extra high word returned in `rax`.
Consequently `R * Y ≡ A² (mod M)`; `Y` need not be less than `M`.
The caller's `__bn_post4x_internal` is outside this specification.

`MathematicalPost` states this equation directly in terms of returned memory and
registers. `checkSquare_iff` proves that `checkSquare` checks exactly the integer
equation for a positive modulus. In `BnSqr8xInternal.lean`,
`bn_sqr8x_internal_montgomery_square` proves this postcondition for the complete
assembly routine under `BnSqr8xContext`, including termination and return.
`BnSqr8xTests.lean` additionally checks concrete executions against the equation.
-/

namespace BnSqr8x

/-- Interpret unsigned 64-bit limbs as a natural number, least significant limb first. -/
def limbsToNat : List (BitVec 64) → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * limbsToNat ws

/-- Montgomery radix for `n` 64-bit limbs. -/
def radix (n : Nat) : Nat := 2 ^ (64 * n)

/-- The radix as the `n`-th power of the limb base, the form limb inductions use. -/
theorem radix_eq_pow (n : Nat) : radix n = (2 ^ 64) ^ n := Nat.pow_mul 2 64 n

/-- Output starts in the upper half of the original `2*N`-limb workspace.
`sp` is the stack pointer on entry, before `ret` increases it by eight bytes. -/
def outputAddress (sp : BitVec 64) (n : Nat) : BitVec 64 :=
  sp + 56 + BitVec.ofNat 64 (8 * n)

/-- Read little-endian limbs. An unmapped word makes the entire read fail. -/
def readLimbs (mem : DataMem) (a : BitVec 64) : Nat → Option (List (BitVec 64))
  | 0 => some []
  | n + 1 => do
    let w ← mem.loadInt a 8
    let ws ← readLimbs mem (a + 8) n
    some (BitVec.ofInt 64 w :: ws)

/-- Decode the full returned bignum, including the high word in `rax`.
The low `N` words alone are insufficient when the reduction produces a carry. -/
def outputValue (sp : BitVec 64) (n : Nat) (s : MachineData) : Option Nat := do
  let limbs ← readLimbs s.dmem (outputAddress sp n) n
  some (limbsToNat limbs + radix n * (s.regs.get64 .rax).toNat)

/-- The full value before the caller's conditional subtraction. -/
def MontgomerySquare (x modulus : List (BitVec 64)) (y : Nat) : Prop :=
  ∃ q < radix x.length,
    radix x.length * y = limbsToNat x * limbsToNat x + limbsToNat modulus * q

/-- Numerical postcondition proved for the complete routine. Calling-convention, memory-disjointness,
inverse-word, and size assumptions are supplied by `BnSqr8xContext`.
This definition does not assume that the arithmetic folds compute a square.

The returned value `Y` is a *Montgomery square* of `A`: the Montgomery product of
`A` with itself, `Y ≡ A * A * R⁻¹ (mod M)` with `R = radix N` (`M` is odd,
so `R` is invertible modulo `M`).

In Montgomery form a residue `a` is stored as `A = a * R mod M`, so squaring
`A` yields `a² * R² * R⁻¹ = a² * R`, the Montgomery form of `a²`. Dividing by `R`
instead of reducing modulo `M` lets the routine replace division by `M` with
shifts: it adds the multiple `M * Q` that clears the low `N` limbs of `A * A`
and keeps the high half, giving the exact equation `R * Y = A * A + M * Q`. -/
def MathematicalPost (sp : BitVec 64) (x modulus : List (BitVec 64))
    (s : MachineData) : Prop :=
  ∃ y, outputValue sp x.length s = some y ∧ MontgomerySquare x modulus y

/-- Executable check of the integer equation, without enumerating coefficients. -/
def checkSquare (x modulus : List (BitVec 64)) (y : Nat) : Bool :=
  let a := limbsToNat x
  let m := limbsToNat modulus
  let r := radix x.length
  let delta := r * y - a * a
  decide (0 < m ∧ a * a ≤ r * y ∧ delta % m = 0 ∧ delta / m < r)

/-- The executable check is equivalent to the mathematical specification for a
positive modulus. It is independent of the assembly-shaped arithmetic folds. -/
theorem checkSquare_iff (x modulus : List (BitVec 64)) (y : Nat) :
    checkSquare x modulus y = true ↔ 0 < limbsToNat modulus ∧ MontgomerySquare x modulus y := by
  simp only [checkSquare, decide_eq_true_eq, MontgomerySquare]
  constructor
  · rintro ⟨hm, ha, hd, hq⟩
    refine ⟨hm, (radix x.length * y - limbsToNat x * limbsToNat x) / limbsToNat modulus, hq, ?_⟩
    have he := Nat.mod_add_div (radix x.length * y - limbsToNat x * limbsToNat x) (limbsToNat modulus)
    omega
  · rintro ⟨hm, q, hq, he⟩
    have hd : radix x.length * y - limbsToNat x * limbsToNat x = limbsToNat modulus * q := by omega
    rw [hd]
    exact ⟨hm, by omega, by simp, by simpa [Nat.mul_div_cancel_left _ hm] using hq⟩

theorem limbsToNat_lt_radix (x : List (BitVec 64)) : limbsToNat x < radix x.length := by
  induction x with
  | nil => decide
  | cons w ws ih =>
    have hw := w.isLt
    simp only [limbsToNat, List.length_cons, radix_eq_pow, Nat.pow_succ] at *
    omega

/-- The exact equation implies the usual Montgomery congruence. -/
theorem MontgomerySquare.congruent {x modulus : List (BitVec 64)} {y : Nat}
    (h : MontgomerySquare x modulus y) :
    (radix x.length * y) % limbsToNat modulus = (limbsToNat x * limbsToNat x) % limbsToNat modulus := by
  obtain ⟨q, _, he⟩ := h
  rw [he, Nat.add_mod]
  simp

end BnSqr8x
