/-
MWE: grind aborts with "maximum recursion depth has been reached" when an
E-matching pattern has a numeral argument and the E-graph has a `Nat` term
`(c + k) % m` in which `c` is closed but not a numeral. Examples of such a `c`
are an opaque constant, or the payload of a fixed-width literal such as
`(Int64.toBitVec 32).toNat`.

Mechanism (traced with gdb on the toolchain below):
- E-matching checks a numeral pattern argument with `isDefEq` under
  `withReducibleAndInstances` (`EMatch.matchGroundPattern`). For the pattern
  `g #0 5` of `g_five` and the E-graph term `g 1 ((c + 1000) % 7)`, the check
  is `5 =?= (c + 1000) % 7`.
- `isDefEqProjInst` unfolds `%` to `Nat.mod`. Then `isDefEqNat` calls
  `reduceNat?`, which calls `reduceBinNatOp Nat.mod`, whose `withNatValue`
  calls `whnf (c + 1000)`.
- `c` is stuck, so `whnf` unfolds `Nat.add c 1000` to `Nat.succ (c + 999)`.
  Then `reduceNat?` tries to fold the `Nat.succ`: `reduceUnaryNatOp` calls
  `whnf (c + 999)` through `withNatValue`, and so on. The recursion is as deep
  as the numeral, about 2 levels of `maxRecDepth` per unit, only to return
  `Nat.succ (c + 999)`. The `#eval` at the end shows this with `whnf` alone.
- `withNatValue` gives up at once on a term with free variables, so a local
  `c` does not trigger the recursion. A bare `c + k` (no `%`) does not trigger
  it either: `isDefEqOffset` decides `5 =?= c + 1000` without reducing.

When `k = 2^63`, no `maxRecDepth` helps. With a very large limit (say 10^8),
the whole `grind` call instead fails with "(deterministic) timeout at
`isDefEq`, maximum number of heartbeats (200000) has been reached". So grind
fails on goals that it otherwise proves at once.

This is how the problem showed up in kraken. Signed comparisons are stated as
`(a.toNat + 2^63) % 2^64 < (b.toNat + 2^63) % 2^64`
(`BitVec.toInt_lt_toInt_iff_flip`), and an immediate `b` reaches grind as
`Int64.toBitVec 32`. The lemma `UInt64.lt_size` (`x.toNat < 2 ^ 64`, tagged
`@[grind .]`) gets the normalized pattern `x.toNat ≤ 18446744073709551615`.
grind compares that numeral with the right-hand side of every `≤` on `Nat` in
the E-graph.

Workaround in kraken (`MachineWP.lean`): a `grind norm` rule that rewrites
`Int64.toBitVec (OfNat.ofNat n)` to `BitVec.ofNat 64 n`. The payload then
becomes a numeral before it reaches the E-graph (last grind example below).

Repro: lean grind-int64-recdepth-mwe.lean
  (toolchain leanprover/lean4-pr-releases:pr-release-15067)
Expected: each example marked FAILS prints a `grind` failure whose diagnostics
contain
  [issue] maximum recursion depth has been reached
and the `#eval` fails with the same message. The examples marked PASSES
succeed.
-/
import Lean -- only for the `whnf` demonstration at the end

set_option linter.unusedVariables false

opaque c : Nat

def g (x y : Nat) : Nat := if y = 5 then x else 0

@[grind =] theorem g_five (x : Nat) : g x 5 = x := by simp [g]

-- FAILS, although the hypothesis is irrelevant and `g_five` proves the goal.
example (h : g 1 ((c + 1000) % 7) = 3) : g 2 5 = 2 := by
  grind

-- FAILS with any recursion limit: the numeral is too large.
set_option maxRecDepth 100000 in
example (h : g 1 ((c + 2 ^ 63) % 2 ^ 64) = 3) : g 2 5 = 2 := by
  grind

-- FAILS: the payload of a fixed-width literal is also closed but not a numeral.
example (h : g 1 (((Int64.toBitVec 32).toNat + 1000) % 7) = 3) : g 2 5 = 2 := by
  grind

-- PASSES: no hypothesis.
example : g 2 5 = 2 := by
  grind

-- PASSES: a local variable in place of the closed term.
example (c : Nat) (h : g 1 ((c + 1000) % 7) = 3) : g 2 5 = 2 := by
  grind

-- PASSES: no `%`.
example (h : g 1 (c + 1000) = 3) : g 2 5 = 2 := by
  grind

-- PASSES: a `BitVec` literal in place of the `Int64` one (the normalizer folds
-- `(32#64).toNat` to `32`).
example (h : g 1 (((32#64).toNat + 1000) % 7) = 3) : g 2 5 = 2 := by
  grind

/-- The kraken workaround: turn the payload of an `Int64` literal into a
numeral (`no_index` lets the rule match the numeral). -/
theorem Int64.toBitVec_ofNat_norm (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toBitVec = BitVec.ofNat 64 n := rfl

section
attribute [local grind norm] Int64.toBitVec_ofNat_norm

-- PASSES: the third example again, with the workaround.
example (h : g 1 (((Int64.toBitVec 32).toNat + 1000) % 7) = 3) : g 2 5 = 2 := by
  grind
end

-- FAILS: `whnf (c + 1000)` alone recurses about 1000 levels deep (a
-- `maxRecDepth` of 2100 is enough, 1900 is not), only to return
-- `(c.add 999).succ`.
open Lean Meta Elab Term in
#eval show TermElabM Unit from do
  let e ← instantiateMVars (← elabTerm (← `((c + 1000 : Nat))) none)
  logInfo m!"{← whnf e}"
