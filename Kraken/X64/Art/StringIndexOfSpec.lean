module

public import Kraken.X64.WP
public import Kraken.X64.WP.Loop
public import Kraken.Layout
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.SeparationMem
import all Kraken.SeparationMem
public import Kraken.X64.Art.StringEquals

open Std
open Std.ExtHashMap

namespace Kraken.X64.Art

public section

/-- Individual UTF-16 code unit at character index `i` of the string payload. -/
@[expose] def strChar (count : BitVec 32) (data : List UInt8) (i : Nat) : Option (BitVec 16) :=
  if count.getLsbD 0 then
    match data[2 * i]?, data[2 * i + 1]? with
    | some lo, some hi => some ((lo.toBitVec.zeroExtend 16) ||| ((hi.toBitVec.zeroExtend 16) <<< 8))
    | _, _ => none
  else
    match data[i]? with
    | some b => some (b.toBitVec.zeroExtend 16)
    | none => none

/-- Extract the list of UTF-16 code units from the string payload. -/
@[expose] def strChars (count : BitVec 32) (data : List UInt8) : List (BitVec 16) :=
  (List.range (count >>> 1).toNat).filterMap (strChar count data)

/-- Java `String.indexOf(ch, fromIndex)` specification for BMP code points (`ch ≤ 0xFFFF`). -/
@[expose] def indexOfSpec (chars : List (BitVec 16)) (ch fromIndex : BitVec 32) : BitVec 32 :=
  let start := if fromIndex.slt 0 then 0 else fromIndex.toNat
  match (chars.drop start).findIdx? (fun c => c.zeroExtend 32 = ch) with
  | some i => BitVec.ofNat 32 (start + i)
  | none   => -1#32

/--
Specification postcondition on final state `t`:
- `out` contains `indexOfSpec chars ch fromIndex`.
- registers not in `out :: temps` are preserved from `s`.
- `dmem` is unchanged.
- `zmms` is either unchanged (`s.zmms`), or zeroUpper after vector writes.
-/
@[expose] def StringIndexOfPost (out : Reg64) (temps : List Reg64)
    (ymm1 ymm2 : AvxReg .W256)
    (chars : List (BitVec 16)) (ch fromIndex : BitVec 32) (s t : MachineData) : Prop :=
  let res : BitVec 32 := indexOfSpec chars ch fromIndex
  (t.regs.get (.low out .W32) = res) ∧
  (∀ r, r ∉ out :: temps → t.regs.get64 r = s.regs.get64 r) ∧
  t.dmem = s.dmem ∧
  (t.zmms = s.zmms ∨
   ∃ v1 v2, t.zmms = ((s.zmms.set ymm1 v1).set ymm2 v2).zeroUpper)

/-- Slow-path postcondition when `ch > 0xFFFF`: jumps to `slow` with unchanged state. -/
@[expose] def StringIndexOfSlow [Host] (slow : Label) (ch : BitVec 32) (s₀ : MachineData)
    (pc : Int64) (s : MachineData) : Prop :=
  pc = label slow ∧ ch.toNat > 0xFFFF ∧ s.regs = s₀.regs ∧ s.dmem = s₀.dmem ∧ s.zmms = s₀.zmms

end

end Kraken.X64.Art
