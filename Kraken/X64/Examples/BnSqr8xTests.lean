import Kraken.X64.Examples.BnSqr8xInternal
import Kraken.X64.Examples.BnSqr8xSpec

private def limbs (n a : Nat) : List (BitVec 64) :=
  (List.range n).map fun i => BitVec.ofNat 64 (a / (2 ^ 64) ^ i)

private def negInverse (m : BitVec 64) : BitVec 64 :=
  -((List.range 6).foldl (fun x _ => x * (2 - m * x)) 1)

private def fixture (x m : List (BitVec 64)) (n0 : BitVec 64) : MachineData :=
  let bytes := 8 * x.length
  let mem : DataMem := (List.replicate (2 * bytes + 64) (0xa5 : UInt8)).At 0x1000
  { regs := { rsp := 0x1000, rsi := 0x10000, r9 := bytes.toUInt64,
              r10 := UInt64.ofBitVec (-(BitVec.ofNat 64 bytes)) }
    zmms := { zmm2 := BitVec.ofNat 512 0x20000,
              zmm3 := (-(BitVec.ofNat 64 bytes)).zeroExtend 512 }
    dmem := ((((mem).storeInt
      0x1000 8 0x80000000).storeInt (0x1000 + 40) 8 n0.toInt).storeBytes 0x10000
      (x.flatMap fun w => Int.toBytes 8 w.toInt)).storeBytes 0x20000
      (m.flatMap fun w => Int.toBytes 8 w.toInt) }

private def check (blocks a m : Nat) : IO Unit := do
  let n := 8 * blocks
  let x := limbs n a
  let modulus := limbs n m
  let n0 := negInverse (modulus.getD 0 0)
  unless (modulus.getD 0 0) * n0 + 1 == 0 do throw <| IO.userError "bad inverse"
  let d := fixture x modulus n0
  let r := bnSqr8xResult d x modulus n0 blocks
  let out := { d with dmem := r.memory, regs := d.regs.set64 .rax r.carry }
  let some y := BnSqr8x.outputValue (d.regs.get64 .rsp) n out
    | throw <| IO.userError "unmapped fold output"
  unless BnSqr8x.checkSquare x modulus y do
    throw <| IO.userError s!"bad fold: blocks={blocks}, A={a}, M={m}, Y={y}"
  let e := bn_sqr8x_internal_prog.fakeLayout
  let .ok (s, _) := e.eval (d, e.labels.label "__bn_sqr8x_internal") (fun s => s.2 == 0x80000000)
    | throw <| IO.userError "interpreter failed"
  unless BnSqr8x.outputValue (d.regs.get64 .rsp) n s == some y do
    throw <| IO.userError "interpreter disagrees"
  if r.carry != 0 then
    let some low := BnSqr8x.readLimbs r.memory (BnSqr8x.outputAddress (d.regs.get64 .rsp) n) n
      | throw <| IO.userError "unmapped low output"
    if BnSqr8x.checkSquare x modulus (BnSqr8x.limbsToNat low) then
      throw <| IO.userError "checker accepted an output with its high carry omitted"

-- These are executable regressions, not a proof for arbitrary input sizes.
-- Compare the actual instruction interpreter and the proved arithmetic fold
-- with the independent integer equation, including a nonzero scratch pattern.
-- The sizes cover no-tail reduction, one tail block, and multiple tail blocks.
#eval do
  for blocks in [1, 2, 3, 4] do
    let r := BnSqr8x.radix (8 * blocks)
    for a in [0, 1, r - 1, r - 2, r / 2] do
      for m in [r - 1, r - 3, r / 2 + 1, 1] do
        check blocks a m

-- Reject an incorrect result and an absent output allocation explicitly.
#guard BnSqr8x.checkSquare (limbs 8 1) (limbs 8 (BnSqr8x.radix 8 - 1)) 0 = false
#guard BnSqr8x.outputValue 0x1000 8 ({} : MachineData) = none
