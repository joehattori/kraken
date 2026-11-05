module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-! Concrete-evaluation tests of semantics that the native asm tests can't observe. -/

private partial def accessChecks :
    Effects → Option (List (Nat × Nat) × List (Nat × Nat))
  | .done _ => some ([], [])
  | .require_read_access p ok => (accessChecks (ok ())).map fun (rs, ws) => ((p.lower.val, p.upper.val) :: rs, ws)
  | .require_write_access p ok => (accessChecks (ok ())).map fun (rs, ws) => (rs, (p.lower.val, p.upper.val) :: ws)
  | _ => none

private partial def runEffects : Effects → Option MachineData
  | .done ⟨s, _⟩ => some s
  | .require_read_access _ ok => runEffects (ok ())
  | .require_write_access _ ok => runEffects (ok ())
  | .require_exec_access _ ok => runEffects (ok ())
  | _ => none

/-- 64 bytes of data memory at `0x1000`. -/
private def s : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }

#guard accessChecks (s.loadAvx 0x1000 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1010)], [])
#guard accessChecks (s.loadAvx 0x1000 .W256 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1020)], [])
#guard accessChecks (s.loadAvx 0x1000 .W512 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1040)], [])
#guard accessChecks (s.storeAvx (w := .W128) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1010)])
#guard accessChecks (s.storeAvx (w := .W256) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1020)])
#guard accessChecks (s.storeAvx (w := .W512) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1040)])

#guard ([Width.W8, .W16, .W32, .W64].all fun w =>
  accessChecks (s.load 0x1000 w fun _ s => .done ⟨s, 0⟩) ==
    some ([(0x1000, 0x1000 + w.bytes)], []) &&
  accessChecks (s.store (w := w) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
    some ([], [(0x1000, 0x1000 + w.bytes)]))

#guard accessChecks (s.loadAvx 0x1001 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1001, 0x1011)], [])
#guard match s.loadAvx 0x1001 .W128 (fun _ s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false
#guard match s.storeAvx (w := .W128) 0x1001 0 (fun s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false

private def wrapping : MachineData :=
  { dmem := (List.replicate 64 0).At 0xfffffffffffffff8 }

#guard accessChecks (wrapping.load 0xffffffffffffffff .W8 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xffffffffffffffff, UInt64.size)], [])
#guard accessChecks (wrapping.loadAvx 0xfffffffffffffff8 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xfffffffffffffff8, UInt64.size), (0, 8)], [])
#guard accessChecks (wrapping.storeAvx (w := .W128) 0xfffffffffffffff8 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0xfffffffffffffff8, UInt64.size), (0, 8)])

#guard
  let _ : Labels := { label _ := 0 }
  match Operation.interp (w := .W64) (address_size := .mk .W64) .std ⟨0, 1⟩ {} (fun s => Effects.done ⟨s, 1⟩) (fun _ _ => Effects.done ⟨{}, 0⟩) with
  | .done ⟨s, _⟩ => s.status.df == true
  | _ => false

#guard
  let _ : Labels := { label _ := 0 }
  match Operation.interp (w := .W64) (address_size := .mk .W64) .cld ⟨0, 1⟩ { status := { (default : StatusFlags) with df := true } } (fun s => Effects.done ⟨s, 1⟩) (fun _ _ => Effects.done ⟨{}, 0⟩) with
  | .done ⟨s, _⟩ => s.status.df == false
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.jrcxz "target") ⟨0, 1⟩ {} (fun _ => Effects.done ⟨{}, 0⟩) (fun tgt _ => Effects.done ⟨{}, tgt⟩) with
  | .done ⟨_, tgt⟩ => tgt == 42
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  let s : MachineData := ({} : MachineData).setReg (Reg.low .rcx .W64) 1
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.jrcxz "target") ⟨0, 1⟩ s (fun _ => Effects.done ⟨{}, 0⟩) (fun tgt _ => Effects.done ⟨{}, tgt⟩) with
  | .done ⟨_, tgt⟩ => tgt == 0
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  let s : MachineData := ({} : MachineData).setReg (Reg.low .rcx .W64) 2
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.loop none "target") ⟨0, 1⟩ s (fun _ => Effects.done ⟨{}, 0⟩) (fun tgt s' => Effects.done ⟨s', tgt⟩) with
  | .done ⟨s', tgt⟩ => tgt == 42 && s'.regs.get (Reg.low .rcx .W64) == 1
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  let s : MachineData := ({} : MachineData).setReg (Reg.low .rcx .W64) 1
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.loop none "target") ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun tgt _ => Effects.done ⟨{}, tgt⟩) with
  | .done ⟨s', tgt⟩ => tgt == 0 && s'.regs.get (Reg.low .rcx .W64) == 0
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  let s : MachineData := { ({} : MachineData).setReg (Reg.low .rcx .W64) 2 with status := { (default : StatusFlags) with zf := true } }
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.loop (some .e) "target") ⟨0, 1⟩ s (fun _ => Effects.done ⟨{}, 0⟩) (fun tgt s' => Effects.done ⟨s', tgt⟩) with
  | .done ⟨_, tgt⟩ => tgt == 42
  | _ => false

#guard
  let _ : Labels := { label _ := 42 }
  let s : MachineData := { ({} : MachineData).setReg (Reg.low .rcx .W64) 2 with status := { (default : StatusFlags) with zf := false } }
  match Operation.interp (w := .W64) (address_size := .mk .W64) (.loop (some .e) "target") ⟨0, 1⟩ s (fun _ => Effects.done ⟨{}, 0⟩) (fun tgt s' => Effects.done ⟨s', tgt⟩) with
  | .done ⟨_, tgt⟩ => tgt == 0
  | _ => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }
  let s := (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.movs false) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.regs.get (Reg.low .rsi .W64) == 0x1001 &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1021
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }
  let s := { (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020 with status := { (default : StatusFlags) with df := true } }
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.movs false) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.regs.get (Reg.low .rsi .W64) == 0x0fff &&
    s'.regs.get (Reg.low .rdi .W64) == 0x101f
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }
  let s := (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.movs true) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.regs.get (Reg.low .rcx .W64) == 0 &&
    s'.regs.get (Reg.low .rsi .W64) == 0x1000
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0x42).At 0x1000 }
  let s := (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.cmps none) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.status.zf == true &&
    s'.regs.get (Reg.low .rsi .W64) == 0x1001 &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1021
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 32 (0x42 : UInt8) ++ List.replicate 32 (0x43 : UInt8)).At 0x1000 }
  let s := (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.cmps none) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.status.zf == false &&
    s'.regs.get (Reg.low .rsi .W64) == 0x1001 &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1021
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }
  let s := (base.setReg (Reg.low .rsi .W64) 0x1000).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.cmps (some .e)) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.regs.get (Reg.low .rcx .W64) == 0 &&
    s'.regs.get (Reg.low .rsi .W64) == 0x1000
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0x42).At 0x1000 }
  let s := (base.setReg (Reg.low .rax .W8) 0x42).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.scas none) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.status.zf == true &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1021
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0x43).At 0x1000 }
  let s := (base.setReg (Reg.low .rax .W8) 0x42).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.scas none) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.status.zf == false &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1021
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }
  let s := (base.setReg (Reg.low .rax .W8) 0x42).setReg (Reg.low .rdi .W64) 0x1020
  match runEffects (Operation.interp (w := .W8) (address_size := .mk .W64) (.scas (some .e)) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩) (fun _ _ => Effects.done ⟨{}, 1⟩)) with
  | some s' =>
    s'.regs.get (Reg.low .rcx .W64) == 0 &&
    s'.regs.get (Reg.low .rdi .W64) == 0x1020
  | none => false

/-- Like `runEffects`, but resolves every `undefined` choice with `h` (all zeros or all ones for
`h = 0` or `h = -1`), so a value that differs between the two is undefined. -/
private partial def runEffectsWith (h : UInt64) : Effects → Option MachineData
  | .done ⟨s, _⟩ => some s
  | .require_read_access _ ok => runEffectsWith h (ok ())
  | .require_write_access _ ok => runEffectsWith h (ok ())
  | .require_exec_access _ ok => runEffectsWith h (ok ())
  | @Effects.undefined _ t cont => runEffectsWith h (cont (t.from_hash h))
  | _ => none

/-- `bsfl %eax, %ecx` from a state with `%eax = src` and `%rcx = 42`. -/
private def bsfl (src : BitVec 32) (h : UInt64) : Option MachineData :=
  let _ : Labels := { label _ := 0 }
  let s := ({} : MachineData).setReg (Reg.low .rax .W32) src |>.setReg (Reg.low .rcx .W64) 42
  runEffectsWith h (Operation.interp (w := .W32) (address_size := .mk .W64)
    (.bsf (.low .rcx .W32) (.reg (.low .rax .W32))) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩)
    (fun _ _ => Effects.done ⟨{}, 1⟩))

-- Nonzero source: the destination is the index of the lowest set bit, and ZF is clear.
#guard [0, -1].all fun h => match bsfl 0x08 h with
  | some s' => s'.status.zf == false && s'.regs.get64 .rcx == 3
  | none => false

-- Zero source: ZF is set, and the whole destination register is undefined.
#guard match bsfl 0 0, bsfl 0 (-1) with
  | some s₀, some s₁ => s₀.status.zf && s₁.status.zf &&
      s₀.regs.get64 .rcx == 0 && s₁.regs.get64 .rcx == -1
  | _, _ => false

-- CF, OF, SF, AF, and PF are undefined.
#guard match bsfl 0x08 0, bsfl 0x08 (-1) with
  | some s₀, some s₁ => !s₀.status.cf && s₁.status.cf && !s₀.status.of && s₁.status.of &&
      !s₀.status.sf && s₁.status.sf && !s₀.status.af && s₁.status.af &&
      !s₀.status.pf && s₁.status.pf
  | _, _ => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := {}
  let s := base.setAvxReg (.ymm .mm0) (0x42#256)
  match runEffects (AvxOperation.interp (w := .W256) (address_size := .mk .W64) (.vpbroadcastb (.ymm .mm1) (.ymm .mm0)) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩)) with
  | some s' =>
    (s'.zmms.get (.ymm .mm1)).lane 8 0 == 0x42 &&
    (s'.zmms.get (.ymm .mm1)).lane 8 31 == 0x42
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := {}
  let s := base.setAvxReg (.ymm .mm0) (0x1234#256)
  match runEffects (AvxOperation.interp (w := .W256) (address_size := .mk .W64) (.vpbroadcastw (.ymm .mm1) (.ymm .mm0)) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩)) with
  | some s' =>
    (s'.zmms.get (.ymm .mm1)).lane 16 0 == 0x1234 &&
    (s'.zmms.get (.ymm .mm1)).lane 16 15 == 0x1234
  | none => false

#guard
  let _ : Labels := { label _ := 0 }
  let base : MachineData := {}
  let s := (base.setAvxReg (.ymm .mm0) (0x12341234#256)).setAvxReg (.ymm .mm1) (0x12345678#256)
  match runEffects (AvxOperation.interp (w := .W256) (address_size := .mk .W64) (.vpcmpeqw (.ymm .mm2) (.ymm .mm0) (.avx (.ymm .mm1))) ⟨0, 1⟩ s (fun s' => Effects.done ⟨s', 0⟩)) with
  | some s' =>
    (s'.zmms.get (.ymm .mm2)).lane 16 0 == 0 &&
    (s'.zmms.get (.ymm .mm2)).lane 16 1 == 0xFFFF
  | none => false





