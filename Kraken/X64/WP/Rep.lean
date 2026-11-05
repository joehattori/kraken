module

public import Kraken.X64.WP.Loop
public import Kraken.X64.WP.Basic

open Classical

@[simp]
public theorem setReg_status {w : Width} (s : MachineData) (r : Reg w) (v : BitVec w.bits) :
    (s.setReg r v).status = s.status := rfl

@[simp]
public theorem strStep_64_df_false {s : MachineData} {r : Reg64} {w : Width}
    (hdf : s.status.df = false := by rfl) :
    s.strStep r w .W64 = s.setReg (Reg.low r .W64) (s.regs.get (Reg.low r .W64) + w.bytesv) := by
  simp [MachineData.strStep, hdf]

@[simp]
public theorem strStep_64_qword_false {s : MachineData} {r : Reg64}
    (hdf : s.status.df = false := by rfl) :
    s.strStep r .W64 .W64 = s.setReg (Reg.low r .W64) (s.regs.get (Reg.low r .W64) + 8#64) := by
  simp [MachineData.strStep, hdf, Width.bytesv, Width.bytes]

/-- When `%rcx = 0`, `repe cmpsq` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repe_cmpsq_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hi : p[i]? = some (.instr (.regular .W64 .W64 (.cmps (some .e)))))
    {s : MachineData} (hrcx : s.regs.get64 .rcx = 0#64)
    (hcont : Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ := by
  refine Program.loop_of_interp hi ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp]
  have hget : s.regs.get (Reg.low .rcx .W64) = 0#64 := by
    simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Width.bits]
    rw [hrcx]; rfl
  simp only [hget, Effects.All]
  exact hcont
