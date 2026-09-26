/-
The instruction dictionary of the separation-logic wp. Each spec is a triple
of one directive with a small footprint. A register write carries the
schematic post to the updated registers. A memory instruction owns the slot's
bytes, and its pure conjunct is the post entailment: the schematic post holds
of the slot as the instruction leaves it, at the registers and flags the
instruction produces. `SepWP.cons_spec` sequences the specs, and the frame
rule of `vcgen` carries the rest of the memory past each instruction.

Every proof runs the same route: `SepWP.sep_intro` opens the triple under an
ambient frame, the `Mem.*_sep` lemmas of Kraken/SeparationMem.lean step the
machine memory under that frame, and the run ends at the directive's end.
-/
import Kraken.SepWP
import Kraken.SeparationMem
import Kraken.X64.Parser

open Std.WP
open Lean.Order
open Kraken.X64.Parser
open scoped SepWP

/-! ## Assertion-level plumbing -/

/-- Rotate the middle assertion out: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem MProp.sep_left_comm {w : Nat} (P Q R : MProp w) :
    P ∗ (Q ∗ R) = Q ∗ (P ∗ R) :=
  Std.ExtHashMap.sep_comm_l P Q R

/- `AddrExpr.zeroExtend_interp_base_disp`, the address of a `disp(base)`
expression, lives in Kraken/MachineWP.lean, whose instruction dictionary uses
it too. -/


/-- The address a `disp(base, index, 8)` expression computes, at 64-bit
address size: the base plus eight times the index plus the displacement. -/
theorem AddrExpr.zeroExtend_interp_sib [L : Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 8 + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

namespace SepWP

variable [CodeEnv] {p : Program}
  {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
  {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}

/-! ## The store -/

/-- Store a 64-bit register at `disp(base)`. The footprint is the slot's old
bytes. The pure conjunct is the post entailment: the schematic post holds of
the slot with the register's bytes, at the unchanged registers and flags. -/
@[spec] theorem mov_store_reg_spec (b : Reg64) (d : Int64) (rs : Reg64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (r.get64 rs).toInt).AtM (r.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  have hstore := Mem.storeInt_sep (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 bs F s.dmem
    ⟨hown, hlen⟩ (s.regs.get64 rs).toInt
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low64,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  have hnew : ((Int.toBytes 8 (s.regs.get64 rs).toInt).AtM
      (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F)
      (Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 (s.regs.get64 rs).toInt) :=
    hstore
  rw [MProp.sep_comm] at hnew
  exact MProp.sep_mono_right F hpost _ hnew

/-- Store an immediate at `disp(base)`. -/
@[spec] theorem mov_store_imm_spec (b : Reg64) (d : Int64) (i : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt).AtM
            (r.get64 b + BitVec.ofInt 64 d.toInt) ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  have hstore := Mem.storeInt_sep (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8 bs F s.dmem
    ⟨hown, hlen⟩ (BitVec.setWidth 64 i.toBitVec).toInt
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
    RegOrMem.interp, MachineData.set, MachineData.store,
    AddrExpr.zeroExtend_interp_base_disp, hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  have hnew : ((Int.toBytes 8 (BitVec.setWidth 64 i.toBitVec).toInt).AtM
      (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F)
      (Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
        (BitVec.setWidth 64 i.toBitVec).toInt) := hstore
  rw [MProp.sep_comm] at hnew
  exact MProp.sep_mono_right F hpost _ hnew

/-- Store a 64-bit register at `disp(base, index, 8)`. -/
@[spec] theorem mov_store_reg_sib_spec (b i : Reg64) (d : Int64) (rs : Reg64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun r z f =>
        ⌜(Int.toBytes 8 (r.get64 rs).toInt).AtM
            (r.get64 b + r.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⊑ Q () r z f⌝
          ⊓ bs.AtM (r.get64 b + r.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt)
      ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  have hstore := Mem.storeInt_sep (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt)
    8 bs F s.dmem ⟨hown, hlen⟩ (s.regs.get64 rs).toInt
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, Reg64s.get_low64,
    AddrExpr.zeroExtend_interp_sib, hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  have hnew : ((Int.toBytes 8 (s.regs.get64 rs).toInt).AtM
      (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) ∗ F)
      (Mem.storeInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8
        (s.regs.get64 rs).toInt) := hstore
  rw [MProp.sep_comm] at hnew
  exact MProp.sep_mono_right F hpost _ hnew

end SepWP

namespace SepWP

variable [CodeEnv] {p : Program}
  {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
  {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}

/-- The empty program: its wp is the postcondition. -/
@[spec] theorem nil_spec :
    ⦃ fun rg z f => Q () rg z f ⦄ ([] : Program) ⦃ Q; E ⦄ := by
  refine SepWP.sep_intro fun F s hpre => ?_
  intro pc _
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-! ## Register instructions

A register instruction owns no memory: its sep spec is the machine spec's
record update, componentwise, with the wp of the tail at the updated
registers and flags. -/

/-- Load an immediate into a 64-bit register. -/
@[spec] theorem mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun rg z f => Q () (rg.set64 r (BitVec.setWidth 64 i.toBitVec)) z f ⦄
      Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.set_low64, Effects.All,
    Kraken.Executable.after]
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-- Copy a 64-bit register. -/
@[spec] theorem mov_reg_reg_spec (rd rs : Reg64) :
    ⦃ fun rg z f => Q () (rg.set64 rd (rg.get64 rs)) z f ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64)))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
    Kraken.Executable.after]
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-- Load the address `disp(base, index, 8)` into a register. -/
@[spec] theorem lea_sib_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun rg z f => Q () (rg.set64 rd (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt)) z f ⦄
      Directive.instr (.regular .W64 .W64
          (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
    Reg64s.set_low64, AddrExpr.zeroExtend_interp_sib, Effects.All, Kraken.Executable.after]
  exact Eventually.done _ (Or.inl ⟨rfl, hpre⟩)

/-! ## The load

`add` from memory reads the slot and leaves it in place. The pure conjunct is
the post entailment: the schematic post holds of the unchanged slot, at the
registers and flags after the addition of the loaded value `Int.ofBytes bs`. -/

/-- Load the 64-bit value at `disp(base)` into a register. -/
@[spec] theorem mov_reg_mem_spec (rd b : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z f =>
        ⌜bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd (BitVec.ofInt 64 (Int.ofBytes bs))) z f⌝
          ⊓ bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  rw [MProp.sep_comm] at hown
  exact MProp.sep_mono_right F hpost _ hown

/-- Load the 64-bit value at `disp(base, index, 8)` into a register. -/
@[spec] theorem mov_reg_mem_sib_spec (rd b i : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z f =>
        ⌜bs.AtM (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd (BitVec.ofInt 64 (Int.ofBytes bs))) z f⌝
          ⊓ bs.AtM (rg.get64 b + rg.get64 i * 8 + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt)
      ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low64, AddrExpr.zeroExtend_interp_sib,
    hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  rw [MProp.sep_comm] at hown
  exact MProp.sep_mono_right F hpost _ hown

/-- Add the 64-bit value at `disp(base)` into a register. -/
@[spec] theorem add_reg_mem_spec (rd b : Reg64) (d : Int64)
    (bs : List UInt8) (hlen : bs.length = 8) :
    ⦃ fun rg z f =>
        let a := BitVec.ofInt 64 (Int.ofBytes bs)
        let bv := rg.get64 rd
        let v := a + bv
        ⌜bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt)
            ⊑ Q () (rg.set64 rd v) z
                (StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + bv.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (bv.take 4).unsigned,
                    of := v.signed != a.signed + bv.signed })⌝
          ⊓ bs.AtM (rg.get64 b + BitVec.ofInt 64 d.toInt) ⦄
      Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64))
            (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q ⦄ := by
  refine SepWP.triple_directive.mpr (SepWP.sep_intro fun F s hpre => ?_)
  obtain ⟨mf, mm, hunion, hinter, hF, hM⟩ := hpre
  obtain ⟨hpost, hbs⟩ := (MProp.meet_apply _ _ mm).mp hM
  have hpost := (MProp.ofProp_apply_iff _ mm).mp hpost
  have hown : (bs.AtM (s.regs.get64 b + BitVec.ofInt 64 d.toInt) ∗ F) s.dmem :=
    ⟨mm, mf, by rw [← hunion]; exact (Std.ExtHashMap.union_comm_of_disjoint mf mm hinter).symm,
      Std.ExtHashMap.disjoint_symm hinter, hbs, hF⟩
  have hload : Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
      = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs _ 8 F s.dmem hown hlen (by decide)
  intro pc hpl
  obtain ⟨zz, rest, hseg, -⟩ := hpl
  rw [Kraken.Executable.after_cons_of_not_label rfl hseg]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get_low64, Reg64s.set_low64, AddrExpr.zeroExtend_interp_base_disp,
    hload, Effects.All, Kraken.Executable.after]
  refine Eventually.done _ (Or.inl ⟨rfl, ?_⟩)
  rw [MProp.sep_comm] at hown
  exact MProp.sep_mono_right F hpost _ hown

end SepWP
