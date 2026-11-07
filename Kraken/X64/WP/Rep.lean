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

@[simp]
public theorem strStep_64_byte_false {s : MachineData} {r : Reg64}
    (hdf : s.status.df = false := by rfl) :
    s.strStep r .W8 .W64 = s.setReg (Reg.low r .W64) (s.regs.get (Reg.low r .W64) + 1#64) := by
  simp [MachineData.strStep, hdf, Width.bytesv, Width.bytes]

@[simp]
public theorem strStep_64_word_false {s : MachineData} {r : Reg64}
    (hdf : s.status.df = false := by rfl) :
    s.strStep r .W16 .W64 = s.setReg (Reg.low r .W64) (s.regs.get (Reg.low r .W64) + 2#64) := by
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

/-- When `%rcx = 0`, `repne scasb` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repne_scasb_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hi : p[i]? = some (.instr (.regular .W64 .W8 (.scas (some .ne)))))
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

/-- When `%rcx = 0`, `repne scasw` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repne_scasw_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hi : p[i]? = some (.instr (.regular .W64 .W16 (.scas (some .ne)))))
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

private theorem rep_get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.get64, Reg64s.set64] <;>
    first | rfl | exact BitVec.ofNat_toNat _

private theorem rep_get_low64 (s : Reg64s) (r : Reg64) :
    s.get (Reg.low r .W64) = s.get64 r := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Width.bits]
  ext i hi; simp

private theorem rep_set_low64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    s.set (Reg.low r .W64) v = s.set64 r v := rfl

private theorem rep_sub_beq_zero {w : Nat} (a b : BitVec w) : (a - b == 0#w) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0#w := fun h' => h (by
      have := BitVec.sub_add_cancel a b; rw [h', BitVec.zero_add] at this; exact this.symm)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

private theorem rep_ofNat64_succ_ne_zero {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == (0 : BitVec 64)) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  have h0' : (0 : BitVec 64).toNat = 0 := rfl
  rw [Nat.mod_eq_of_lt hlt, h0'] at this
  omega

private theorem rep_ofNat64_pred {n : Nat} :
    BitVec.ofNat 64 (n + 1) - (1 : BitVec 64) = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel (BitVec.ofNat 64 n) (1 : BitVec 64)

private theorem rep_all_require_exec (span : Std.Rco Int64) (ok : Unit → Effects)
    (post : MachineState → Prop) :
    (Effects.require_exec_access span ok).All post = (ok ()).All post := rfl

private theorem rep_zeroExtend_64 (x : BitVec 64) : BitVec.zeroExtend 64 x = x := by
  simp [BitVec.zeroExtend]

public theorem regs_cmps_rcx (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rcx = regs.get64 .rcx := by
  rw [rep_get64_set64, rep_get64_set64]; rfl

public theorem regs_cmps_rsi (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rsi = v_rsi := by
  rw [rep_get64_set64, rep_get64_set64]; rfl

public theorem regs_cmps_rdi (regs : Reg64s) (v_rsi v_rdi : BitVec 64) :
    ((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).get64 .rdi = v_rdi := by
  rw [rep_get64_set64]; rfl

public theorem regs_cmps_set64_rcx (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rcx = v_rcx := by
  rw [rep_get64_set64]; rfl

public theorem regs_cmps_set64_rsi (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rsi = v_rsi := by
  rw [rep_get64_set64, rep_get64_set64, rep_get64_set64]; rfl

public theorem regs_cmps_set64_rdi (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 .rdi = v_rdi := by
  rw [rep_get64_set64, rep_get64_set64]; rfl

public theorem regs_cmps_set64_other (regs : Reg64s) (v_rsi v_rdi v_rcx : BitVec 64)
    {r : Reg64} (hr : r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi]) :
    (((regs.set64 .rsi v_rsi).set64 .rdi v_rdi).set64 .rcx v_rcx).get64 r = regs.get64 r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
  simp only [rep_get64_set64, hr.1, hr.2.1, hr.2.2, ↓reduceIte]

/-- When `%rcx = 0`, `repe cmps` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repe_cmps_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {w : Width}
    (hi : p[i]? = some (.instr (.regular .W64 w (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} (hrcx : s.regs.get64 .rcx = 0#64)
    (hcont : Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ := by
  refine Program.loop_of_interp hi ?_
  dsimp only [Directive.interp, Instr.interp, Operation.interp]
  rw [rep_get_low64, hrcx]
  simp only [Effects.All]
  exact hcont

/-- When `%rcx = 0`, `repe cmpsb` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repe_cmpsb_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hi : p[i]? = some (.instr (.regular .W64 .W8 (.cmps (some .e)))))
    {s : MachineData} (hrcx : s.regs.get64 .rcx = 0#64)
    (hcont : Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_zero hi hrcx hcont

/-- When `%rcx = 0`, `repe cmpsw` terminates immediately without executing or modifying state. -/
public theorem Program.loop_repe_cmpsw_zero [Host] {p : Program} {H : Embedding p} {i : Nat}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hi : p[i]? = some (.instr (.regular .W64 .W16 (.cmps (some .e)))))
    {s : MachineData} (hrcx : s.regs.get64 .rcx = 0#64)
    (hcont : Program.LoopCont p H Q E ⟨s, Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_zero hi hrcx hcont

private theorem loop_repe_cmps_eq_aux [Host] {p : Program} {H : Embedding p} {i : Nat}
    {w : Width}
    (hi : p[i]? = some (.instr (.regular .W64 w (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (rsi0 rdi0 : BitVec 64) (f g : Nat → BitVec w.bits)
    (m : Nat) :
    ∀ (k : Nat) (t : MachineData),
      k + (m + 1) < 2 ^ 64 →
      t.status.df = false →
      t.regs.get64 .rcx = .ofNat 64 (m + 1) →
      t.regs.get64 .rsi = rsi0 + .ofNat 64 (k * w.bytes) →
      t.regs.get64 .rdi = rdi0 + .ofNat 64 (k * w.bytes) →
      (∀ j < k + (m + 1), ∃ x,
        t.dmem.loadInt (rsi0 + .ofNat 64 (j * w.bytes)) w.bytes = some x ∧ BitVec.ofInt w.bits x = f j) →
      (∀ j < k + (m + 1), ∃ y,
        t.dmem.loadInt (rdi0 + .ofNat 64 (j * w.bytes)) w.bytes = some y ∧ BitVec.ofInt w.bits y = g j) →
      (∀ j < k + (m + 1), f j = g j) →
      (∀ t',
        t'.dmem = t.dmem →
        t'.zmms = t.zmms →
        t'.status.zf = true →
        t'.status.df = false →
        t'.regs.get64 .rcx = 0#64 →
        t'.regs.get64 .rsi = rsi0 + .ofNat 64 ((k + (m + 1)) * w.bytes) →
        t'.regs.get64 .rdi = rdi0 + .ofNat 64 ((k + (m + 1)) * w.bytes) →
        (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = t.regs.get64 r) →
        Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) →
      Program.Loop p H Q E ⟨t, Host.addrOf (H.start + i)⟩ := by
  induction m with
  | zero =>
    intro k t hm_lt hdf hrcx hrsi hrdi hload_rsi hload_rdi heq hcont
    have hlt_i : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨x, hx_load, hx_val⟩ := hload_rsi k (by omega)
    obtain ⟨y, hy_load, hy_val⟩ := hload_rdi k (by omega)
    have hfg : BitVec.ofInt w.bits x = BitVec.ofInt w.bits y := by
      rw [hx_val, hy_val]; exact heq k (by omega)
    have hne0 : (BitVec.ofNat 64 (0 + 1) == (0 : BitVec 64)) = false := rfl
    refine Program.loop_of_interp hi ?_
    dsimp only [Directive.interp, Instr.interp, Operation.interp]
    rw [rep_all_require_exec, rep_get_low64, hrcx, hne0]
    simp only [Option.isSome_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      rep_zeroExtend_64]
    rw [rep_get_low64, rep_get_low64, hrsi, hrdi]
    dsimp only [MachineData.load]
    simp only [Effects.All_require_read_access, hx_load, hy_load, hdf]
    have hzf : (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == BitVec.zero w.bits) = true := by
      change (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == 0#w.bits) = true
      rw [rep_sub_beq_zero, hfg, beq_self_eq_true]
    simp only [StatusFlags.from_result, MachineData.setReg, strStep_64_df_false,
      rep_set_low64, rep_get_low64]
    rw [regs_cmps_rcx, hrcx, rep_ofNat64_pred]
    simp only [hzf]
    refine hcont _ rfl rfl rfl rfl ?_ ?_ ?_ (fun r hr => ?_)
    · rw [regs_cmps_set64_rcx]
    · rw [regs_cmps_set64_rsi, hrsi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · rw [regs_cmps_set64_rdi, rep_get64_set64]
      change t.regs.get64 .rdi + w.bytesv = _
      rw [hrdi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · exact regs_cmps_set64_other _ _ _ _ hr
  | succ m' ih =>
    intro k t hm_lt hdf hrcx hrsi hrdi hload_rsi hload_rdi heq hcont
    have hlt_i : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨x, hx_load, hx_val⟩ := hload_rsi k (by omega)
    obtain ⟨y, hy_load, hy_val⟩ := hload_rdi k (by omega)
    have hfg : BitVec.ofInt w.bits x = BitVec.ofInt w.bits y := by
      rw [hx_val, hy_val]; exact heq k (by omega)
    have hne0 : (BitVec.ofNat 64 (m' + 1 + 1) == (0 : BitVec 64)) = false :=
      rep_ofNat64_succ_ne_zero (by omega) (by omega)
    have hne_rem : (BitVec.ofNat 64 (m' + 1) != (0 : BitVec 64)) = true := by
      rw [bne_iff_ne]
      exact beq_eq_false_iff_ne.mp (rep_ofNat64_succ_ne_zero (by omega) (by omega))
    refine Program.loop_of_interp hi ?_
    dsimp only [Directive.interp, Instr.interp, Operation.interp]
    rw [rep_all_require_exec, rep_get_low64, hrcx, hne0]
    simp only [Option.isSome_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      rep_zeroExtend_64]
    rw [rep_get_low64, rep_get_low64, hrsi, hrdi]
    dsimp only [MachineData.load]
    simp only [Effects.All_require_read_access, hx_load, hy_load, hdf]
    have hzf : (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == BitVec.zero w.bits) = true := by
      change (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == 0#w.bits) = true
      rw [rep_sub_beq_zero, hfg, beq_self_eq_true]
    simp only [StatusFlags.from_result, MachineData.setReg, strStep_64_df_false,
      rep_set_low64, rep_get_low64]
    rw [regs_cmps_rcx, hrcx, rep_ofNat64_pred]
    simp only [hzf, hne_rem, Bool.and_self, ↓reduceIte, Effects.All]
    change Program.LoopCont p H Q E ⟨_, Host.addrOf (H.start + i)⟩
    refine Program.loopCont_of_le (j := i) (Nat.le_of_lt hlt_i) ?_
    refine ih (k + 1) _ (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [regs_cmps_set64_rcx]
    · rw [regs_cmps_set64_rsi, hrsi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · rw [regs_cmps_set64_rdi, rep_get64_set64]
      change t.regs.get64 .rdi + w.bytesv = _
      rw [hrdi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · intro j hj; exact hload_rsi j (by omega)
    · intro j hj; exact hload_rdi j (by omega)
    · intro j hj; exact heq j (by omega)
    · intro t' hm' hz' hzf' hdf' hrcx' hrsi' hrdi' hother'
      have hm'' : t'.dmem = t.dmem := hm'
      have hz'' : t'.zmms = t.zmms := hz'
      have hrsi'' : t'.regs.get64 .rsi = rsi0 + .ofNat 64 ((k + (m' + 2)) * w.bytes) := by
        rw [hrsi', show k + 1 + (m' + 1) = k + (m' + 2) by omega]
      have hrdi'' : t'.regs.get64 .rdi = rdi0 + .ofNat 64 ((k + (m' + 2)) * w.bytes) := by
        rw [hrdi', show k + 1 + (m' + 1) = k + (m' + 2) by omega]
      refine hcont t' hm'' hz'' hzf' hdf' hrcx' hrsi'' hrdi'' (fun r hr => ?_)
      rw [hother' r hr]
      exact regs_cmps_set64_other _ _ _ _ hr

/--
When `%rcx = n` with `0 < n < 2^64` and all `n` elements at `%rsi` and `%rdi` compare equal,
`repe cmps` finishes at the next instruction with `%rcx = 0`, `zf = true`, and pointers
advanced by `n * w.bytes`.
-/
public theorem Program.loop_repe_cmps_eq [Host] {p : Program} {H : Embedding p} {i : Nat}
    {w : Width}
    (hi : p[i]? = some (.instr (.regular .W64 w (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n : Nat} (hn0 : 0 < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec w.bits)
    (hload_rsi : ∀ j < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 (j * w.bytes)) w.bytes = some x ∧ BitVec.ofInt w.bits x = f j)
    (hload_rdi : ∀ j < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 (j * w.bytes)) w.bytes = some y ∧ BitVec.ofInt w.bits y = g j)
    (heq : ∀ j < n, f j = g j)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = true →
      t'.status.df = false →
      t'.regs.get64 .rcx = 0#64 →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 (n * w.bytes) →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 (n * w.bytes) →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ := by
  cases n with
  | zero => omega
  | succ m =>
    refine loop_repe_cmps_eq_aux hi rsi0 rdi0 f g m 0 s (by omega) hdf hrcx ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Nat.zero_mul, hrsi]; simp
    · rw [Nat.zero_mul, hrdi]; simp
    · simpa using hload_rsi
    · simpa using hload_rdi
    · simpa using heq
    · simpa using hcont

private theorem loop_repe_cmps_ne_aux [Host] {p : Program} {H : Embedding p} {i : Nat}
    {w : Width}
    (hi : p[i]? = some (.instr (.regular .W64 w (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (rsi0 rdi0 : BitVec 64) (f g : Nat → BitVec w.bits) (n k : Nat)
    (d : Nat) :
    ∀ (j : Nat) (t : MachineData),
      j + d = k →
      k < n →
      n < 2 ^ 64 →
      t.status.df = false →
      t.regs.get64 .rcx = .ofNat 64 (n - j) →
      t.regs.get64 .rsi = rsi0 + .ofNat 64 (j * w.bytes) →
      t.regs.get64 .rdi = rdi0 + .ofNat 64 (j * w.bytes) →
      (∀ idx < n, ∃ x,
        t.dmem.loadInt (rsi0 + .ofNat 64 (idx * w.bytes)) w.bytes = some x ∧ BitVec.ofInt w.bits x = f idx) →
      (∀ idx < n, ∃ y,
        t.dmem.loadInt (rdi0 + .ofNat 64 (idx * w.bytes)) w.bytes = some y ∧ BitVec.ofInt w.bits y = g idx) →
      (∀ idx < k, f idx = g idx) →
      f k ≠ g k →
      (∀ t',
        t'.dmem = t.dmem →
        t'.zmms = t.zmms →
        t'.status.zf = false →
        t'.status.df = false →
        t'.regs.get64 .rcx = .ofNat 64 (n - (k + 1)) →
        t'.regs.get64 .rsi = rsi0 + .ofNat 64 ((k + 1) * w.bytes) →
        t'.regs.get64 .rdi = rdi0 + .ofNat 64 ((k + 1) * w.bytes) →
        (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = t.regs.get64 r) →
        Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) →
      Program.Loop p H Q E ⟨t, Host.addrOf (H.start + i)⟩ := by
  induction d with
  | zero =>
    intro j t hd hk_lt hn64 hdf hrcx hrsi hrdi hload_rsi hload_rdi hpre hne hcont
    have hjk : j = k := by omega
    subst hjk
    have hlt_i : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨x, hx_load, hx_val⟩ := hload_rsi j hk_lt
    obtain ⟨y, hy_load, hy_val⟩ := hload_rdi j hk_lt
    have hfg : BitVec.ofInt w.bits x ≠ BitVec.ofInt w.bits y := by
      rw [hx_val, hy_val]; exact hne
    have hnj : n - j = (n - (j + 1)) + 1 := by omega
    have hne0 : (BitVec.ofNat 64 (n - j) == (0 : BitVec 64)) = false :=
      rep_ofNat64_succ_ne_zero (by omega) (by omega)
    refine Program.loop_of_interp hi ?_
    dsimp only [Directive.interp, Instr.interp, Operation.interp]
    rw [rep_all_require_exec, rep_get_low64, hrcx, hne0]
    simp only [Option.isSome_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      rep_zeroExtend_64]
    rw [rep_get_low64, rep_get_low64, hrsi, hrdi]
    dsimp only [MachineData.load]
    simp only [Effects.All_require_read_access, hx_load, hy_load, hdf]
    have hzf : (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == BitVec.zero w.bits) = false := by
      change (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == 0#w.bits) = false
      rw [rep_sub_beq_zero, beq_eq_false_iff_ne]
      exact hfg
    simp only [StatusFlags.from_result, MachineData.setReg, strStep_64_df_false,
      rep_set_low64, rep_get_low64]
    rw [regs_cmps_rcx, hrcx, hnj, rep_ofNat64_pred]
    simp only [hzf, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, Effects.All]
    refine hcont _ rfl rfl rfl rfl ?_ ?_ ?_ (fun r hr => ?_)
    · rw [regs_cmps_set64_rcx]
    · rw [regs_cmps_set64_rsi, hrsi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · rw [regs_cmps_set64_rdi, rep_get64_set64]
      change t.regs.get64 .rdi + w.bytesv = _
      rw [hrdi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · exact regs_cmps_set64_other _ _ _ _ hr
  | succ d' ih =>
    intro j t hd hk_lt hn64 hdf hrcx hrsi hrdi hload_rsi hload_rdi hpre hne hcont
    have hlt_i : i < p.length := (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨x, hx_load, hx_val⟩ := hload_rsi j (by omega)
    obtain ⟨y, hy_load, hy_val⟩ := hload_rdi j (by omega)
    have hfg : BitVec.ofInt w.bits x = BitVec.ofInt w.bits y := by
      rw [hx_val, hy_val]; exact hpre j (by omega)
    have hnj : n - j = (n - (j + 1)) + 1 := by omega
    have hne0 : (BitVec.ofNat 64 (n - j) == (0 : BitVec 64)) = false :=
      rep_ofNat64_succ_ne_zero (by omega) (by omega)
    have hne_rem : (BitVec.ofNat 64 (n - (j + 1)) != (0 : BitVec 64)) = true := by
      rw [bne_iff_ne]
      exact beq_eq_false_iff_ne.mp (rep_ofNat64_succ_ne_zero (by omega) (by omega))
    refine Program.loop_of_interp hi ?_
    dsimp only [Directive.interp, Instr.interp, Operation.interp]
    rw [rep_all_require_exec, rep_get_low64, hrcx, hne0]
    simp only [Option.isSome_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      rep_zeroExtend_64]
    rw [rep_get_low64, rep_get_low64, hrsi, hrdi]
    dsimp only [MachineData.load]
    simp only [Effects.All_require_read_access, hx_load, hy_load, hdf]
    have hzf : (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == BitVec.zero w.bits) = true := by
      change (BitVec.ofInt w.bits x - BitVec.ofInt w.bits y == 0#w.bits) = true
      rw [rep_sub_beq_zero, hfg, beq_self_eq_true]
    simp only [StatusFlags.from_result, MachineData.setReg, strStep_64_df_false,
      rep_set_low64, rep_get_low64]
    rw [regs_cmps_rcx, hrcx, hnj, rep_ofNat64_pred]
    simp only [hzf, hne_rem, Bool.and_self, ↓reduceIte, Effects.All]
    change Program.LoopCont p H Q E ⟨_, Host.addrOf (H.start + i)⟩
    refine Program.loopCont_of_le (j := i) (Nat.le_of_lt hlt_i) ?_
    refine ih (j + 1) _ (by omega) hk_lt hn64 rfl ?_ ?_ ?_ ?_ ?_ hpre hne ?_
    · rw [regs_cmps_set64_rcx]
    · rw [regs_cmps_set64_rsi, hrsi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · rw [regs_cmps_set64_rdi, rep_get64_set64]
      change t.regs.get64 .rdi + w.bytesv = _
      rw [hrdi]
      have hbytes : w.bytesv = BitVec.ofNat 64 w.bytes := rfl
      rw [hbytes, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_mul, Nat.one_mul]
    · intro idx hidx; exact hload_rsi idx hidx
    · intro idx hidx; exact hload_rdi idx hidx
    · intro t' hm' hz' hzf' hdf' hrcx' hrsi' hrdi' hother'
      refine hcont t' hm' hz' hzf' hdf' hrcx' hrsi' hrdi' (fun r hr => ?_)
      rw [hother' r hr]
      exact regs_cmps_set64_other _ _ _ _ hr

/--
When `%rcx = n < 2^64` and `k < n` is the first index where the elements at `%rsi` and `%rdi`
differ, `repe cmps` stops after element `k` with `zf = false`, `%rcx = n - (k + 1)`, and
pointers advanced by `(k + 1) * w.bytes`.
-/
public theorem Program.loop_repe_cmps_ne [Host] {p : Program} {H : Embedding p} {i : Nat}
    {w : Width}
    (hi : p[i]? = some (.instr (.regular .W64 w (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n k : Nat} (hk : k < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec w.bits)
    (hload_rsi : ∀ idx < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 (idx * w.bytes)) w.bytes = some x ∧ BitVec.ofInt w.bits x = f idx)
    (hload_rdi : ∀ idx < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 (idx * w.bytes)) w.bytes = some y ∧ BitVec.ofInt w.bits y = g idx)
    (hpre : ∀ idx < k, f idx = g idx)
    (hne : f k ≠ g k)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = false →
      t'.status.df = false →
      t'.regs.get64 .rcx = .ofNat 64 (n - (k + 1)) →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 ((k + 1) * w.bytes) →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 ((k + 1) * w.bytes) →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ := by
  refine loop_repe_cmps_ne_aux hi rsi0 rdi0 f g n k k 0 s (Nat.zero_add k) hk hn64 hdf ?_ ?_ ?_
    hload_rsi hload_rdi hpre hne hcont
  · simpa using hrcx
  · rw [Nat.zero_mul, hrsi]; simp
  · rw [Nat.zero_mul, hrdi]; simp

/-- Specialization of `Program.loop_repe_cmps_eq` to `repe cmpsb`. -/
public theorem Program.loop_repe_cmpsb_eq [Host] {p : Program} {H : Embedding p} {i : Nat}
    (hi : p[i]? = some (.instr (.regular .W64 .W8 (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n : Nat} (hn0 : 0 < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec 8)
    (hload_rsi : ∀ j < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 j) 1 = some x ∧ BitVec.ofInt 8 x = f j)
    (hload_rdi : ∀ j < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 j) 1 = some y ∧ BitVec.ofInt 8 y = g j)
    (heq : ∀ j < n, f j = g j)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = true →
      t'.status.df = false →
      t'.regs.get64 .rcx = 0#64 →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 n →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 n →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_eq hi hn0 hn64 hdf hrcx rsi0 rdi0 hrsi hrdi f g
    (fun j hj => by simpa [Width.bytes] using hload_rsi j hj)
    (fun j hj => by simpa [Width.bytes] using hload_rdi j hj)
    heq
    (fun t' hm hz hzf hdf' hrcx' hrsi' hrdi' hother =>
      hcont t' hm hz hzf hdf' hrcx'
        (by simpa [Width.bytes] using hrsi')
        (by simpa [Width.bytes] using hrdi') hother)

/-- Specialization of `Program.loop_repe_cmps_ne` to `repe cmpsb`. -/
public theorem Program.loop_repe_cmpsb_ne [Host] {p : Program} {H : Embedding p} {i : Nat}
    (hi : p[i]? = some (.instr (.regular .W64 .W8 (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n k : Nat} (hk : k < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec 8)
    (hload_rsi : ∀ idx < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 idx) 1 = some x ∧ BitVec.ofInt 8 x = f idx)
    (hload_rdi : ∀ idx < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 idx) 1 = some y ∧ BitVec.ofInt 8 y = g idx)
    (hpre : ∀ idx < k, f idx = g idx)
    (hne : f k ≠ g k)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = false →
      t'.status.df = false →
      t'.regs.get64 .rcx = .ofNat 64 (n - (k + 1)) →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 (k + 1) →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 (k + 1) →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_ne hi hk hn64 hdf hrcx rsi0 rdi0 hrsi hrdi f g
    (fun idx hidx => by simpa [Width.bytes] using hload_rsi idx hidx)
    (fun idx hidx => by simpa [Width.bytes] using hload_rdi idx hidx)
    hpre hne
    (fun t' hm hz hzf hdf' hrcx' hrsi' hrdi' hother =>
      hcont t' hm hz hzf hdf' hrcx'
        (by simpa [Width.bytes] using hrsi')
        (by simpa [Width.bytes] using hrdi') hother)

/-- Specialization of `Program.loop_repe_cmps_eq` to `repe cmpsw`. -/
public theorem Program.loop_repe_cmpsw_eq [Host] {p : Program} {H : Embedding p} {i : Nat}
    (hi : p[i]? = some (.instr (.regular .W64 .W16 (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n : Nat} (hn0 : 0 < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec 16)
    (hload_rsi : ∀ j < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 (2 * j)) 2 = some x ∧ BitVec.ofInt 16 x = f j)
    (hload_rdi : ∀ j < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 (2 * j)) 2 = some y ∧ BitVec.ofInt 16 y = g j)
    (heq : ∀ j < n, f j = g j)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = true →
      t'.status.df = false →
      t'.regs.get64 .rcx = 0#64 →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 (2 * n) →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 (2 * n) →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_eq hi hn0 hn64 hdf hrcx rsi0 rdi0 hrsi hrdi f g
    (fun j hj => by simpa [Width.bytes, Nat.mul_comm] using hload_rsi j hj)
    (fun j hj => by simpa [Width.bytes, Nat.mul_comm] using hload_rdi j hj)
    heq
    (fun t' hm hz hzf hdf' hrcx' hrsi' hrdi' hother =>
      hcont t' hm hz hzf hdf' hrcx'
        (by simpa [Width.bytes, Nat.mul_comm] using hrsi')
        (by simpa [Width.bytes, Nat.mul_comm] using hrdi') hother)

/-- Specialization of `Program.loop_repe_cmps_ne` to `repe cmpsw`. -/
public theorem Program.loop_repe_cmpsw_ne [Host] {p : Program} {H : Embedding p} {i : Nat}
    (hi : p[i]? = some (.instr (.regular .W64 .W16 (.cmps (some .e)))))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} {n k : Nat} (hk : k < n) (hn64 : n < 2 ^ 64)
    (hdf : s.status.df = false)
    (hrcx : s.regs.get64 .rcx = .ofNat 64 n)
    (rsi0 rdi0 : BitVec 64)
    (hrsi : s.regs.get64 .rsi = rsi0)
    (hrdi : s.regs.get64 .rdi = rdi0)
    (f g : Nat → BitVec 16)
    (hload_rsi : ∀ idx < n, ∃ x,
      s.dmem.loadInt (rsi0 + .ofNat 64 (2 * idx)) 2 = some x ∧ BitVec.ofInt 16 x = f idx)
    (hload_rdi : ∀ idx < n, ∃ y,
      s.dmem.loadInt (rdi0 + .ofNat 64 (2 * idx)) 2 = some y ∧ BitVec.ofInt 16 y = g idx)
    (hpre : ∀ idx < k, f idx = g idx)
    (hne : f k ≠ g k)
    (hcont : ∀ t',
      t'.dmem = s.dmem →
      t'.zmms = s.zmms →
      t'.status.zf = false →
      t'.status.df = false →
      t'.regs.get64 .rcx = .ofNat 64 (n - (k + 1)) →
      t'.regs.get64 .rsi = rsi0 + .ofNat 64 (2 * (k + 1)) →
      t'.regs.get64 .rdi = rdi0 + .ofNat 64 (2 * (k + 1)) →
      (∀ r, r ∉ [Reg64.rcx, Reg64.rdi, Reg64.rsi] → t'.regs.get64 r = s.regs.get64 r) →
      Program.LoopCont p H Q E ⟨t', Host.addrOf (H.start + i + 1)⟩) :
    Program.Loop p H Q E ⟨s, Host.addrOf (H.start + i)⟩ :=
  Program.loop_repe_cmps_ne hi hk hn64 hdf hrcx rsi0 rdi0 hrsi hrdi f g
    (fun idx hidx => by simpa [Width.bytes, Nat.mul_comm] using hload_rsi idx hidx)
    (fun idx hidx => by simpa [Width.bytes, Nat.mul_comm] using hload_rdi idx hidx)
    hpre hne
    (fun t' hm hz hzf hdf' hrcx' hrsi' hrdi' hother =>
      hcont t' hm hz hzf hdf' hrcx'
        (by simpa [Width.bytes, Nat.mul_comm] using hrsi')
        (by simpa [Width.bytes, Nat.mul_comm] using hrdi') hother)
