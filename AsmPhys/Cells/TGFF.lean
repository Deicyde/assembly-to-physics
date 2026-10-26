import AsmPhys.Design.TGFF
import AsmPhys.Cells.TGLatch
import AsmPhys.Cells.FlipFlop

/-!
# TGMS26: structure and FF1

The flip-flop, its hold tube and its timing conditions are defined in `AsmPhys.Design.TGFF`. Its
structural facts are read off the transistor table. FF1 holds because in the low phase the slave's
input gate TG3 is off and its loop is invariant.
-/

namespace AsmPhys

open Set

section Structure

variable {S : Params} {dev : Fin 26 → ℝ → ℝ → ℝ → ℝ} {C : Fin 11 → ℝ → ℝ}
  {hC : ∀ k v, 0 < C k v}

/-! The structural facts are read off the table: each premise below is a closed decidable fact
about `Fin 26` and `Node 11 4`, closed by `decide` without unfolding `Netlist.F`. -/

/-- A table pair `iN, iP` driving `out` alone is an inverter of `tgff`. -/
theorem tgff_isInverter_of_table {inp : Node 11 4} {out : Fin 11} {iN iP : Fin 26}
    (h : iN ≠ iP ∧ TGFF.pol iN = .n ∧ TGFF.pol iP = .p ∧ TGFF.gate iN = inp ∧
      TGFF.gate iP = inp ∧ TGFF.drain iN = .state out ∧ TGFF.source iN = .bdry TGFF.gnd ∧
      TGFF.drain iP = .state out ∧ TGFF.source iP = .bdry TGFF.vdd ∧
      ∀ i, i ≠ iN → i ≠ iP → TGFF.drain i ≠ .state out ∧ TGFF.source i ≠ .state out) :
    (tgff S dev C hC).IsInverter inp out TGFF.gnd TGFF.vdd iN iP := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- A table pair `iN, iP` driving `out`, whose other channels at `out` lie in `side`, is an inverter
core of `tgff`. -/
theorem tgff_isInvCore_of_table {inp : Node 11 4} {out : Fin 11} {iN iP : Fin 26}
    {side : Finset (Fin 26)}
    (h : iN ≠ iP ∧ TGFF.pol iN = .n ∧ TGFF.pol iP = .p ∧ TGFF.gate iN = inp ∧
      TGFF.gate iP = inp ∧ TGFF.drain iN = .state out ∧ TGFF.source iN = .bdry TGFF.gnd ∧
      TGFF.drain iP = .state out ∧ TGFF.source iP = .bdry TGFF.vdd ∧ iN ∉ side ∧ iP ∉ side ∧
      ∀ i, i ≠ iN → i ≠ iP → i ∉ side → TGFF.drain i ≠ .state out ∧ TGFF.source i ≠ .state out) :
    (tgff S dev C hC).IsInvCore inp out TGFF.gnd TGFF.vdd iN iP side := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- A table pair `jN, jP` with channels between `x` and `y` is a transmission gate of `tgff`. -/
theorem tgff_isTG_of_table {x y : Fin 11} {gn gp : Node 11 4} {jN jP : Fin 26}
    (h : jN ≠ jP ∧ x ≠ y ∧ TGFF.pol jN = .n ∧ TGFF.pol jP = .p ∧ TGFF.gate jN = gn ∧
      TGFF.gate jP = gp ∧
      ((TGFF.drain jN = .state y ∧ TGFF.source jN = .state x) ∨
        (TGFF.drain jN = .state x ∧ TGFF.source jN = .state y)) ∧
      ((TGFF.drain jP = .state y ∧ TGFF.source jP = .state x) ∨
        (TGFF.drain jP = .state x ∧ TGFF.source jP = .state y))) :
    (tgff S dev C hC).IsTG x y gn gp jN jP := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem tgff_inv_CKB :
    (tgff S dev C hC).IsInverter (.bdry TGFF.clk) TGFF.CKB TGFF.gnd TGFF.vdd
      (0 : Fin 26) (1 : Fin 26) :=
  tgff_isInverter_of_table (by decide)

theorem tgff_inv_Y :
    (tgff S dev C hC).IsInverter (.state TGFF.X) TGFF.Y TGFF.gnd TGFF.vdd
      (6 : Fin 26) (7 : Fin 26) :=
  tgff_isInverter_of_table (by decide)

theorem tgff_inv_B1 :
    (tgff S dev C hC).IsInverter (.state TGFF.Y) TGFF.B1 TGFF.gnd TGFF.vdd
      (12 : Fin 26) (13 : Fin 26) :=
  tgff_isInverter_of_table (by decide)

theorem tgff_inv_B2 :
    (tgff S dev C hC).IsInverter (.state TGFF.B1) TGFF.B2 TGFF.gnd TGFF.vdd
      (14 : Fin 26) (15 : Fin 26) :=
  tgff_isInverter_of_table (by decide)

theorem tgff_inv_Q :
    (tgff S dev C hC).IsInverter (.state TGFF.Z) TGFF.Q TGFF.gnd TGFF.vdd
      (20 : Fin 26) (21 : Fin 26) :=
  tgff_isInverter_of_table (by decide)

/-- The master latch: storage `X`, forward `Y`, input core `A1` from `D` through TG1 (n-gate `CKB`,
p-gate clock), feedback core `A2` through TG2 (n-gate clock, p-gate `CKB`). -/
theorem tgff_master :
    (tgff S dev C hC).IsTGLatch TGFF.gnd TGFF.vdd (.bdry TGFF.d) TGFF.X TGFF.Y TGFF.A1 TGFF.A2
      (.state TGFF.CKB) (.bdry TGFF.clk) (.bdry TGFF.clk) (.state TGFF.CKB)
      (2 : Fin 26) (3 : Fin 26) (8 : Fin 26) (9 : Fin 26)
      (4 : Fin 26) (5 : Fin 26) (10 : Fin 26) (11 : Fin 26) (6 : Fin 26) (7 : Fin 26) where
  core₁ := tgff_isInvCore_of_table (side := ({4, 5} : Finset (Fin 26))) (by decide)
  core₂ := tgff_isInvCore_of_table (side := ({10, 11} : Finset (Fin 26))) (by decide)
  tg₁ := tgff_isTG_of_table (by decide)
  tg₂ := tgff_isTG_of_table (by decide)
  fwd := tgff_inv_Y
  only_x := (by decide : ∀ i : Fin 26, (TGFF.drain i = .state TGFF.X ∨
    TGFF.source i = .state TGFF.X) → i ∈ ({4, 5, 10, 11} : Finset (Fin 26)))
  tg_disj := (by decide : Disjoint ({4, 5} : Finset (Fin 26)) {10, 11})
  distinct := by decide

/-- The slave latch: storage `Z`, forward `Q`, input core `B` from `B2` through TG3 (n-gate clock,
p-gate `CKB`), feedback core `A4` through TG4 (n-gate `CKB`, p-gate clock). -/
theorem tgff_slave :
    (tgff S dev C hC).IsTGLatch TGFF.gnd TGFF.vdd (.state TGFF.B2) TGFF.Z TGFF.Q TGFF.B TGFF.A4
      (.bdry TGFF.clk) (.state TGFF.CKB) (.state TGFF.CKB) (.bdry TGFF.clk)
      (16 : Fin 26) (17 : Fin 26) (22 : Fin 26) (23 : Fin 26)
      (18 : Fin 26) (19 : Fin 26) (24 : Fin 26) (25 : Fin 26) (20 : Fin 26) (21 : Fin 26) where
  core₁ := tgff_isInvCore_of_table (side := ({18, 19} : Finset (Fin 26))) (by decide)
  core₂ := tgff_isInvCore_of_table (side := ({24, 25} : Finset (Fin 26))) (by decide)
  tg₁ := tgff_isTG_of_table (by decide)
  tg₂ := tgff_isTG_of_table (by decide)
  fwd := tgff_inv_Q
  only_x := (by decide : ∀ i : Fin 26, (TGFF.drain i = .state TGFF.Z ∨
    TGFF.source i = .state TGFF.Z) → i ∈ ({18, 19, 24, 25} : Finset (Fin 26)))
  tg_disj := (by decide : Disjoint ({18, 19} : Finset (Fin 26)) {24, 25})
  distinct := by decide

/-- Only ground and supply touch channels; the clock and data pins drive gates only. -/
theorem tgff_touchesChannel (j : Fin 4) :
    (tgff S dev C hC).TouchesChannel j ↔ j = TGFF.gnd ∨ j = TGFF.vdd :=
  (by decide : ∀ j : Fin 4, (∃ i : Fin 26, TGFF.drain i = .bdry j ∨ TGFF.source i = .bdry j) ↔
    j = TGFF.gnd ∨ j = TGFF.vdd) j

/-- Every transistor meets its polarity's contract when every device function does. -/
theorem tgff_contractOn (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))
    (T : Finset (Fin 26)) : (tgff S dev C hC).ContractOn S T :=
  fun i _ => hdev i

end Structure

/-- **FF1 for TGMS26**, without leakage: the `ff1` field of `FFContract` for every device family
meeting the contracts and every capacitance law in range, when `t_cq^max` reaches past the fall
window and the clock inverter's delay (N6) and `t_cq^min = 0` (N7). -/
theorem tgff_ff1 {S : Params} (hS : S.Consistent)                     -- THM (norm_num)
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {dev : Fin 26 → ℝ → ℝ → ℝ → ℝ} {C : Fin 11 → ℝ → ℝ} {hC : ∀ k v, 0 < C k v}
    (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))  -- MODEL/MEAS
    {Cmin Cmax : Fin 11 → ℝ} (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (C k))       -- MEAS
    (hN6 : 2 * S.tslew + S.thigh + S.tpdINV (Cmax TGFF.CKB) ≤ S.tcqmax)        -- MODEL
    (hN7 : S.tcqmin = 0) :                                                    -- MODEL
    ∀ (VDD : ℝ) (u : ℝ → Fin 4 → ℝ) (e : ℝ → Fin 11 → ℝ) (a b : ℝ) (tg tr : ℕ → ℝ),
      (tgff S dev C hC).IsTrajOn u e a b →
      FFRun S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd VDD u e a b tg tr →
      ∀ (k : ℕ) (d : Bool) (s : ℝ), s ∈ Icc a b → tr k + S.tcqmax ≤ s → s < tr (k + 1) →
        e s ∈ tgffHold S (fun t => u t TGFF.clk) d s →
        (∀ t ∈ Icc a b, s ≤ t → t < tr (k + 1) →
            e t ∈ tgffHold S (fun t => u t TGFF.clk) d t) ∧
          ∀ t ∈ Icc a b, s ≤ t → t ≤ tr (k + 1) + S.tcqmin → S.validOut d (e t TGFF.Q) := by
  intro VDD u e a b tg tr he hrun k d s hs hks hsk h0
  simp only [tgffHold, Set.mem_ofPred_eq] at h0 ⊢
  obtain ⟨h0r, h0c, h0l⟩ := h0
  obtain ⟨hVOL, hK01, hK02, hK03, hK04⟩ := hS.K0
  have hVDD := hrun.vdd_mem
  -- Work on `[s, b']` with `b' = min b T'`.
  have hsb' : s ≤ min b (tr (k + 1)) := le_min hs.2 hsk.le
  have hsub : ∀ t ∈ Icc s (min b (tr (k + 1))), t ∈ Icc a b := fun t ht =>
    ⟨hs.1.trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have he' : (tgff S dev C hC).IsTrajOn u e s (min b (tr (k + 1))) :=
    he.mono hs.1 (min_le_left _ _)
  have hgnd : ∀ t ∈ Icc s (min b (tr (k + 1))), u t TGFF.gnd = 0 := fun t ht =>
    hrun.gnd_eq t (hsub t ht)
  have hvdd : ∀ t ∈ Icc s (min b (tr (k + 1))), u t TGFF.vdd = VDD := fun t ht =>
    hrun.vdd_eq t (hsub t ht)
  -- (1) Only ground and supply touch channels, both in `[0, V_DD^max]`: rails on `[s, b]`.
  have hrail : ∀ t ∈ Icc s b, ∀ j, e t j ∈ Icc 0 S.VDDmax := by
    refine (tgff S dev C hC).rail_invariance (fun i => (hdev i).passive)
      (fun i => (hdev i).regular) (he.mono hs.1 le_rfl) (fun j hj t ht => ?_) h0r
    have hta : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    rcases (tgff_touchesChannel j).1 hj with rfl | rfl
    · rw [hrun.gnd_eq t hta]
      exact ⟨le_rfl, by linarith [hS.K13_supply]⟩
    · rw [hrun.vdd_eq t hta]
      exact ⟨by linarith [hVDD.1], hVDD.2⟩
  have hrail' : ∀ t ∈ Icc s (min b (tr (k + 1))), ∀ j, e t j ∈ Icc 0 S.VDDmax := fun t ht =>
    hrail t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  -- (2) `t_pd ≥ 0` and N6 put `s` past the fall: the clock is low on `[s, T']`.
  have hCmax : 0 ≤ Cmax TGFF.CKB :=
    (hcap TGFF.CKB).pos.le.trans (((hcap TGFF.CKB).range 0).1.trans ((hcap TGFF.CKB).range 0).2)
  have htpd : 0 ≤ S.tpdINV (Cmax TGFF.CKB) :=
    mul_nonneg hCmax ((div_pos (by linarith) (sub_pos.2 hS.K5)).le.trans (le_max_left _ _))
  have hlow : ∀ t, s ≤ t → t ≤ tr (k + 1) → u t TGFF.clk ≤ S.VIL := fun t h1 h2 =>
    hrun.clockOK.low_between k t ⟨by linarith, h2⟩
  -- (3) The clock inverter's input is valid-low and `CKB ≥ V_OH` at `s`: `CKB` stays high.
  have hckb : ∀ t ∈ Icc s (min b (tr (k + 1))), S.VOH ≤ e t TGFF.CKB :=
    ((tgff_inv_CKB (S := S) (dev := dev) (C := C) (hC := hC)).propagation_rail hS (hdev 0)
      (hdev 1) (hcap TGFF.CKB).range hVDD he' hgnd hvdd (fun t ht => hrail' t ht _) (x := false)
      (fun t ht => hlow t ht.1 (ht.2.trans (min_le_right _ _)))).2 s ⟨le_rfl, hsb'⟩ h0c
  -- (4) Clock low and `CKB ≥ V_OH > V_IH` turn TG3 off: the slave holds `d`.
  have hhold : ∀ t ∈ Icc s (min b (tr (k + 1))), latchHold S d TGFF.Z TGFF.Q TGFF.A4 (e t) :=
    (tgff_slave (S := S) (dev := dev) (C := C) (hC := hC)).hold_invariant hS
      (tgff_contractOn hdev _) hI hVDD he' hgnd hvdd (fun t ht j _ => hrail' t ht j)
      (fun t ht => ⟨hlow t ht.1 (ht.2.trans (min_le_right _ _)), hK03.le.trans (hckb t ht)⟩) h0l
  -- (5) Assemble; with `t_cq^min = 0` the output window ends at `T'`.
  refine ⟨fun t ht hst htr => ?_, fun t ht hst htr => ?_⟩
  · have htb : t ∈ Icc s (min b (tr (k + 1))) := ⟨hst, le_min ht.2 htr.le⟩
    exact ⟨hrail t ⟨hst, ht.2⟩, hckb t htb, hhold t htb⟩
  · rw [hN7, add_zero] at htr
    exact (hhold t ⟨hst, le_min ht.2 htr⟩).2.2

end AsmPhys
