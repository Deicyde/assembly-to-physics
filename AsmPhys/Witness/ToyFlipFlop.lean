import AsmPhys.Cells.TGFFCapture
import AsmPhys.Cells.Buridan
import AsmPhys.Witness.Toy
import AsmPhys.Witness.Clock

/-!
# Toy flip-flop: non-vacuity of H_cells' flip-flop clause and of THM L3.3 (spike milestone C)

The transmission-gate flip-flop TGMS26 built from the toy clamp devices, with constant node
capacitances: `CKB` 0.01, the delay stages `B1, B2` 52 each, every other node 0.1. On the toy sheet
(`t_su = 550`, `t_h = 11`, `t_cq ∈ [0, 421]`, clock edges every 1000) it meets N1–N7, so it meets the
flip-flop contract with a time-independent, nonempty hold tube that every state on the rails reaches
by a capture. Its hypotheses together with a continuous ClockOK clock and a rising `D` meet every
hypothesis of THM L3.3, which therefore holds non-vacuously: some start time of the rise leaves `Q`
at `(V_IL + V_IH)/2` one cycle later.
-/

namespace AsmPhys.Witness

open Set

/-- Toy node capacitances, indexed as `TGFF`'s state nodes. -/
noncomputable def toyC : Fin 11 → ℝ := ![0.01, 0.1, 0.1, 0.1, 0.1, 52, 52, 0.1, 0.1, 0.1, 0.1]

theorem toyC_pos (k : Fin 11) : 0 < toyC k := by
  fin_cases k <;> norm_num [toyC]

/-- The toy flip-flop: TGMS26 with the toy clamp devices and the toy capacitances. -/
noncomputable def toyFF : Netlist 11 4 :=
  tgff sheet (fun i => dev (TGFF.pol i) fetParams) (fun k _ => toyC k) (fun k _ => toyC_pos k)

theorem sheet_par (pol : Polarity) : sheet.par pol = fetParams := by
  cases pol <;> rfl

theorem sheet_Irise : sheet.Irise = 0.1 := by
  norm_num [Params.Irise, sheet, fetParams]

theorem sheet_Ifall : sheet.Ifall = 0.1 := by
  norm_num [Params.Ifall, sheet, fetParams]

/-- On the toy sheet `t_pd(C) = 9·C`. -/
theorem sheet_tpdINV_mul (c : ℝ) : sheet.tpdINV c = 9 * c := by
  rw [Params.tpdINV, sheet_Irise, sheet_Ifall]
  norm_num [sheet]
  ring

/-- On the toy sheet `t_cd(C) = C/10`. -/
theorem sheet_tcdINV (c : ℝ) : sheet.tcdINV c = c / 10 := by
  norm_num [Params.tcdINV, Params.NML, Params.NMH, sheet, fetParams]
  ring

/-- On the toy sheet `Φ(C_A, C_X) = 10·(C_A + C_X) + 10·C_X`. -/
theorem sheet_PhiTG (a x : ℝ) : sheet.PhiTG a x = 10 * (a + x) + 10 * x := by
  norm_num [Params.PhiTG, Params.NML, Params.NMH, sheet, fetParams]
  ring

/-- The toy capacitances and the toy sheet meet N1–N7. -/
theorem toy_timing : TGFFTiming sheet toyC toyC := by
  constructor <;>
    (try simp only [Params.σm, Params.σs, sheet_PhiTG, sheet_tpdINV_mul, sheet_tcdINV]) <;>
    norm_num [toyC, TGFF.CKB, TGFF.A1, TGFF.X, TGFF.Y, TGFF.A2, TGFF.B1, TGFF.B2, TGFF.B, TGFF.Z,
      TGFF.Q, TGFF.A4, sheet]

/-- Every toy transistor meets its polarity's contract with the sheet's parameters. -/
theorem toy_hdev (i : Fin 26) :
    FETContract (TGFF.pol i) (sheet.par (TGFF.pol i)) sheet.VDDmax
      (dev (TGFF.pol i) fetParams) := by
  rw [sheet_par]
  exact toy_contract _

theorem toy_hcap (k : Fin 11) : NodeCap (toyC k) (toyC k) (toyFF.C k) :=
  nodeCap_const (toyC_pos k)

/-- **H_cells' flip-flop clause is satisfiable.** The toy flip-flop meets the flip-flop contract. -/
theorem toy_tgff_contract :
    FFContract sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold sheet) :=
  tgff_contract sheet_consistent ⟨rfl, rfl⟩ toy_hdev (fun k => nodeCap_const (toyC_pos k))
    toy_timing

/-- A state in the hold tube of `b`: `CKB` and `Q` at `V_OH` for `b = 1`; `CKB`, `Z` and `A4` at
`V_OH` for `b = 0`; every other node at `0`. -/
noncomputable def toyHoldState : Bool → Fin 11 → ℝ
  | true => ![0.9, 0, 0, 0, 0, 0, 0, 0, 0, 0.9, 0]
  | false => ![0.9, 0, 0, 0, 0, 0, 0, 0, 0.9, 0, 0.9]

theorem toyHoldState_mem (clk : ℝ → ℝ) (b : Bool) (t : ℝ) :
    toyHoldState b ∈ tgffHold sheet clk b t := by
  cases b <;> refine ⟨fun k => ?_, ?_, ?_⟩
  all_goals first
    | (fin_cases k <;> norm_num [toyHoldState, sheet])
    | norm_num [toyHoldState, latchHold, Params.Lvl, Params.θL, Params.θH, Params.validOut,
        TGFF.CKB, TGFF.Z, TGFF.Q, TGFF.A4, sheet]

/-- The hold tube of each bit is nonempty. -/
theorem toy_tgffHold_nonempty (clk : ℝ → ℝ) (b : Bool) (t : ℝ) :
    (tgffHold sheet clk b t).Nonempty :=
  ⟨toyHoldState b, toyHoldState_mem clk b t⟩

/-- The toy boundary waveform: ground `0`, supply `1`, clock `clk`, data `v`. -/
noncomputable def toyU (clk : ℝ → ℝ) (v : ℝ) (t : ℝ) : Fin 4 → ℝ := ![0, 1, clk t, v]

section ToyU

variable {clk : ℝ → ℝ} {v t : ℝ}

@[simp] theorem toyU_gnd : toyU clk v t TGFF.gnd = 0 := rfl
@[simp] theorem toyU_vdd : toyU clk v t TGFF.vdd = 1 := rfl
@[simp] theorem toyU_clk : toyU clk v t TGFF.clk = clk t := rfl
@[simp] theorem toyU_d : toyU clk v t TGFF.d = v := rfl

theorem continuous_toyU (hclk : Continuous clk) : Continuous (toyU clk v) :=
  continuous_pi fun j => by fin_cases j <;> simp [toyU] <;> fun_prop

end ToyU

/-- **The hold tube is reachable.** From any state on the rails at `t = 421`, with a continuous
ClockOK clock (edges every 1000) and `D` held at `b`, the toy flip-flop's trajectory is in the hold
tube of `b` at `t = 1421`. -/
theorem toy_tgff_reachable (b : Bool) (e₀ : Fin 11 → ℝ) (he₀ : ∀ j, e₀ j ∈ Icc 0 1) :
    ∃ (u : ℝ → Fin 4 → ℝ) (e : ℝ → Fin 11 → ℝ), Continuous u ∧
      (∀ t, u t TGFF.d = if b then 1 else 0) ∧ toyFF.IsTrajOn u e 421 1421 ∧ e 421 = e₀ ∧
      FFRun sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd 1 u e 421 1421
        (fun k => (k : ℝ) * 1000) (fun k => (k : ℝ) * 1000) ∧
      e 1421 ∈ tgffHold sheet (fun t => u t TGFF.clk) b 1421 := by
  have hVDD : (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax := ⟨le_rfl, le_rfl⟩
  obtain ⟨clk, hclk, hedges, hok⟩ := exists_clockOK sheet_consistent hVDD
  have hv : (if b then (1 : ℝ) else 0) ∈ Icc 0 1 := by cases b <;> norm_num
  obtain ⟨e, he, he0⟩ := toyFF.exists_isTrajOn (fun i => (toy_hdev i).regular) toy_hcap
    (continuous_toyU (v := if b then 1 else 0) hclk).continuousOn (by norm_num : (421 : ℝ) ≤ 1421)
    e₀
  have hrun : FFRun sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd 1
      (toyU clk (if b then 1 else 0)) e 421 1421
      (fun k => (k : ℝ) * 1000) (fun k => (k : ℝ) * 1000) :=
    { vdd_mem := hVDD
      gnd_eq := fun _ _ => rfl
      vdd_eq := fun _ _ => rfl
      edges := hedges
      clockOK := hok
      d_rail := fun _ _ => hv }
  refine ⟨_, e, continuous_toyU hclk, fun _ => rfl, he, he0, hrun, ?_⟩
  -- Only ground and supply touch channels: every node stays on `[0, 1]`.
  have hrail : ∀ t ∈ Icc (421 : ℝ) 1421, ∀ j, e t j ∈ Icc 0 1 := by
    refine toyFF.rail_invariance (fun i => (toy_hdev i).passive) (fun i => (toy_hdev i).regular)
      he (fun j hj t _ => ?_) (by rw [he0]; exact he₀)
    rcases (tgff_touchesChannel j).1 hj with rfl | rfl <;> norm_num
  -- The clock is low on `[420, 1000]` and `t_pd(CKB) = 0.09`, so `CKB ≥ V_OH` at `450`.
  have hlow : ∀ t ∈ Icc (421 : ℝ) 1000, toyU clk (if b then 1 else 0) t TGFF.clk ≤ sheet.VIL :=
    fun t ht => hok.low_between 0 t ⟨by norm_num [sheet]; linarith [ht.1], by norm_num; exact ht.2⟩
  have hckb : sheet.VOH ≤ e 450 TGFF.CKB :=
    ((tgff_inv_CKB (S := sheet) (dev := fun i => dev (TGFF.pol i) fetParams)
      (C := fun k _ => toyC k) (hC := fun k _ => toyC_pos k)).propagation_rail sheet_consistent
      (toy_hdev 0) (toy_hdev 1) (toy_hcap TGFF.CKB).range hVDD (he.mono le_rfl (by norm_num))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun t ht => hrail t ⟨ht.1, by linarith [ht.2]⟩ _)
      (x := false) hlow).1 450
      ⟨by rw [sheet_tpdINV_mul]; norm_num [toyC, TGFF.CKB], by norm_num⟩
  -- Capture at the edge `1000`: `T' − t_su = 450`, `T' + t_h = 1011`, `T' + t_cq^max = 1421`.
  have hT : ((0 + 1 : ℕ) : ℝ) * 1000 - sheet.tsu = 450 := by norm_num [sheet]
  have hτ : ((0 + 1 : ℕ) : ℝ) * 1000 + sheet.tcqmax = 1421 := by norm_num [sheet]
  have key := tgff_capture (k := 0) (d' := b) sheet_consistent ⟨rfl, rfl⟩ toy_hdev
    (fun k => nodeCap_const (toyC_pos k)) toy_timing he hrun (by norm_num [sheet])
    (by norm_num [sheet]) (by rw [hT]; exact hrail 450 ⟨by norm_num, by norm_num⟩)
    (by rw [hT]; exact hckb)
    (fun t _ => by cases b <;> norm_num [Params.validIn, sheet]) (by norm_num [sheet])
  rw [hτ] at key
  exact key

/-- **THM L3.3 is non-vacuous.** For the toy flip-flop with a continuous ClockOK clock, started in
its hold tube at `t = 421`, some start `τ` of a unit-slope rise of `D` leaves `Q` exactly at
`(V_IL + V_IH)/2` at `t = 1421`. -/
theorem toy_buridan : ∃ clk : ℝ → ℝ, Continuous clk ∧ ClockOK sheet 1 clk (fun k => (k : ℝ) * 1000) ∧
    ∃ τ ∈ Icc (421 : ℝ) 1011, ∃ e : ℝ → Fin 11 → ℝ,
      toyFF.IsTrajOn
        (fun t => Function.update ![0, 1, clk t, 0] TGFF.d (max 0 (min 1 (t - τ)))) e 421 1421 ∧
      e 421 ∈ tgffHold sheet clk true 421 ∧ e 1421 TGFF.Q = (sheet.VIL + sheet.VIH) / 2 := by
  have hVDD : (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax := ⟨le_rfl, le_rfl⟩
  obtain ⟨clk, hclk, hedges, hok⟩ := exists_clockOK sheet_consistent hVDD
  refine ⟨clk, hclk, hok, ?_⟩
  -- `k = 0`, `t_ρ = 1`: `0 + 421 + 1 ≤ 1000 − 550`, and `t_obs = 1421 ∈ [1421, 2000]`.
  obtain ⟨τ, hτ, e, he, he0, hQ⟩ := buridan (k := 0) (d₀ := true) (e₀ := toyHoldState true)
    (tobs := 1421) (ρ := fun x => max 0 (min 1 x)) (tρ := 1) (u₀ := toyU clk 0)
    sheet_consistent toy_tgff_contract (fun i => (toy_hdev i).regular) toy_hcap (by decide) hVDD
    (continuous_toyU hclk) (fun _ => rfl) (fun _ => rfl) hedges hok (by fun_prop)
    (fun x hx => max_eq_left ((min_le_right _ _).trans hx))
    (fun x hx => by rw [min_eq_left hx, max_eq_right zero_le_one])
    (fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩) (by norm_num [sheet])
    (toyHoldState_mem _ _ _) (by norm_num [sheet])
  have h421 : ((0 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax = 421 := by norm_num [sheet]
  rw [h421] at he he0
  refine ⟨τ, by norm_num [sheet] at hτ ⊢; exact hτ, e, he, ?_, hQ⟩
  rw [he0]
  exact toyHoldState_mem _ _ _

/-- **Every hypothesis of THM L3.3 holds for the toy flip-flop**, as a statement: the flip-flop
contract, regular devices, capacitance ranges, a data pin distinct from the other pins, a supply in
range, a continuous boundary waveform with ground and supply pins, edges every `T_clk` with a
ClockOK clock, a continuous unit-slope rise `ρ`, `k = 0` with `t_cq^max + t_ρ ≤ T_clk − t_su`, a
start state in the hold tube, and `t_obs = 1421` in the observation window. `toy_buridan` is
`buridan` applied to them. -/
theorem toy_buridan_hyps : ∃ clk : ℝ → ℝ,
    FFContract sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold sheet) ∧
    (∀ i, Regular (toyFF.fet i).I) ∧ (∀ k, NodeCap (toyC k) (toyC k) (toyFF.C k)) ∧
    (TGFF.d ≠ TGFF.clk ∧ TGFF.d ≠ TGFF.gnd ∧ TGFF.d ≠ TGFF.vdd) ∧
    (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax ∧
    Continuous (toyU clk 0) ∧ (∀ t, toyU clk 0 t TGFF.gnd = 0) ∧
    (∀ t, toyU clk 0 t TGFF.vdd = 1) ∧
    EdgesOK sheet (fun k => (k : ℝ) * sheet.Tclk) (fun k => (k : ℝ) * sheet.Tclk) ∧
    ClockOK sheet 1 (fun t => toyU clk 0 t TGFF.clk) (fun k => (k : ℝ) * sheet.Tclk) ∧
    Continuous (fun x : ℝ => max 0 (min 1 x)) ∧ (∀ x ≤ 0, max 0 (min 1 x) = 0) ∧
    (∀ x, 1 ≤ x → max 0 (min 1 x) = 1) ∧ (∀ x, max 0 (min 1 x) ∈ Icc (0 : ℝ) 1) ∧
    ((0 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax + 1 ≤ ((0 + 1 : ℕ) : ℝ) * sheet.Tclk - sheet.tsu ∧
    toyHoldState true ∈
      tgffHold sheet (fun t => toyU clk 0 t TGFF.clk) true (((0 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax) ∧
    (1421 : ℝ) ∈ Icc (((0 + 1 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax)
      (((0 + 2 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmin) := by
  have hVDD : (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax := ⟨le_rfl, le_rfl⟩
  obtain ⟨clk, hclk, hedges, hok⟩ := exists_clockOK sheet_consistent hVDD
  exact ⟨clk, toy_tgff_contract, fun i => (toy_hdev i).regular, toy_hcap, by decide, hVDD,
    continuous_toyU hclk, fun _ => rfl, fun _ => rfl, hedges, hok, by fun_prop,
    fun x hx => max_eq_left ((min_le_right _ _).trans hx),
    fun x hx => by rw [min_eq_left hx, max_eq_right zero_le_one],
    fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, by norm_num [sheet],
    toyHoldState_mem _ _ _, by norm_num [sheet]⟩

end AsmPhys.Witness
