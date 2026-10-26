import AsmPhys.Witness.Toy
import AsmPhys.Cells.Inverter
import AsmPhys.Circuit.WellPosed

/-!
# Toy inverter: non-vacuity of THM L3.1 (M2)

One state node (the output), boundary nodes ground `0`, supply `1` and input `2`, the toy n-FET
and p-FET, and unit output capacitance. With ground at `0`, supply at `1` and the input held at
`0`, THM L2.2 gives a trajectory from `0`, every hypothesis of `IsInverter.propagation` holds,
and the output is a valid `1` from `t_pd = 1 · max(0.9/0.1, 0.9/0.1) = 9` on.

The toy objects are defined in `AsmPhys.Design.Toy`.
-/

namespace AsmPhys.Witness

open AsmPhys.Toy Set

theorem inv_isInverter : inv.IsInverter (.bdry 2) 0 0 1 (0 : Fin 2) (1 : Fin 2) where
  ne := by change (0 : Fin 2) ≠ 1; decide
  pol_n := rfl
  pol_p := rfl
  gate_n := rfl
  gate_p := rfl
  drain_n := rfl
  source_n := rfl
  drain_p := rfl
  source_p := rfl
  only i h0 h1 := by
    change Fin 2 at i
    fin_cases i
    exacts [absurd rfl h0, absurd rfl h1]

/-- Both toy devices are regular (C2). -/
lemma inv_regular (i : Fin inv.nf) : Regular (inv.fet i).I := by
  change Fin 2 at i
  fin_cases i
  exacts [(toy_contract .n).regular, (toy_contract .p).regular]

/-- With unit output capacitance, `t_pd(INV) = 1 · max(0.9/0.1, 0.9/0.1) = 9` on the toy sheet. -/
lemma sheet_tpdINV : sheet.tpdINV 1 = 9 := by
  norm_num [Params.tpdINV, Params.Irise, Params.Ifall, sheet, fetParams]

/-- Non-vacuity of THM L3.1 for INV: the toy inverter with its input held low has a trajectory
from `0` on `[0, 20]`, and its output is `validOut 1` on `[9, 20]`. -/
theorem inv_rises : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 0]) e 0 20 ∧ e 0 = 0 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut true (e t 0) := by
  obtain ⟨e, he, he0⟩ := inv.exists_isTrajOn (Cmin := fun _ => 1) (Cmax := fun _ => 1)
    inv_regular (fun _ => nodeCap_const one_pos) (u := fun _ => ![0, 1, 0]) (a := 0) (b := 20)
    continuousOn_const (by norm_num) 0
  refine ⟨e, he, he0, fun t ht => ?_⟩
  have hin : ∀ t ∈ Icc (0 : ℝ) 20,
      sheet.validIn false (pot ((fun _ => ![0, 1, 0]) t) (e t) (.bdry 2)) := fun _ _ => by
    norm_num [Params.validIn, sheet]
  have h0 : e 0 0 ∈ Icc 0 1 := by simp [he0]
  exact (inv_isInverter.propagation sheet_consistent (toy_contract .n) (toy_contract .p)
    (Cmin := 1) (Cmax := 1) (fun _ => ⟨le_rfl, le_rfl⟩) (VDD := 1) ⟨le_rfl, le_rfl⟩ he
    (fun _ _ => rfl) (fun _ _ => rfl) hin h0).1 t ⟨by rw [sheet_tpdINV]; linarith [ht.1], ht.2⟩

end AsmPhys.Witness

namespace AsmPhys.Witness

open AsmPhys.Toy Set

/-- Non-vacuity of THM L3.1 for INV, hypothesis by hypothesis: the toy sheet, inverter, devices,
capacitance, supply, and a trajectory from `0` with the input held low meet every hypothesis of
`IsInverter.propagation`. -/
theorem inv_propagation_hypotheses : ∃ (u : ℝ → Fin 3 → ℝ) (e : ℝ → Fin 1 → ℝ),
    sheet.Consistent ∧ inv.IsInverter (.bdry 2) 0 0 1 (0 : Fin 2) (1 : Fin 2) ∧
    FETContract .n sheet.pn sheet.VDDmax (inv.fet (0 : Fin 2)).I ∧
    FETContract .p sheet.pp sheet.VDDmax (inv.fet (1 : Fin 2)).I ∧
    (∀ v, inv.C 0 v ∈ Icc 1 1) ∧ (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax ∧
    inv.IsTrajOn u e 0 20 ∧ (∀ t ∈ Icc (0 : ℝ) 20, u t 0 = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 20, u t 1 = 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 20, sheet.validIn false (pot (u t) (e t) (.bdry 2))) ∧
    e 0 0 ∈ Icc 0 1 := by
  obtain ⟨e, he, he0⟩ := inv.exists_isTrajOn (Cmin := fun _ => 1) (Cmax := fun _ => 1)
    inv_regular (fun _ => nodeCap_const one_pos) (u := fun _ => ![0, 1, 0]) (a := 0) (b := 20)
    continuousOn_const (by norm_num) 0
  refine ⟨fun _ => ![0, 1, 0], e, sheet_consistent, inv_isInverter, toy_contract .n,
    toy_contract .p, fun _ => ⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩, he, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => ?_, by simp [he0]⟩
  norm_num [Params.validIn, sheet]

/-- The falling case: with the input held high, the toy inverter's output, started at `1`, is
`validOut 0` on `[9, 20]`. -/
theorem inv_falls : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 1]) e 0 20 ∧ e 0 = 1 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut false (e t 0) := by
  obtain ⟨e, he, he0⟩ := inv.exists_isTrajOn (Cmin := fun _ => 1) (Cmax := fun _ => 1)
    inv_regular (fun _ => nodeCap_const one_pos) (u := fun _ => ![0, 1, 1]) (a := 0) (b := 20)
    continuousOn_const (by norm_num) 1
  refine ⟨e, he, he0, fun t ht => ?_⟩
  have hin : ∀ t ∈ Icc (0 : ℝ) 20,
      sheet.validIn true (pot ((fun _ => ![0, 1, 1]) t) (e t) (.bdry 2)) := fun _ _ => by
    norm_num [Params.validIn, sheet]
  have h0 : e 0 0 ∈ Icc 0 1 := by simp [he0]
  exact (inv_isInverter.propagation sheet_consistent (toy_contract .n) (toy_contract .p)
    (Cmin := 1) (Cmax := 1) (fun _ => ⟨le_rfl, le_rfl⟩) (VDD := 1) ⟨le_rfl, le_rfl⟩ he
    (fun _ _ => rfl) (fun _ _ => rfl) hin h0).1 t ⟨by rw [sheet_tpdINV]; linarith [ht.1], ht.2⟩

end AsmPhys.Witness
