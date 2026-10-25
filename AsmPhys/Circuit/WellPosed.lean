import AsmPhys.Circuit.Field
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

/-!
# THM L2.2 and THM L2.4 — Well-posedness and continuous dependence

Under C2 for every device and a Lipschitz capacitance law with values in `[C_k^min, C_k^max]`
for every state node, the nodal vector field `F/C` is continuous in `t`, globally Lipschitz in
`e` and in `u`, and globally bounded (C2 makes `F` bounded as well as Lipschitz). Picard–Lindelöf
gives a unique trajectory on `[a, b]` from each initial state, and Grönwall gives Lipschitz
dependence on the initial state and on the boundary waveform in the sup norm over `[a, b]`.
-/

namespace AsmPhys

open Set
open scoped NNReal

/-- `gronwallBound δ K ε x ≤ exp (K x)·δ + ε·x·exp (K x)` for `K, ε ≥ 0`. -/
lemma gronwallBound_le_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ Real.exp (K * x) * δ + ε * x * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hK
  · rw [gronwallBound_K0]
    simp
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have hexp : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K * x)))
      (Real.exp_pos (K * x)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    linarith
  have h : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) :=
    calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
          mul_le_mul_of_nonneg_left hexp (div_nonneg hε hK.le)
      _ = ε * x * Real.exp (K * x) := by
          rw [div_mul_eq_mul_div, div_eq_iff hK.ne']
          ring
  linarith

namespace Netlist

variable {n m : ℕ} (N : Netlist n m)

/-- **THM L2.2** (well-posedness), existence: for continuous boundary waveforms, every initial
state has a trajectory on `[a, b]`. -/
theorem exists_isTrajOn {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))        -- MEAS range, MODEL Lipschitz law
    {u : ℝ → Fin m → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b))                        -- ENV
    (hab : a ≤ b) (e₀ : Fin n → ℝ) :
    ∃ e, N.IsTrajOn u e a b ∧ e a = e₀ := by
  obtain ⟨K, hKe, hKu⟩ := N.exists_lipschitzWith_vf hreg hcap
  obtain ⟨B, hB⟩ := N.exists_norm_vf_le hreg hcap
  have hPL : IsPicardLindelof (fun t => N.vf (u t)) (⟨a, left_mem_Icc.2 hab⟩ : Icc a b) e₀
      (B * (b - a).toNNReal) 0 B K :=
    { lipschitzOnWith := fun t _ => (hKe (u t)).lipschitzOnWith
      continuousOn := fun x _ => (hKu x).continuous.comp_continuousOn hu
      norm_le := fun t _ x _ => hB (u t) x
      mul_max_le := by
        have h1 : ((B * (b - a).toNNReal : ℝ≥0) : ℝ) = B * (b - a) := by
          rw [NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.2 hab)]
        have h2 : max (b - a) (a - a) = b - a := max_eq_left (by linarith)
        simp only [h1, h2, NNReal.coe_zero, sub_zero, le_refl] }
  obtain ⟨e, he0, he⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨e, ⟨fun t ht => (he t ht).continuousWithinAt,
    fun t ht => (he t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)⟩, he0⟩

/-- **THM L2.2** (well-posedness), uniqueness: two trajectories on `[a, b]` with the same
initial state agree on `[a, b]`. -/
theorem isTrajOn_unique {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))        -- MEAS range, MODEL Lipschitz law
    {u : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b) (he' : N.IsTrajOn u e' a b) (h : e a = e' a) :
    EqOn e e' (Icc a b) := by
  obtain ⟨K, hKe, -⟩ := N.exists_lipschitzWith_vf hreg hcap
  exact ODE_solution_unique_of_mem_Icc_right (v := fun t => N.vf (u t)) (s := fun _ => univ)
    (fun t _ => (hKe (u t)).lipschitzOnWith) he.continuousOn he.hasDerivWithinAt
    (fun _ _ => mem_univ _) he'.continuousOn he'.hasDerivWithinAt (fun _ _ => mem_univ _) h

/-- **THM L2.4** (continuous dependence), Grönwall form: there are constants `K` (Lipschitz in the
state) and `Lu` (Lipschitz in the boundary waveform), depending only on the netlist, such that
trajectories driven by waveforms within `δ` of each other on `[a, b]` stay within the Grönwall
bound. -/
theorem exists_dist_le_gronwallBound {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :      -- MEAS range, MODEL Lipschitz law
    ∃ K Lu : ℝ≥0, ∀ {u u' : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b δ : ℝ},
      N.IsTrajOn u e a b → N.IsTrajOn u' e' a b →
      (∀ t ∈ Icc a b, ‖u t - u' t‖ ≤ δ) →
      ∀ t ∈ Icc a b, ‖e t - e' t‖ ≤ gronwallBound ‖e a - e' a‖ K (Lu * δ) (t - a) := by
  obtain ⟨K, hKe, hKu⟩ := N.exists_lipschitzWith_vf hreg hcap
  refine ⟨K, K, fun {u u' e e' a b δ} he he' hδ t ht => ?_⟩
  have h := dist_le_of_approx_trajectories_ODE (v := fun t => N.vf (u t)) (εf := 0)
    (εg := K * δ) (fun t => hKe (u t)) he.continuousOn he.hasDerivWithinAt
    (fun t _ => (dist_self _).le) he'.continuousOn he'.hasDerivWithinAt
    (fun t ht => ?_) le_rfl t ht
  · simpa only [dist_eq_norm, zero_add] using h
  · calc dist (N.vf (u' t) (e' t)) (N.vf (u t) (e' t)) ≤ K * dist (u' t) (u t) :=
          (hKu (e' t)).dist_le_mul _ _
      _ ≤ K * δ := by
          rw [dist_eq_norm, norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hδ t (Ico_subset_Icc_self ht)) K.coe_nonneg

/-- **THM L2.4** (continuous dependence): the state at time `t ∈ [a, b]` depends
Lipschitz-continuously on the initial state and on the boundary waveform in the sup norm over
`[a, b]`, with constants depending only on the netlist and on `t − a`. -/
theorem exists_lipschitz_dependence {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :      -- MEAS range, MODEL Lipschitz law
    ∃ K Lu : ℝ≥0, ∀ {u u' : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b δ : ℝ},
      N.IsTrajOn u e a b → N.IsTrajOn u' e' a b →
      (∀ t ∈ Icc a b, ‖u t - u' t‖ ≤ δ) →
      ∀ t ∈ Icc a b, ‖e t - e' t‖ ≤
        Real.exp (K * (t - a)) * ‖e a - e' a‖ + Lu * (t - a) * Real.exp (K * (t - a)) * δ := by
  obtain ⟨K, Lu, h⟩ := N.exists_dist_le_gronwallBound hreg hcap
  refine ⟨K, Lu, fun {u u' e e' a b δ} he he' hδ t ht => ?_⟩
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ a ⟨le_rfl, ht.1.trans ht.2⟩)
  refine (h he he' hδ t ht).trans
    ((gronwallBound_le_exp K.coe_nonneg (mul_nonneg Lu.coe_nonneg hδ0)).trans_eq ?_)
  ring

end Netlist

end AsmPhys
