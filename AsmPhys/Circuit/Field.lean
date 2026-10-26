import AsmPhys.Circuit.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounds on the nodal vector field

Under C2 for every device and `NodeCap` for every state node, the net channel current `F` and the
vector field `F/C` are globally bounded and globally Lipschitz in the boundary and state
potentials `(u, e)`. Distances on `Fin m → ℝ` and `Fin n → ℝ` are sup norms, and the distance
between pairs `(u, e)` is the larger of the two.
-/

namespace AsmPhys

open Set
open scoped NNReal

variable {n m : ℕ}

/-- A node potential is 1-Lipschitz in the boundary and state potentials jointly. -/
lemma abs_pot_sub_pot_le (u u' : Fin m → ℝ) (e e' : Fin n → ℝ) (x : Node n m) :
    |pot u e x - pot u' e' x| ≤ max ‖u - u'‖ ‖e - e'‖ := by
  cases x with
  | state k =>
    have h := norm_le_pi_norm (e - e') k
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_max_of_le_right h
  | bdry j =>
    have h := norm_le_pi_norm (u - u') j
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_max_of_le_left h

/-- `|x/y − x'/y'| ≤ |x − x'|/c + B·|y − y'|/c²` when `y, y' ≥ c > 0` and `|x'| ≤ B`. -/
lemma abs_div_sub_div_le {x x' y y' c B : ℝ} (hc : 0 < c) (hy : c ≤ y) (hy' : c ≤ y')
    (hx' : |x'| ≤ B) : |x / y - x' / y'| ≤ |x - x'| / c + B * |y - y'| / c ^ 2 := by
  have hy0 : 0 < y := hc.trans_le hy
  have hy0' : 0 < y' := hc.trans_le hy'
  have h : x / y - x' / y' = (x - x') / y + x' * (y' - y) / (y * y') := by
    rw [div_add_div _ _ hy0.ne' (mul_pos hy0 hy0').ne', div_sub_div _ _ hy0.ne' hy0'.ne',
      div_eq_div_iff (mul_pos hy0 hy0').ne' (mul_pos hy0 (mul_pos hy0 hy0')).ne']
    ring
  rw [h]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hy0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hy
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hy0 hy0'), abs_sub_comm y' y, sq]
    exact div_le_div₀ (mul_nonneg ((abs_nonneg _).trans hx') (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hx' (abs_nonneg _)) (mul_pos hc hc)
      (mul_le_mul hy hy' hc.le hy0.le)

namespace FET

/-- If the device function is `L`-Lipschitz, the channel current is `L`-Lipschitz in `(u, e)`. -/
lemma abs_current_sub_current_le {f : FET n m} {L : ℝ≥0}
    (hf : LipschitzWith L fun x : ℝ × ℝ × ℝ => f.I x.1 x.2.1 x.2.2)
    (u u' : Fin m → ℝ) (e e' : Fin n → ℝ) :
    |f.current u e - f.current u' e'| ≤ L * max ‖u - u'‖ ‖e - e'‖ := by
  have h := hf.dist_le_mul (pot u e f.g, pot u e f.d, pot u e f.s)
    (pot u' e' f.g, pot u' e' f.d, pot u' e' f.s)
  simp only [Real.dist_eq, Prod.dist_eq] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
  exact max_le (abs_pot_sub_pot_le u u' e e' _)
    (max_le (abs_pot_sub_pot_le u u' e e' _) (abs_pot_sub_pot_le u u' e e' _))

/-- Under C2, the channel current is bounded. -/
lemma exists_abs_current_le {f : FET n m} (hf : Regular f.I) :
    ∃ B, 0 ≤ B ∧ ∀ u e, |f.current u e| ≤ B := by
  obtain ⟨B, hB⟩ := hf.bdd
  exact ⟨B, (abs_nonneg _).trans (hB 0 0 0), fun u e => hB _ _ _⟩

end FET

namespace Netlist

variable (N : Netlist n m)

private lemma abs_ite_sub_ite_sub_le (P Q : Prop) [Decidable P] [Decidable Q] (c c' : ℝ) :
    |((if P then c else 0) - (if Q then c else 0)) -
      ((if P then c' else 0) - (if Q then c' else 0))| ≤ 2 * |c - c'| := by
  have h := abs_le.1 (le_refl |c - c'|)
  split_ifs <;> refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [h.1, h.2]

private lemma abs_ite_sub_ite_le (P Q : Prop) [Decidable P] [Decidable Q] {c B : ℝ}
    (hc : |c| ≤ B) : |(if P then c else 0) - (if Q then c else 0)| ≤ 2 * B := by
  have h := abs_le.1 hc
  split_ifs <;> refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [h.1, h.2]

/-- If device `i` is `Lᵢ`-Lipschitz, the net channel current into each state node is Lipschitz in
`(u, e)` with constant `2 ∑ᵢ Lᵢ`. -/
lemma abs_F_sub_F_le {L : Fin N.nf → ℝ≥0}
    (hL : ∀ i, LipschitzWith (L i) fun x : ℝ × ℝ × ℝ => (N.fet i).I x.1 x.2.1 x.2.2)
    (u u' : Fin m → ℝ) (e e' : Fin n → ℝ) (k : Fin n) :
    |N.F u e k - N.F u' e' k| ≤ (∑ i, 2 * (L i : ℝ)) * max ‖u - u'‖ ‖e - e'‖ := by
  simp only [F]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (abs_ite_sub_ite_sub_le _ _ _ _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((N.fet i).abs_current_sub_current_le (hL i) u u' e e')
    zero_le_two

/-- Under C2 for every device, the net channel current is Lipschitz in `(u, e)`, uniformly in
the node. -/
lemma exists_abs_F_sub_F_le (hreg : ∀ i, Regular (N.fet i).I) :
    ∃ L, 0 ≤ L ∧ ∀ u u' e e' k, |N.F u e k - N.F u' e' k| ≤ L * max ‖u - u'‖ ‖e - e'‖ := by
  choose L hL using fun i => (hreg i).lipschitz
  exact ⟨_, Finset.sum_nonneg fun i _ => by positivity, N.abs_F_sub_F_le hL⟩

/-- Under C2 for every device, the net channel current is bounded, uniformly in the node. -/
lemma exists_abs_F_le (hreg : ∀ i, Regular (N.fet i).I) :
    ∃ B, 0 ≤ B ∧ ∀ u e k, |N.F u e k| ≤ B := by
  choose B hB0 hB using fun i => (N.fet i).exists_abs_current_le (hreg i)
  refine ⟨∑ i, 2 * B i, Finset.sum_nonneg fun i _ => mul_nonneg zero_le_two (hB0 i),
    fun u e k => ?_⟩
  simp only [F]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => abs_ite_sub_ite_le _ _ (hB i u e))

/-- Under C2 for every device and `NodeCap` for every state node, the vector field is globally
Lipschitz in `(u, e)`. -/
lemma exists_norm_vf_sub_vf_le {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :
    ∃ K : ℝ≥0, ∀ u u' e e', ‖N.vf u e - N.vf u' e'‖ ≤ K * max ‖u - u'‖ ‖e - e'‖ := by
  obtain ⟨LF, hLF0, hLF⟩ := N.exists_abs_F_sub_F_le hreg
  obtain ⟨B, hB0, hB⟩ := N.exists_abs_F_le hreg
  choose KC hKC using fun k => (hcap k).lipschitz
  have hc : ∀ k, 0 ≤ LF / Cmin k + B * KC k / Cmin k ^ 2 := fun k =>
    add_nonneg (div_nonneg hLF0 (hcap k).pos.le)
      (div_nonneg (mul_nonneg hB0 (KC k).coe_nonneg) (sq_nonneg _))
  have hsum : 0 ≤ ∑ k, (LF / Cmin k + B * KC k / Cmin k ^ 2) :=
    Finset.sum_nonneg fun k _ => hc k
  refine ⟨(∑ k, (LF / Cmin k + B * KC k / Cmin k ^ 2)).toNNReal, fun u u' e e' => ?_⟩
  rw [Real.coe_toNNReal _ hsum]
  have hD : 0 ≤ max ‖u - u'‖ ‖e - e'‖ := le_max_of_le_left (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum hD)).2 fun k => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hC : |N.C k (e k) - N.C k (e' k)| ≤ KC k * max ‖u - u'‖ ‖e - e'‖ := by
    have h := (hKC k).dist_le_mul (e k) (e' k)
    rw [Real.dist_eq, Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_pot_sub_pot_le u u' e e' (.state k))
      (KC k).coe_nonneg)
  calc |N.vf u e k - N.vf u' e' k|
      ≤ |N.F u e k - N.F u' e' k| / Cmin k + B * |N.C k (e k) - N.C k (e' k)| / Cmin k ^ 2 :=
        abs_div_sub_div_le (hcap k).pos ((hcap k).range _).1 ((hcap k).range _).1 (hB u' e' k)
    _ ≤ LF * max ‖u - u'‖ ‖e - e'‖ / Cmin k
          + B * (KC k * max ‖u - u'‖ ‖e - e'‖) / Cmin k ^ 2 :=
        add_le_add (div_le_div_of_nonneg_right (hLF u u' e e' k) (hcap k).pos.le)
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hC hB0) (sq_nonneg _))
    _ = (LF / Cmin k + B * KC k / Cmin k ^ 2) * max ‖u - u'‖ ‖e - e'‖ := by ring
    _ ≤ (∑ k, (LF / Cmin k + B * KC k / Cmin k ^ 2)) * max ‖u - u'‖ ‖e - e'‖ :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ k)) hD

/-- Under C2 for every device and `NodeCap` for every state node, the vector field is globally
Lipschitz in the state and in the boundary potentials, with one constant. -/
lemma exists_lipschitzWith_vf {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :
    ∃ K : ℝ≥0, (∀ u, LipschitzWith K (N.vf u)) ∧ ∀ e, LipschitzWith K fun u => N.vf u e := by
  obtain ⟨K, hK⟩ := N.exists_norm_vf_sub_vf_le hreg hcap
  refine ⟨K, fun u => LipschitzWith.of_dist_le_mul fun e e' => ?_,
    fun e => LipschitzWith.of_dist_le_mul fun u u' => ?_⟩
  · rw [dist_eq_norm, dist_eq_norm]
    exact (hK u u e e').trans_eq (by rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)])
  · rw [dist_eq_norm, dist_eq_norm]
    exact (hK u u' e e).trans_eq (by rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)])

/-- Under C2 for every device and `NodeCap` for every state node, the vector field is globally
bounded. -/
lemma exists_norm_vf_le {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :
    ∃ B : ℝ≥0, ∀ u e, ‖N.vf u e‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := N.exists_abs_F_le hreg
  have hc : ∀ k, 0 ≤ B / Cmin k := fun k => div_nonneg hB0 (hcap k).pos.le
  have hsum : 0 ≤ ∑ k, B / Cmin k := Finset.sum_nonneg fun k _ => hc k
  refine ⟨(∑ k, B / Cmin k).toNNReal, fun u e => ?_⟩
  rw [Real.coe_toNNReal _ hsum]
  refine (pi_norm_le_iff_of_nonneg hsum).2 fun k => ?_
  rw [Real.norm_eq_abs]
  calc |N.vf u e k| = |N.F u e k| / N.C k (e k) := by
        rw [vf, abs_div, abs_of_pos (N.C_pos k _)]
    _ ≤ B / Cmin k := div_le_div₀ hB0 (hB u e k) (hcap k).pos ((hcap k).range _).1
    _ ≤ ∑ k, B / Cmin k := Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ k)

end Netlist

end AsmPhys
