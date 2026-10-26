import AsmPhys.Circuit.Rails
import AsmPhys.Spec.Params

/-!
# Local currents

`N.inflow u e k i` is the current transistor `i` carries into state node `k`, so `N.F` is the sum of
the inflows over the transistors touching `k`. Cells are analysed one node at a time through this
decomposition, never by unfolding `N.F` over the whole netlist. Passivity fixes the sign of an
inflow from the far terminal's potential.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

namespace Netlist

variable {N : Netlist n m}

/-- Current that transistor `i` carries into state node `k`: its channel current if its source is
at `k`, minus it if its drain is at `k`. -/
def inflow (N : Netlist n m) (u : Fin m → ℝ) (e : Fin n → ℝ) (k : Fin n) (i : Fin N.nf) : ℝ :=
  (if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
    (if (N.fet i).d = .state k then (N.fet i).current u e else 0)

/-- If every transistor with a channel terminal at `k` lies in `T`, the net current into `k` is the
sum of the inflows over `T`. -/
theorem F_eq_sum_inflow {k : Fin n} {T : Finset (Fin N.nf)}
    (hT : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → i ∈ T)
    (u : Fin m → ℝ) (e : Fin n → ℝ) : N.F u e k = ∑ i ∈ T, N.inflow u e k i := by
  change ∑ i, N.inflow u e k i = _
  refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
  have hs : (N.fet i).s ≠ .state k := fun h => hi (hT i (.inr h))
  have hd : (N.fet i).d ≠ .state k := fun h => hi (hT i (.inl h))
  simp [inflow, hs, hd]

/-- Passive regular transistors whose far terminals are no higher than `k` carry no net current
into `k`. -/
theorem sum_inflow_nonpos {k : Fin n} {T : Finset (Fin N.nf)} {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hpr : ∀ i ∈ T, Passive (N.fet i).I ∧ Regular (N.fet i).I)
    (hfar : ∀ i ∈ T, ((N.fet i).s = .state k → pot u e (N.fet i).d ≤ e k) ∧
      ((N.fet i).d = .state k → pot u e (N.fet i).s ≤ e k)) :
    ∑ i ∈ T, N.inflow u e k i ≤ 0 := by
  refine Finset.sum_nonpos fun i hi => ?_
  obtain ⟨hP, hR⟩ := hpr i hi
  obtain ⟨hs, hd⟩ := hfar i hi
  unfold inflow FET.current
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact hP.nonpos_of_le hR (hs h1)
  · rw [h2, pot_state, zero_sub, neg_nonpos]
    exact hP.nonneg_of_le hR (hd h2)
  · simp

/-- Passive regular transistors whose far terminals are no lower than `k` carry no net current
out of `k`. -/
theorem sum_inflow_nonneg {k : Fin n} {T : Finset (Fin N.nf)} {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hpr : ∀ i ∈ T, Passive (N.fet i).I ∧ Regular (N.fet i).I)
    (hfar : ∀ i ∈ T, ((N.fet i).s = .state k → e k ≤ pot u e (N.fet i).d) ∧
      ((N.fet i).d = .state k → e k ≤ pot u e (N.fet i).s)) :
    0 ≤ ∑ i ∈ T, N.inflow u e k i := by
  refine Finset.sum_nonneg fun i hi => ?_
  obtain ⟨hP, hR⟩ := hpr i hi
  obtain ⟨hs, hd⟩ := hfar i hi
  unfold inflow FET.current
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact hP.nonneg_of_le hR (hs h1)
  · rw [h2, pot_state, zero_sub, neg_nonneg]
    exact hP.nonpos_of_le hR (hd h2)
  · simp

/-- Every transistor in `T` meets the contract of its polarity, with the sheet's parameters. -/
def ContractOn (N : Netlist n m) (S : Params) (T : Finset (Fin N.nf)) : Prop :=
  ∀ i ∈ T, FETContract (N.fet i).pol (S.par (N.fet i).pol) S.VDDmax (N.fet i).I

end Netlist

end AsmPhys
