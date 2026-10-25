import AsmPhys.Circuit.Rails
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Node charge along trajectories

A state node with capacitance law `C` carries charge `q(v) = ∫₀ᵛ C`, so `q' = C` and, along a
trajectory, `d/dt q(e_k) = C(e_k)·ė_k = F_k`: the net channel current. Sums of node charges are
what charge sharing conserves, and the hold tubes of series stacks and of leaky latches are level
sets of such sums (docs/SPIKE-FLIPFLOP.md, stage 3 and the v1 NAND2/NOR2 work). With
`C ∈ [C^min, C^max]`, `C^min·v ≤ q(v) ≤ C^max·v` for `v ≥ 0`.

Charge-sharing tubes also take minima of node potentials, so the right derivative of a minimum
is recorded here as well.
-/

namespace AsmPhys

open Set Filter Topology

/-- Charge of a node with capacitance law `C` at potential `v`: `q(v) = ∫₀ᵛ C`. -/
noncomputable def charge (C : ℝ → ℝ) (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, C s

/-- With a continuous capacitance law, `q' = C`. -/
theorem hasDerivAt_charge {C : ℝ → ℝ} (hC : Continuous C) (v : ℝ) :
    HasDerivAt (charge C) (C v) v :=
  (hC.integral_hasStrictDerivAt 0 v).hasDerivAt

/-- With `C ∈ [C^min, C^max]` and `v ≥ 0`, `C^min·v ≤ q(v) ≤ C^max·v`. -/
theorem charge_mem_Icc {C : ℝ → ℝ} {Cmin Cmax : ℝ} (hC : Continuous C)
    (hr : ∀ v, C v ∈ Icc Cmin Cmax) {v : ℝ} (hv : 0 ≤ v) :
    charge C v ∈ Icc (Cmin * v) (Cmax * v) := by
  have hi : IntervalIntegrable C MeasureTheory.volume 0 v := hC.intervalIntegrable 0 v
  have h₁ := intervalIntegral.integral_mono_on hv intervalIntegrable_const hi fun x _ => (hr x).1
  have h₂ := intervalIntegral.integral_mono_on hv hi intervalIntegrable_const fun x _ => (hr x).2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- With positive capacitance, charge is strictly increasing in the potential. -/
theorem strictMono_charge {C : ℝ → ℝ} (hC : Continuous C) (hpos : ∀ v, 0 < C v) :
    StrictMono (charge C) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_charge hC) hpos

/-- Along a trajectory, a node's charge has right derivative equal to the net channel current
into it, when its capacitance law is continuous. -/
theorem Netlist.IsTrajOn.hasDerivWithinAt_charge {n m : ℕ} {N : Netlist n m}
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ} (he : N.IsTrajOn u e a b) (k : Fin n)
    (hC : Continuous (N.C k)) :
    ∀ t ∈ Ico a b,
      HasDerivWithinAt (fun t => charge (N.C k) (e t k)) (N.F (u t) (e t) k) (Ici t) t := by
  intro t ht
  have h := (hasDerivAt_charge hC (e t k)).comp_hasDerivWithinAt t
    (hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) k)
  rwa [Netlist.vf, mul_div_cancel₀ _ (N.C_pos k (e t k)).ne'] at h

/-- Right derivative of a minimum: where `f < g` it is `f'`, where `g < f` it is `g'`, and where
they are equal it is `min f' g'`. -/
theorem HasDerivWithinAt.min_Ici {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivWithinAt f f' (Ici t) t) (hg : HasDerivWithinAt g g' (Ici t) t) :
    HasDerivWithinAt (fun s => min (f s) (g s))
      (if f t < g t then f' else if g t < f t then g' else min f' g') (Ici t) t := by
  split_ifs with h₁ h₂
  · exact hf.congr_of_eventuallyEq
      ((hf.continuousWithinAt.eventually_lt hg.continuousWithinAt h₁).mono fun s hs =>
        min_eq_left hs.le) (min_eq_left h₁.le)
  · exact hg.congr_of_eventuallyEq
      ((hg.continuousWithinAt.eventually_lt hf.continuousWithinAt h₂).mono fun s hs =>
        min_eq_right hs.le) (min_eq_right h₂.le)
  · have hfg : f t = g t := le_antisymm (not_lt.1 h₂) (not_lt.1 h₁)
    refine HasDerivWithinAt.of_isLittleO <| (Asymptotics.IsBigO.of_bound' ?_).trans_isLittleO
      (hf.isLittleO.norm_left.add hg.isLittleO.norm_left)
    filter_upwards [self_mem_nhdsWithin] with s (hst : t ≤ s)
    have key : min (f t + (s - t) * f') (g t + (s - t) * g') =
        min (f t) (g t) + (s - t) * min f' g' := by
      rw [hfg, min_self, min_add_add_left, mul_min_of_nonneg _ _ (sub_nonneg.2 hst)]
    simp only [Real.norm_eq_abs, smul_eq_mul]
    calc |min (f s) (g s) - min (f t) (g t) - (s - t) * min f' g'|
        = |min (f s) (g s) - min (f t + (s - t) * f') (g t + (s - t) * g')| := by
          rw [key, sub_sub]
      _ ≤ max |f s - (f t + (s - t) * f')| |g s - (g t + (s - t) * g')| :=
          abs_min_sub_min_le_max _ _ _ _
      _ ≤ |f s - f t - (s - t) * f'| + |g s - g t - (s - t) * g'| := by
          simp only [sub_sub]
          exact max_le (le_add_of_nonneg_right (abs_nonneg _))
            (le_add_of_nonneg_left (abs_nonneg _))
      _ ≤ _ := le_abs_self _

end AsmPhys
