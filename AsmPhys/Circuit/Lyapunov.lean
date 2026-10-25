import AsmPhys.Circuit.Charge

/-!
# Reaching a target with a Lyapunov function

A function `Φ` that is positive off a target and decreases at rate at least `1` there forces the
target to be reached within time `Φ(t₀)`. Settling arguments for two-node clusters use maxima and
minima of node potentials, so the right derivative of a maximum is recorded with that of a minimum.
-/

namespace AsmPhys

open Set

/-- Right derivative of a maximum: where `g < f` it is `f'`, where `f < g` it is `g'`, and where
they are equal it is `max f' g'`. -/
theorem HasDerivWithinAt.max_Ici {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivWithinAt f f' (Ici t) t) (hg : HasDerivWithinAt g g' (Ici t) t) :
    HasDerivWithinAt (fun s => max (f s) (g s))
      (if g t < f t then f' else if f t < g t then g' else max f' g') (Ici t) t := by
  have h := (HasDerivWithinAt.min_Ici hf.neg hg.neg).neg
  simp only [Pi.neg_apply, neg_lt_neg_iff, min_neg_neg] at h
  convert h using 1
  · ext s; simp
  · split_ifs <;> simp

/-- **Lyapunov reach.** If `Φ` is positive and decreases at rate at least `1` wherever the target
`P` fails, then `P` holds at some time in `[t₀, t₀ + max 0 (Φ t₀)]`, provided the interval fits. -/
theorem reach_of_lyapunov {Φ Φ' : ℝ → ℝ} {P : ℝ → Prop} {t₀ t₁ : ℝ}
    (hΦ : ContinuousOn Φ (Icc t₀ t₁))
    (hΦ' : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt Φ (Φ' t) (Ici t) t)
    (hdec : ∀ t ∈ Ico t₀ t₁, ¬ P t → Φ' t ≤ -1)
    (hpos : ∀ t ∈ Icc t₀ t₁, ¬ P t → 0 < Φ t)
    (hT : t₀ + max 0 (Φ t₀) ≤ t₁) :
    ∃ t ∈ Icc t₀ (t₀ + max 0 (Φ t₀)), P t := by
  by_contra hP
  push Not at hP
  set T := t₀ + max 0 (Φ t₀) with hTdef
  have hT₀ : t₀ ≤ T := le_add_of_nonneg_right (le_max_left _ _)
  have h₀ : 0 < Φ t₀ := hpos t₀ ⟨le_rfl, hT₀.trans hT⟩ (hP t₀ ⟨le_rfl, hT₀⟩)
  have hTΦ : T = t₀ + Φ t₀ := by rw [hTdef, max_eq_right h₀.le]
  have hIco : Ico t₀ T ⊆ Ico t₀ t₁ := Ico_subset_Ico_right hT
  -- `Φ` decreases at rate at least `1` on `[t₀, T]`, so `Φ T ≤ Φ t₀ - (T - t₀) = 0`.
  have hle := image_le_of_deriv_right_le_deriv_boundary (hΦ.mono (Icc_subset_Icc_right hT))
    (fun t ht => hΦ' t (hIco ht)) (B := fun t => Φ t₀ - (t - t₀)) (B' := fun _ => -1)
    (by simp) (by fun_prop)
    (fun t _ => by simpa using ((hasDerivWithinAt_id t (Ici t)).sub_const t₀).const_sub (Φ t₀))
    (fun t ht => hdec t (hIco ht) (hP t (Ico_subset_Icc_self ht)))
    (right_mem_Icc.2 hT₀)
  have hΦT := hpos T ⟨hT₀, hT⟩ (hP T (right_mem_Icc.2 hT₀))
  linarith

end AsmPhys
