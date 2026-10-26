import AsmPhys.Spec.Levels
import AsmPhys.Design.Latch
import AsmPhys.Spec.Params

/-!
# Logic and latch levels

K0 makes the output levels strictly inside the input levels, with noise margins `NM_L` and `NM_H`.
The latch levels `θ_L` and `θ_H` (`AsmPhys.Design.Latch`) sit inside the logic levels with margin
`δ₀` on every side.
-/

namespace AsmPhys

namespace Params

variable {S : Params}

/-- A valid output level is a valid input level (K0). -/
theorem Consistent.validIn_of_validOut (hS : S.Consistent) {b : Bool} {v : ℝ}
    (h : S.validOut b v) : S.validIn b v := by
  obtain ⟨-, h1, -, h3, -⟩ := hS.K0
  cases b
  · exact h.trans h1.le
  · exact h3.le.trans h

/-- No voltage reads as both bits (K0). -/
theorem Consistent.not_validIn_both (hS : S.Consistent) {v : ℝ} :
    ¬(S.validIn false v ∧ S.validIn true v) := by
  rintro ⟨h0, h1⟩
  obtain ⟨-, -, h2, -⟩ := hS.K0
  exact absurd (h1.trans h0) (not_le.2 h2)

variable (S)

/-- Band width `δ₀ = min(NM_L, NM_H)/2`, the margin between the latch levels and the logic levels. -/
noncomputable def δ₀ : ℝ := min S.NML S.NMH / 2

variable {S}

/-- The latch levels sit strictly inside the logic levels, with margin `δ₀ > 0` on every side. -/
theorem Consistent.band (hS : S.Consistent) :
    0 < S.δ₀ ∧ S.VOL + S.δ₀ ≤ S.θL ∧ S.θL + S.δ₀ ≤ S.VIL ∧ S.VIH + S.δ₀ ≤ S.θH ∧
      S.θH + S.δ₀ ≤ S.VOH := by
  obtain ⟨-, h1, -, h3, -⟩ := hS.K0
  have hL : min S.NML S.NMH ≤ S.VIL - S.VOL := min_le_left _ _
  have hH : min S.NML S.NMH ≤ S.VOH - S.VIH := min_le_right _ _
  have hpos : 0 < min S.NML S.NMH := lt_min (sub_pos.2 h1) (sub_pos.2 h3)
  simp only [δ₀, θL, θH]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Params

end AsmPhys
