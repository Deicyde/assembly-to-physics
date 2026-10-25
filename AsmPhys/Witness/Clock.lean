import AsmPhys.Cells.FlipFlop
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Non-vacuity of the adopted ClockOK

The adopted `ClockOK` (FINDINGS F1, F6) adds constraints to the spec's condition, so it must still
be satisfiable. For every sheet satisfying K0–K14 and every supply in range, edges at `k·T_clk`
with a continuous, `T_clk`-periodic, piecewise-linear clock meet `EdgesOK` and `ClockOK`. With
slope `a = (V_DD − V_IL)/t_slew`, the clock equals `V_IL` at each edge, rises to `V_DD` over
`t_slew`, stays at `V_DD` for `t_high`, falls with slope `a` through `V_IL` at
`2·t_slew + t_high` after the edge, is clamped at `0`, and climbs back with slope `a` to `V_IL` at
the next edge. K12 and K14 make the phases fit in one period, and `V_IL` at both ends of the
period makes the periodic extension continuous.
-/

namespace AsmPhys.Witness

open Set

/-- A continuous clock meeting the adopted ClockOK exists, with edges `k·T_clk`. -/
theorem exists_clockOK {S : Params} (hS : S.Consistent) {VDD : ℝ}
    (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) :
    ∃ clk : ℝ → ℝ, Continuous clk ∧
      EdgesOK S (fun k => k * S.Tclk) (fun k => k * S.Tclk) ∧
      ClockOK S VDD clk (fun k => k * S.Tclk) := by
  obtain ⟨hOL, hOLIL, hILIH, hIHOH, hOHmin⟩ := hS.K0
  obtain ⟨hslew, hlow, hhigh, hsmax, -⟩ := hS.K14
  have hK12 := hS.K12
  have hVmin := hVDD.1
  set T := S.Tclk with hT
  set w := 2 * S.tslew + S.thigh with hw
  have hTpos : 0 < T := by linarith
  have hwT : w ≤ T := by linarith
  have hIL : 0 < S.VIL := by linarith
  have hVDDIL : S.VIL < VDD := by linarith
  have hVDDIH : S.VIH ≤ VDD := by linarith
  set a := (VDD - S.VIL) / S.tslew with ha
  have hapos : 0 < a := div_pos (by linarith) hslew
  have hat : a * S.tslew = VDD - S.VIL := by rw [ha]; field_simp
  -- The profile on one period `[0, T]`: `V_IL + a·g` clamped to `[0, V_DD]`, where `g` is the
  -- tent `min x (w − x)` raised near `T` by `x − T`.
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ,
      ∀ x, f x = max 0 (min VDD (S.VIL + a * max (min x (w - x)) (x - T))) :=
    ⟨_, fun _ => rfl⟩
  have hfc : Continuous f := by
    rw [show f = _ from funext hfdef]
    fun_prop
  have hfrail : ∀ x, f x ∈ Icc 0 VDD := fun x => by
    rw [hfdef]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfIL : ∀ x, max (min x (w - x)) (x - T) = 0 → f x = S.VIL := fun x hx => by
    rw [hfdef, hx, mul_zero, add_zero, min_eq_right hVDDIL.le, max_eq_right hIL.le]
  have hf0 : f 0 = S.VIL :=
    hfIL 0 (by rw [min_eq_left (by linarith), max_eq_left (by linarith)])
  have hfT : f T = S.VIL :=
    hfIL T (by rw [sub_self, max_eq_right ((min_le_right _ _).trans (by linarith))])
  have hfle : ∀ x, w ≤ x → x ≤ T → f x ≤ S.VIL := fun x h1 h2 => by
    rw [hfdef]
    have hg : max (min x (w - x)) (x - T) ≤ 0 :=
      max_le ((min_le_right _ _).trans (by linarith)) (by linarith)
    have := mul_le_mul_of_nonneg_left hg hapos.le
    rw [mul_zero] at this
    exact max_le hIL.le ((min_le_right _ _).trans (by linarith))
  have hfpin : ∀ x, 0 < x → x ≤ S.tslew → S.VIL < f x := fun x h1 h2 => by
    rw [hfdef]
    have hg : 0 < max (min x (w - x)) (x - T) :=
      lt_max_of_lt_left (lt_min h1 (by linarith))
    have := mul_pos hapos hg
    exact lt_max_of_lt_right (lt_min hVDDIL (by linarith))
  have hfhigh : ∀ x, S.tslew ≤ x → x ≤ S.tslew + S.thigh → S.VIH ≤ f x := fun x h1 h2 => by
    rw [hfdef]
    have hg : S.tslew ≤ max (min x (w - x)) (x - T) :=
      le_max_of_le_left (le_min h1 (by linarith))
    have := mul_le_mul_of_nonneg_left hg hapos.le
    exact le_max_of_le_right (le_min hVDDIH (by linarith))
  -- The clock: the profile repeated with period `T`.
  obtain ⟨clk, hclkdef⟩ : ∃ clk : ℝ → ℝ, ∀ t, clk t = f (T * Int.fract (t / T)) :=
    ⟨_, fun _ => rfl⟩
  have hclk : ∀ (j : ℤ) (t : ℝ), (j : ℝ) * T ≤ t → t < (j : ℝ) * T + T →
      clk t = f (t - (j : ℝ) * T) := by
    intro j t h1 h2
    have hfr : Int.fract (t / T) = (t - j * T) / T := by
      rw [Int.fract_eq_iff]
      refine ⟨div_nonneg (by linarith) hTpos.le, (div_lt_one hTpos).2 (by linarith), j, ?_⟩
      field_simp
      ring
    rw [hclkdef, hfr]
    congr 1
    field_simp
  refine ⟨clk, ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun y => f (T * y)) (Icc 0 1) := by
      apply Continuous.continuousOn
      fun_prop
    have h2 := ContinuousOn.comp_fract'' h1 (by simp only [mul_zero, mul_one, hf0, hfT])
    rw [show clk = ((fun y => f (T * y)) ∘ Int.fract) ∘ (fun t => t / T) from
      funext fun t => hclkdef t]
    exact h2.comp (continuous_id.div_const T)
  · refine ⟨fun k => ?_, fun k => ⟨le_rfl, by linarith⟩⟩
    push_cast
    linarith
  · refine ⟨?_, ?_, ?_, ?_, fun t => by rw [hclkdef]; exact hfrail _⟩
    · -- low: `t ∈ [kT − t_low, kT]`
      intro k t ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with h | h
      · rw [hclk k t (by push_cast; linarith) (by push_cast; linarith)]
        push_cast
        rw [h, sub_self, hf0]
      · rw [hclk ((k : ℤ) - 1) t (by push_cast; linarith) (by push_cast; linarith)]
        push_cast
        exact hfle _ (by linarith) (by linarith)
    · -- low_between: `t ∈ [kT + w, (k+1)T]`
      intro k t ⟨h1, h2⟩
      push_cast at h2
      rcases eq_or_lt_of_le h2 with h | h
      · rw [hclk ((k : ℤ) + 1) t (by push_cast; linarith) (by push_cast; linarith)]
        push_cast
        rw [h, sub_self, hf0]
      · rw [hclk k t (by push_cast; linarith) (by push_cast; linarith)]
        push_cast
        exact hfle _ (by linarith) (by linarith)
    · -- pin: `t ∈ (kT, kT + t_slew]`
      intro k t ⟨h1, h2⟩
      rw [hclk k t (by push_cast; linarith) (by push_cast; linarith)]
      push_cast
      exact hfpin _ (by linarith) (by linarith)
    · -- high: `t ∈ [kT + t_slew, kT + t_slew + t_high]`
      intro k t ⟨h1, h2⟩
      rw [hclk k t (by push_cast; linarith) (by push_cast; linarith)]
      push_cast
      exact hfhigh _ (by linarith) (by linarith)

end AsmPhys.Witness
