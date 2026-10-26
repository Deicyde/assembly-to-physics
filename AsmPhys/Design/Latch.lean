import AsmPhys.Spec.Levels

/-!
# Latch levels

Part of the design layer: definitions only, importing only Mathlib, `AsmPhys.Spec` and
`AsmPhys.Design`. See README.md for how the layers fit together.

The hold tube of the flip-flop TGMS26 (`AsmPhys.Design.TGFF`) holds its storage nodes at mid-band
latch levels, between the output and input levels of the sheet, and its timing conditions bound
the settling of a transmission-gate latch by `PhiTG`.
-/

namespace AsmPhys

namespace Params

variable (S : Params)

/-- Mid-band low level `θ_L = (V_OL + V_IL)/2`, the bound of a node holding `0` in a latch tube. -/
noncomputable def θL : ℝ := (S.VOL + S.VIL) / 2

/-- Mid-band high level `θ_H = (V_IH + V_OH)/2`, the bound of a node holding `1` in a latch tube. -/
noncomputable def θH : ℝ := (S.VIH + S.VOH) / 2

/-- Latch level: `v ≤ θ_L` for `0`, `v ≥ θ_H` for `1`. -/
def Lvl : Bool → ℝ → Prop
  | false, v => v ≤ S.θL
  | true, v => S.θH ≤ v

end Params

/-- The latch holds `b` at `y`: `x` and `a₂` at the latch level of `¬b`, and `y` a valid output
`b`. -/
def latchHold (S : Params) (b : Bool) {n : ℕ} (x y a₂ : Fin n) (e : Fin n → ℝ) : Prop :=
  S.Lvl (!b) (e x) ∧ S.Lvl (!b) (e a₂) ∧ S.validOut b (e y)

namespace Params

/-- Settling time of a latch's (input core, storage node) pair with capacitances at most `CA` and
`CX`, without leakage: the larger of the pull-down and pull-up bounds. -/
noncomputable def PhiTG (S : Params) (CA CX : ℝ) : ℝ :=
  max ((CA + CX) * S.VDDmax / min (S.pn.Gon * S.VOL) S.pn.Isat
        + CX * S.VDDmax / min (S.pn.Gon * (S.NML / 2)) S.pn.Isat)
      ((CA + CX) * S.VDDmax / min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat
        + CX * S.VDDmax / min (S.pp.Gon * (S.NMH / 2)) S.pp.Isat)

end Params

end AsmPhys
