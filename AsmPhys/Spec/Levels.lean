import AsmPhys.Spec.Params

/-!
# L3 — Logic levels

Part of the trusted specification: definitions only, importing only Mathlib and
`AsmPhys.Spec`. See README.md for how the layers fit together.

Logic levels are voltage intervals: `validIn b v` is the input reading of `v` as `b`, and
`validOut b v` the stronger output level (spec, "L3").
-/

namespace AsmPhys

namespace Params

variable (S : Params)

/-- `v` reads as the bit `b` at an input: `v ≤ V_IL` for `0`, `v ≥ V_IH` for `1`. -/
def validIn : Bool → ℝ → Prop
  | false, v => v ≤ S.VIL
  | true, v => S.VIH ≤ v

/-- `v` is a valid output level for the bit `b`: `v ≤ V_OL` for `0`, `v ≥ V_OH` for `1`. -/
def validOut : Bool → ℝ → Prop
  | false, v => v ≤ S.VOL
  | true, v => S.VOH ≤ v

end Params

end AsmPhys
