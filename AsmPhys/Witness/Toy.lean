import AsmPhys.Witness.Devices
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Toy parameter sheet (M2)

The handoff's toy witness (section 5): `V_DD^min = V_DD^max = 1`;
`V_OL, V_IL, V_IH, V_OH = 0.1, 0.3, 0.7, 0.9`; `V_off = 0.3` and `V_on = 0.55` for both
polarities; `η = 0.05`; `G_on = I_sat = I_max = 1` and `I_off = 0`. With these numbers the clamp
devices of `AsmPhys.Witness.Devices` are `r(x) = clamp((x − 0.3)/0.25, 0, 1)` times
`c(x) = clamp(x, −1, 1)`. The clock numbers are the handoff's. The flip-flop timing (`t_su = 550`,
`t_h = 11`, `t_cq ∈ [0, 421]`) is that of the transmission-gate flip-flop TGMS26
(docs/SPIKE-FLIPFLOP.md §7); it meets K8 with `421 + 550 < 1000`.
-/

namespace AsmPhys.Witness

/-- Toy device parameters, shared by both polarities. -/
noncomputable def fetParams : FETParams where
  Von := 0.55
  Voff := 0.3
  Ioff := 0
  Gon := 1
  Isat := 1
  Imax := 1

/-- Toy parameter sheet. -/
noncomputable def sheet : Params where
  VDDmin := 1
  VDDmax := 1
  VOL := 0.1
  VIL := 0.3
  VIH := 0.7
  VOH := 0.9
  pn := fetParams
  pp := fetParams
  Tclk := 1000
  smax := 0
  tlow := 400
  thigh := 400
  tslew := 10
  tsu := 550
  th := 11
  tcqmin := 0
  tcqmax := 421
  tin := 0
  η := 0.05

/-- The toy sheet satisfies K0–K13. -/
theorem sheet_consistent : sheet.Consistent := by
  constructor <;> norm_num [sheet, fetParams, Params.NML, Params.NMH]

/-- The toy devices meet their contracts on the rail `[0, 1]`. -/
theorem toy_contract (pol : Polarity) : FETContract pol fetParams 1 (dev pol fetParams) :=
  dev_contract (by norm_num [fetParams]) (by norm_num [fetParams]) (by norm_num [fetParams])
    (by norm_num [fetParams]) (by norm_num [fetParams])

end AsmPhys.Witness
