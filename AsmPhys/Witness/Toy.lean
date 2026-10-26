import AsmPhys.Witness.Devices
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Toy parameter sheet (M2)

The handoff's toy sheet and devices (section 5), defined in `AsmPhys.Design.Toy`, satisfy the
consistency conditions and the FET contracts on the rail `[0, 1]`.
-/

namespace AsmPhys.Witness

open AsmPhys.Toy

/-- The toy sheet satisfies K0–K14. -/
theorem sheet_consistent : sheet.Consistent := by
  constructor <;> norm_num [sheet, fetParams, Params.NML, Params.NMH]

/-- The toy devices meet their contracts on the rail `[0, 1]`. -/
theorem toy_contract (pol : Polarity) : FETContract pol fetParams 1 (dev pol fetParams) :=
  dev_contract (by norm_num [fetParams]) (by norm_num [fetParams]) (by norm_num [fetParams])
    (by norm_num [fetParams]) (by norm_num [fetParams])

end AsmPhys.Witness
