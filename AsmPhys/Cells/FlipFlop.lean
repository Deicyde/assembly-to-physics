import AsmPhys.Spec.FlipFlop
import AsmPhys.Cells.Levels
import AsmPhys.Circuit.Basic

/-!
# The adopted ClockOK implies the spec's

`ClockOK` (`AsmPhys.Spec.FlipFlop`) strengthens the spec's `ClockOKSpec` with the fixes for
docs/FINDINGS.md F1 and F6; every clock meeting it meets the spec's condition.
-/

namespace AsmPhys

/-- The adopted ClockOK implies the spec's. -/
theorem ClockOK.toSpec {S : Params} {VDD : ℝ} {clk : ℝ → ℝ} {tr : ℕ → ℝ}
    (h : ClockOK S VDD clk tr) : ClockOKSpec S VDD clk tr :=
  ⟨h.low, h.high, h.rail⟩

end AsmPhys
