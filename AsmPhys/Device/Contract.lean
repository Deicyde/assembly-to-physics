import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Basic.Real.Basic

/-!
# L1 — Device contracts and node capacitance

Devices and node capacitances enter the development only through contracts: inequalities whose
clauses are tagged by what justifies them (spec, "L1"). Every theorem above L1 holds for every
device function and capacitance law that satisfies them.

A device function `I g d s` is the quasi-static channel current from drain to source at gate,
drain and source potentials `g`, `d`, `s`.

C1, C2 and C6 are separate predicates (`Passive`, `Regular`, `BoundedOnRail`) because the L2
theorems assume them alone; `FETContract` bundles all six clauses. Tags sit in field docstrings, and
in `--` comments on theorem hypotheses; a bundle's hypothesis is tagged by its fields.

Tags (spec, "Assumption tags"): LAW, MODEL, MEAS, ENV, THM, TCB. The spec tags C1 as
"LAW (second law), applied to a quasi-static channel model (MODEL)"; under the one-tag rule this
is MODEL, which the tag table defines as "a LAW plus a physical condition" (docs/CHANGELOG.md).
-/

namespace AsmPhys

open Set

/-- Transistor polarity. -/
inductive Polarity
  | n
  | p
  deriving DecidableEq, Repr

/-- Per-polarity device parameters, valid over the stated supply and temperature range. -/
structure FETParams where
  /-- On threshold of the gate drive (MEAS). -/
  Von : ℝ
  /-- Off threshold of the gate drive (MEAS). -/
  Voff : ℝ
  /-- Off-state leakage bound (MEAS). -/
  Ioff : ℝ
  /-- On-conductance lower bound (MEAS). -/
  Gon : ℝ
  /-- Saturation floor of the on-drive bound (MEAS). -/
  Isat : ℝ
  /-- Current bound with all terminals on the rails (MEAS). -/
  Imax : ℝ

/-- Gate drive: `v_g − min(v_d, v_s)` for an n-FET and `max(v_d, v_s) − v_g` for a p-FET. -/
def gateDrive : Polarity → ℝ → ℝ → ℝ → ℝ
  | .n, g, d, s => g - min d s
  | .p, g, d, s => max d s - g

/-- The device is on: gate drive at least `V_on`. -/
def onCond (pol : Polarity) (P : FETParams) (g d s : ℝ) : Prop :=
  P.Von ≤ gateDrive pol g d s

/-- The device is off: gate drive at most `V_off`. -/
def offCond (pol : Polarity) (P : FETParams) (g d s : ℝ) : Prop :=
  gateDrive pol g d s ≤ P.Voff

/-- **C1 Passivity** (MODEL: the second law, LAW-3, applied to a quasi-static channel model).
The channel never delivers power: `v_ds · I ≥ 0`. -/
def Passive (I : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ g d s, 0 ≤ (d - s) * I g d s

/-- **C2 Regularity** (MODEL): the device function is globally Lipschitz (sup metric on
`ℝ × ℝ × ℝ`) and globally bounded. No theorem depends on the value of the Lipschitz constant, so
the sheet does not fix one (docs/CHANGELOG.md). -/
structure Regular (I : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- Global Lipschitz bound (MODEL). -/
  lipschitz : ∃ L, LipschitzWith L (fun x : ℝ × ℝ × ℝ => I x.1 x.2.1 x.2.2)
  /-- Global bound (MODEL). -/
  bdd : ∃ B, ∀ g d s, |I g d s| ≤ B

/-- **C6 Bound** (MEAS): `|I| ≤ Imax` whenever all three terminals lie in `Rail = [0, Vmax]`. -/
def BoundedOnRail (Imax Vmax : ℝ) (I : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ g d s, g ∈ Icc 0 Vmax → d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax → |I g d s| ≤ Imax

/-- The FET contract C1–C6 for a device of polarity `pol` with parameters `P`, on the rail
`[0, Vmax]` where `Vmax = V_DD^max`. -/
structure FETContract (pol : Polarity) (P : FETParams) (Vmax : ℝ)
    (I : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- C1 Passivity (MODEL: LAW-3 on a quasi-static channel). -/
  passive : Passive I
  /-- C2 Regularity (MODEL). -/
  regular : Regular I
  /-- C3 Off leakage (MEAS). -/
  off_leak : ∀ g d s, d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax →
    offCond pol P g d s → |I g d s| ≤ P.Ioff
  /-- C4 On drive (MEAS). -/
  on_drive : ∀ g d s, d ∈ Icc 0 Vmax → s ∈ Icc 0 Vmax →
    onCond pol P g d s → min (P.Gon * |d - s|) P.Isat ≤ |I g d s|
  /-- C5 Output monotonicity in the drain (MEAS; device-specific, not physics). -/
  mono_d : ∀ g s, Monotone fun d => I g d s
  /-- C5 Output monotonicity in the source (MEAS; device-specific, not physics). -/
  anti_s : ∀ g d, Antitone fun s => I g d s
  /-- C6 Bound (MEAS). -/
  bounded : BoundedOnRail P.Imax Vmax I

/-- Node capacitance contract for a capacitance law `C = q′` (per-field tags). Gate, junction, wire
and device-internal charge storage are lumped here, with coupling capacitance counted at Miller
factor 0 for `Cmin` and 2 for `Cmax`. The range is claimed for every voltage, as in the spec; only
on-rail values are reached, by THM L2.3. -/
structure NodeCap (Cmin Cmax : ℝ) (C : ℝ → ℝ) : Prop where
  /-- The lower capacitance bound is positive (MEAS). -/
  pos : 0 < Cmin
  /-- The capacitance lies in `[Cmin, Cmax]`, coupling counted at Miller factors 0 and 2 (MEAS). -/
  range : ∀ v, C v ∈ Icc Cmin Cmax
  /-- The capacitance law is Lipschitz (MODEL). -/
  lipschitz : ∃ K, LipschitzWith K C

end AsmPhys
