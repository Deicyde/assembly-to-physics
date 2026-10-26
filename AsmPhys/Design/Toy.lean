import AsmPhys.Design.TGFF
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Toy instances

Part of the design layer: definitions only, importing only Mathlib, `AsmPhys.Spec` and
`AsmPhys.Design`. See README.md for how the layers fit together.

The concrete objects of the non-vacuity claims (handoff, section 5, and docs/SPIKE-FLIPFLOP.md):

- the clamp device `I(g, d, s) = r(gate drive) · c(v_ds)` with
  `r(x) = clamp((x − V_off)/(V_on − V_off), 0, 1)` and `c(x) = clamp(G_on·x, −I_sat, I_sat)`;
- the toy sheet: `V_DD = 1`; `V_OL, V_IL, V_IH, V_OH = 0.1, 0.3, 0.7, 0.9`; `V_off = 0.3`,
  `V_on = 0.55`, `G_on = I_sat = I_max = 1`, `I_off = 0` for both polarities; `η = 0.05`; the
  handoff's clock numbers; TGMS26's flip-flop timing `t_su = 550`, `t_h = 11`, `t_cq ∈ [0, 421]`;
- the toy inverter: one state node (the output), boundary nodes ground `0`, supply `1`, input `2`,
  unit output capacitance;
- the toy flip-flop: TGMS26 with the toy devices and constant capacitances (`CKB` 0.01, the delay
  stages `B1, B2` 52 each, every other node 0.1), a state in each hold tube, and its boundary
  waveform.
-/

namespace AsmPhys.Toy

open Set

/-- Gate-drive ramp `r(x) = clamp((x − V_off)/(V_on − V_off), 0, 1)`. -/
noncomputable def ramp (P : FETParams) (x : ℝ) : ℝ :=
  max 0 (min 1 ((x - P.Voff) / (P.Von - P.Voff)))

/-- Channel characteristic `c(x) = clamp(G_on·x, −I_sat, I_sat)`. -/
noncomputable def chan (P : FETParams) (x : ℝ) : ℝ :=
  max (-P.Isat) (min P.Isat (P.Gon * x))

/-- The clamp device of polarity `pol`: `r(gate drive) · c(v_ds)`. -/
noncomputable def dev (pol : Polarity) (P : FETParams) (g d s : ℝ) : ℝ :=
  ramp P (gateDrive pol g d s) * chan P (d - s)

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

/-- The toy n-FET: gate at the input, drain at the output, source at ground. -/
noncomputable def invN : FET 1 3 where
  pol := .n
  P := fetParams
  I := dev .n fetParams
  g := .bdry 2
  d := .state 0
  s := .bdry 0

/-- The toy p-FET: gate at the input, drain at the output, source at the supply. -/
noncomputable def invP : FET 1 3 where
  pol := .p
  P := fetParams
  I := dev .p fetParams
  g := .bdry 2
  d := .state 0
  s := .bdry 1

/-- The toy inverter netlist. -/
noncomputable def inv : Netlist 1 3 where
  nf := 2
  fet := ![invN, invP]
  C := fun _ _ => 1
  C_pos := fun _ _ => one_pos

/-- Toy node capacitances, indexed as `TGFF`'s state nodes. -/
noncomputable def toyC : Fin 11 → ℝ := ![0.01, 0.1, 0.1, 0.1, 0.1, 52, 52, 0.1, 0.1, 0.1, 0.1]

/-- The toy flip-flop: TGMS26 with the toy clamp devices and the toy capacitances. -/
noncomputable def toyFF : Netlist 11 4 :=
  tgff sheet (fun i => dev (TGFF.pol i) fetParams) (fun k _ => toyC k)
    (fun k _ => by fin_cases k <;> norm_num [toyC])

/-- A state in the hold tube of `b`: `CKB` and `Q` at `V_OH` for `b = 1`; `CKB`, `Z` and `A4` at
`V_OH` for `b = 0`; every other node at `0`. -/
noncomputable def toyHoldState : Bool → Fin 11 → ℝ
  | true => ![0.9, 0, 0, 0, 0, 0, 0, 0, 0, 0.9, 0]
  | false => ![0.9, 0, 0, 0, 0, 0, 0, 0, 0.9, 0, 0.9]

/-- The toy boundary waveform: ground `0`, supply `1`, clock `clk`, data `v`. -/
noncomputable def toyU (clk : ℝ → ℝ) (v : ℝ) (t : ℝ) : Fin 4 → ℝ := ![0, 1, clk t, v]

end AsmPhys.Toy
