import AsmPhys.Device.Contract

/-!
# Parameter sheet and consistency conditions K0–K12

Every number the theorems depend on lives here with its tag (spec, "Parameter sheet and
consistency conditions"). Per-node capacitance ranges live in `NodeCap`, per-cell delays with the
cells, and the failure budgets with the probabilistic shell. The temperature range is not a number
the theorems use: it is the range over which every MEAS bound below is claimed.

Once values are filled in, the consistency conditions are inequalities closed by `norm_num`
(see `AsmPhys.Witness.Toy`).
-/

namespace AsmPhys

/-- The parameter sheet. -/
structure Params where
  /-- Lower end of the supply range (ENV). -/
  VDDmin : ℝ
  /-- Upper end of the supply range; the rail is `[0, VDDmax]` (ENV). -/
  VDDmax : ℝ
  /-- Output-low threshold (MEAS: design value validated by characterization). -/
  VOL : ℝ
  /-- Input-low threshold (MEAS: design value validated by characterization). -/
  VIL : ℝ
  /-- Input-high threshold (MEAS: design value validated by characterization). -/
  VIH : ℝ
  /-- Output-high threshold (MEAS: design value validated by characterization). -/
  VOH : ℝ
  /-- n-FET parameters (MEAS). -/
  pn : FETParams
  /-- p-FET parameters (MEAS). -/
  pp : FETParams
  /-- Minimum spacing of the actual clock edges (ENV). -/
  Tclk : ℝ
  /-- Skew window: flip-flop `r`'s `k`-th edge lies in `[t_k, t_k + smax]` (ENV). -/
  smax : ℝ
  /-- Clock low phase before an edge (ENV). -/
  tlow : ℝ
  /-- Clock high phase after the slew (ENV). -/
  thigh : ℝ
  /-- Clock edge slew (ENV). -/
  tslew : ℝ
  /-- Flip-flop setup time (MODEL in v0, part of H_cells). -/
  tsu : ℝ
  /-- Flip-flop hold time (MODEL in v0, part of H_cells). -/
  th : ℝ
  /-- Minimum clock-to-Q delay (MODEL in v0, part of H_cells). -/
  tcqmin : ℝ
  /-- Maximum clock-to-Q delay (MODEL in v0, part of H_cells). -/
  tcqmax : ℝ
  /-- Primary-input valid time after an edge (ENV). -/
  tin : ℝ
  /-- Per-cycle fidelity bound (MODEL). -/
  η : ℝ

namespace Params

variable (S : Params)

/-- The sheet's device parameters for a polarity. -/
def par : Polarity → FETParams
  | .n => S.pn
  | .p => S.pp

/-- Low noise margin `NM_L = V_IL − V_OL`. -/
def NML : ℝ := S.VIL - S.VOL

/-- High noise margin `NM_H = V_OH − V_IH`. -/
def NMH : ℝ := S.VOH - S.VIH

/-- Guaranteed net pull-up current of an inverter whose output is below `V_OH` (K5). -/
noncomputable def Irise : ℝ := min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat - S.pn.Ioff

/-- Guaranteed net pull-down current of an inverter whose output is above `V_OL` (K6). -/
noncomputable def Ifall : ℝ := min (S.pn.Gon * S.VOL) S.pn.Isat - S.pp.Ioff

/-- The consistency conditions K0–K13 (THM once the values are filled in, by `norm_num`).
K8 here is only its cell-independent part; the per-path setup and hold checks belong to L4.
K13 and K14 are not in the spec. Without K13's first two clauses a sheet can satisfy K0–K12 while
no device meets the FET contract (docs/FINDINGS.md, F3); with them every consistent sheet has
contract-meeting devices (`AsmPhys.Params.Consistent.exists_fetContract`). K13's supply clause and
K14 keep the operating envelope nonempty: without them `V_DD` has no admissible value or no clock
meets ClockOK (F7). -/
structure Consistent : Prop where
  /-- K0: `0 < V_OL < V_IL < V_IH < V_OH < V_DD^min`. -/
  K0 : 0 < S.VOL ∧ S.VOL < S.VIL ∧ S.VIL < S.VIH ∧ S.VIH < S.VOH ∧ S.VOH < S.VDDmin
  /-- K1: a valid-low input turns n-FETs off. -/
  K1 : S.VIL ≤ S.pn.Voff
  /-- K2: a valid-low input turns p-FETs on. -/
  K2 : S.pp.Von ≤ S.VDDmin - S.VIL
  /-- K3: a valid-high input turns n-FETs on. -/
  K3 : S.pn.Von ≤ S.VIH
  /-- K4: a valid-high input turns p-FETs off. -/
  K4 : S.VDDmax - S.VIH ≤ S.pp.Voff
  /-- K5: the inverter's pull-up beats leakage. -/
  K5 : S.pn.Ioff < min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat
  /-- K6: the inverter's pull-down beats leakage. -/
  K6 : S.pp.Ioff < min (S.pn.Gon * S.VOL) S.pn.Isat
  /-- K7: the fidelity bound is below both noise margins. -/
  K7 : S.η < min S.NML S.NMH
  /-- K8 (strict, cell-independent part): `t_cq^max + t_su + s_max < T_clk`. -/
  K8 : S.tcqmax + S.tsu + S.smax < S.Tclk
  /-- K9: no gate drive makes an n-FET both on and off. -/
  K9n : S.pn.Voff < S.pn.Von
  /-- K9: no gate drive makes a p-FET both on and off. -/
  K9p : S.pp.Voff < S.pp.Von
  /-- K10 (stacks): the upper device of a stack stays on. -/
  K10 : S.pn.Von ≤ S.VIH - S.VOL ∧ S.pp.Von ≤ S.VOH - S.VIL
  /-- K11 (stacks, candidate): stack drive beats two leakers, for NAND2 low and NOR2 high. -/
  K11 : 2 * S.pp.Ioff < min (S.pn.Gon * S.VOL / 2) S.pn.Isat ∧
    2 * S.pn.Ioff < min (S.pp.Gon * (S.VDDmin - S.VOH) / 2) S.pp.Isat
  /-- K12: the clock phases fit in one period (with K14, ClockOK waveforms exist). -/
  K12 : S.tlow + S.thigh + 2 * S.tslew + S.smax ≤ S.Tclk
  /-- K13 (added, docs/FINDINGS.md F3): leakage bounds are nonnegative, as C3 forces. -/
  K13_leak : 0 ≤ S.pn.Ioff ∧ 0 ≤ S.pp.Ioff
  /-- K13 (added, F3): the on-drive floor at full swing fits under the rail bound, as C4 and C6
  together force. -/
  K13_drive : min (S.pn.Gon * S.VDDmax) S.pn.Isat ≤ S.pn.Imax ∧
    min (S.pp.Gon * S.VDDmax) S.pp.Isat ≤ S.pp.Imax
  /-- K13 (added, F3): the supply range is nonempty. -/
  K13_supply : S.VDDmin ≤ S.VDDmax
  /-- K14 (added, F7): the clock slew is positive and the low phase, high phase, skew window and
  fidelity bound are nonnegative, so continuous ClockOK clocks and EdgesOK edges exist. -/
  K14 : 0 < S.tslew ∧ 0 ≤ S.tlow ∧ 0 ≤ S.thigh ∧ 0 ≤ S.smax ∧ 0 ≤ S.η

end Params

end AsmPhys
