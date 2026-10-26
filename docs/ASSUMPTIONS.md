# Assumptions

Everything the claims in [`AsmPhys/Claims.lean`](../AsmPhys/Claims.lean) rest on that Lean does
not prove. Three kinds: the foundations, the modelling choices built into the Spec definitions,
and the tagged hypotheses of each claim. The layering is described in [README.md](../README.md).

## 1. Foundations

- The Lean 4 kernel, v4.35.0, and Mathlib, tag v4.35.0.
- The axioms `propext`, `Classical.choice` and `Quot.sound`, and no others
  ([`scripts/Audit.lean`](../scripts/Audit.lean) checks every claim and every Spec and Design
  declaration).
- `native_decide` and `bv_decide` are not used ([`scripts/check_layers.py`](../scripts/check_layers.py)).

## 2. Modelling choices

These are definitions, not hypotheses: no theorem can discharge them, and every claim is about the
model they define. They follow the specification (doc rev 46) except where
[CHANGELOG.md](CHANGELOG.md) records a change.

| Choice | Tag | Definition |
| --- | --- | --- |
| A transistor has gate, drain and source terminals and no body terminal; its channel current is a function of the three terminal potentials (quasi-static) | MODEL | `FET` (`Spec/Circuit.lean`) |
| Gates draw no current; gate leakage is charged to the fidelity hypothesis MF_k | MODEL | `FET`, `Netlist.F` |
| A node is either a state node, whose potential evolves, or a boundary node, whose potential is prescribed (ground, supply, clocks, primary inputs) | MODEL | `Node`, `pot` |
| Kirchhoff's current law at each state node: the net channel current into node `k` is `C_k(e_k) · ė_k` | LAW | `Netlist.F`, `Netlist.vf` |
| All capacitance is grounded and lumped per node; coupling capacitance is folded in with Miller factors 0 (for `C^min`) and 2 (for `C^max`), the residual crosstalk is charged to MF_k | MODEL | `Netlist.vf`, `NodeCap` |
| A trajectory on `[a, b]` is continuous on `[a, b]` and satisfies the nodal ODE as a right derivative on `[a, b)` | MODEL | `Netlist.IsTrajOn` |
| Logic values are read through thresholds: an input reads `0` at most `V_IL` and `1` at least `V_IH`; a valid output is at most `V_OL` or at least `V_OH` | MODEL | `Params.validIn`, `Params.validOut` (`Spec/Levels.lean`) |
| An inverter is an n-FET to ground and a p-FET to the supply sharing a gate, and no other channel at the output; its delays are `t_pd = C^max · max(V_OH / I_rise, (V_DD^max − V_OL) / I_fall)` and `t_cd = min(NM_L, NM_H) · C^min / (2 · I_max)` | MODEL | `Netlist.IsInverter`, `Params.tpdINV`, `Params.tcdINV` (`Spec/Cells.lean`) |
| A cell *behaves* on `[A, B]` when it meets THM L3.1(a) and THM L3.2 with its delays; a combinational DAG propagates values by its cells' Boolean functions and times by `max + t_pd`, `min + t_cd` | MODEL | `Cell`, `Cell.Behaves`, `CombDAG` (`Spec/Cells.lean`) |
| A flip-flop is specified by FF1–FF2 with hold tubes, under edge spacing and skew (`EdgesOK`) and the adopted clock waveform condition (`ClockOK`) | MODEL | `Spec/FlipFlop.lean` |
| A synchronous netlist means the Mealy machine `(δ, λ)` of its DAG; setup and hold are per-node recursions relative to the clock edges; one cycle runs from `s_k = t_k + s_max + t_cq^max` to `s_{k+1}` | MODEL | `Spec/Sync.lean` |
| The probabilistic shell applies the measure as an outer measure, so no event needs to be measurable; "succeeds with probability at least `1 − ε`" is the inner-measure reading | — | `end_to_end` (`Claims.lean`) |

The design layer adds the objects the claims are about, which are trusted in the same sense (a
claim about `tgff` is a claim about the netlist `tgff` defines):

| Object | Definition |
| --- | --- |
| TGMS26: 26 transistors, 11 state nodes, pins ground, supply, clock and data | `TGFF.pol`, `TGFF.gate`, `TGFF.drain`, `TGFF.source`, `tgff` (`Design/TGFF.lean`) |
| TGMS26's hold tube: every node on the rail, `CKB` high, the slave latch holding the bit at mid-band levels | `tgffHold` (`Design/TGFF.lean`); `latchHold`, `Params.Lvl`, `Params.θL`, `Params.θH` (`Design/Latch.lean`) |
| TGMS26's timing conditions N1–N7, built from the inverter delays and the latch settling time `PhiTG` | `TGFFTiming`, `Params.σm`, `Params.σs` (`Design/TGFF.lean`); `Params.PhiTG` (`Design/Latch.lean`) |
| The toy clamp device, sheet, inverter and flip-flop of the non-vacuity claims | namespace `AsmPhys.Toy` (`Design/Toy.lean`) |

## 3. Hypotheses of the claims

Each hypothesis of a claim carries a tag in a comment. A bundled hypothesis (`FETContract`,
`NodeCap`, `UEnv`) is tagged by its fields' docstrings, and its comment summarizes them. Premises
that only constrain the claim's own variables (trajectories, initial states, logic values,
observation times, the cell driving an output) carry none. The tables list every tagged assumption
and the claims that use it; "via `FETContract`" means the assumption enters through that bundle.

`FFRun` (supply, ground and supply pins, edges, ClockOK, `D` on the rails) is not a hypothesis of
any claim: it is the premise under which `FFContract` promises FF1–FF2. A claim that assumes
`FFContract` assumes the promise; `tgff_contract` proves it for TGMS26.

### LAW

No claim assumes a physical law directly. C1 is tagged MODEL with the second law (LAW-3) as its
justification, and Kirchhoff's current law is built into the model (section 2).

### MODEL

| Assumption | Definition | Claims |
| --- | --- | --- |
| C1 passivity: `v_ds · I ≥ 0` | `Passive` | `rail_invariance`, `rail_invariance_set`, `rail_invariance_node`, `slew_bound`, `slew_lipschitz`, `refinement`, `refinement_out`; via `FETContract`: the inverter claims, `keeper_hold`, `tgff_contract` |
| C2 regularity: the device function is Lipschitz and bounded | `Regular` | `exists_isTrajOn`, `isTrajOn_unique`, `rail_invariance`, `rail_invariance_set`, `rail_invariance_node`, the L2.4 claims, `slew_bound`, `slew_lipschitz`, `buridan`, `refinement`, `refinement_out`; via `FETContract` as above |
| The capacitance law is Lipschitz | `NodeCap.lipschitz` | `exists_isTrajOn`, `isTrajOn_unique`, the L2.4 claims, `buridan`, `tgff_contract` |
| H_cells, flip-flop clause: each flip-flop meets FF1–FF2 | `FFContract` | `buridan`, `refinement`, `refinement_out`; discharged for TGMS26 by `tgff_contract` |
| H_cells, combinational clause: each cell behaves | `Cell.Behaves` | `combinational_timing`, `refinement`, `refinement_out`; discharged for INV by `inverter_behaves` |
| Flip-flop timing signs: `t_su, t_h, t_cq^min ≥ 0`, `t_cq^min < t_cq^max` (FINDINGS F2) | `FFContract` fields | wherever `FFContract` is assumed; `tgff_contract` proves them from N1–N7 |
| TGMS26 timing conditions N1–N7 | `TGFFTiming` | `tgff_contract` |
| `t_h ≤ t_cq^max` (FINDINGS F5) | — | `refinement` |
| The fidelity bound MF_k fails with probability at most `ε_cycle` per cycle | — | `end_to_end` |

### MEAS

| Assumption | Definition | Claims |
| --- | --- | --- |
| C3 off leakage, C4 on drive, C5 monotonicity in drain and source, with the sheet's per-polarity numbers | `FETContract` | the inverter claims, `keeper_hold`, `tgff_contract` |
| C6 current bound on the rail | `BoundedOnRail` | `slew_bound`, `slew_lipschitz`, `abs_vf_le`; via `FETContract` as above |
| Node capacitance ranges `0 < C^min ≤ C_k(v) ≤ C^max` | `NodeCap.pos`, `NodeCap.range`, or explicit bounds | the L2.2, L2.4 and L2.5 claims, the inverter claims, `buridan`, `tgff_contract` (whose `hC : 0 < C_k(v)` follows from the range) |
| No leakage: `I_off = 0` for both polarities (the scope of the flip-flop result, FINDINGS F14) | — | `tgff_contract` |
| The sheet's thresholds and device parameters | `Params`, `FETParams` field docstrings | every claim with a sheet `S` |
| Load and manufacturing failure probabilities `ε_init`, `ε_mfg` | — | `end_to_end` |

### ENV

| Assumption | Definition | Claims |
| --- | --- | --- |
| Supply in range: `V_DD ∈ [V_DD^min, V_DD^max]` | — | the inverter claims, `keeper_hold`, `buridan`; via `UEnv` |
| Ground pin at `0`, supply pin at `V_DD` | — | the inverter claims, `keeper_hold`, `buridan`; via `UEnv` |
| Boundary waveforms continuous | — | `exists_isTrajOn`, `buridan`; via `UEnv` |
| Boundary potentials on the rail | — | `rail_invariance` (channel-touching pins only), `slew_bound`, `slew_lipschitz`; via `UEnv` |
| The neighbours of a node set or node are in it or on the rail | — | `rail_invariance_set`, `rail_invariance_node` |
| Clock edges at least `T_clk` apart, flip-flop edges in the skew window | `EdgesOK` | `buridan`; via `UEnv` |
| The clock waveform condition (the adopted fix for F1 and F6) | `ClockOK` | `buridan`; via `UEnv` |
| The data input of THM L3.3: a continuous rise `ρ` from `0` to `V_DD` within `t_ρ`, on the rail, fitting before the next setup window | — | `buridan` |
| Primary inputs valid from `t_k + t_in` to `t_{k+1} + s_max + t_h` | `UEnv.pi_valid` | `refinement`, `refinement_out` |

### THM

Discharged by a proof or a finite check once the numbers or the netlist are fixed.

| Assumption | Definition | Discharged by |
| --- | --- | --- |
| The sheet's consistency conditions K0–K14 | `Params.Consistent` | `norm_num` on a filled-in sheet (`sheet_consistent` for the toy) |
| Setup and hold on every path | `SyncNet.SetupOK`, `SyncNet.HoldOK` | a finite check on the netlist |
| The window condition `a(i') ≤ min_{In(i')} b` on a cell's fan-in cone | `hwin` of `combinational_timing`, `refinement_out` | a finite check on the DAG |
| The data pin differs from the clock, ground and supply pins | `hD` of `buridan` | `decide` on the pins |
| THM Core: a run that loads correctly, meets its contracts and tracks the model has no bad cycle | `hcore` of `end_to_end` | not yet proved (M5) |

### TCB

None yet. The instruction-set model and the L0 bridge (M5, M7) will add some.

## 4. Assumptions not yet discharged anywhere

- The flip-flop contract for any flip-flop other than TGMS26, and for TGMS26 with leakage (F14).
- `Cell.Behaves` for NAND2 and NOR2 cells.
- THM Core, the `hcore` hypothesis of `end_to_end`.
- A synchronous netlist meeting every hypothesis of THM L4.1 (F13).
