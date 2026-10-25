# Status

Snapshot 2026-10-25. Lean v4.35.0, Mathlib tag v4.35.0. `lake build` is clean, the library
contains no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`, and every theorem below
depends only on `propext`, `Classical.choice` and `Quot.sound` (`scratch/AxiomsAll.lean`, not
committed, reproduces the audit).

`ClockOK` is the owner-adopted fix for FINDINGS F1 and F6 (2026-10-24); the spec's version is
kept as `ClockOKSpec`. Under the spec's version the flip-flop contract forces empty hold sets.
Under the fixed version the flip-flop spike ([SPIKE-FLIPFLOP.md](SPIKE-FLIPFLOP.md)) succeeded:
the transistor-level flip-flop TGMS26 meets the flip-flop contract for every device family meeting
the per-polarity contracts and every capacitance law in range, on every sheet without leakage that
satisfies its timing conditions (`tgff_contract`), and a toy instance makes H_cells' flip-flop
clause and THM L3.3 non-vacuous. THM L4.1 still has no non-vacuity witness (FINDINGS F13).

## Milestones

| Milestone | State |
| --- | --- |
| M1 L2 core | Done |
| M2 Contracts and inverter | Done, with K13–K14 added (F3, F7) |
| M3 Buridan | Done; non-vacuous (`Witness.toy_buridan_hyps`, `toy_buridan`) |
| M4 Synchronous refinement | Done, with the F5 changes; no L4 witness yet (F13: needs a toy timing with a fast clock slew) |
| M5 ISA and core | Not started |
| M6 Shell | `end_to_end` done; THM Core not started (needs M5) |
| M7 L0 bridge | Not started |

## Spec theorem → Lean

| Spec | Lean | File |
| --- | --- | --- |
| C1–C6, NodeCap | `Passive`, `Regular`, `BoundedOnRail`, `FETContract`, `NodeCap` | `Device/Contract.lean` |
| Derived `I(v_g, v, v) = 0` | `Passive.apply_self` | `Circuit/Rails.lean` |
| Netlist, `F`, trajectories | `Node`, `FET`, `Netlist`, `pot`, `Netlist.F`, `Netlist.vf`, `Netlist.IsTrajOn` | `Circuit/Netlist.lean` |
| THM L2.1 | `tellegen`, `tellegen_matrix` | `Circuit/Tellegen.lean` |
| THM L2.2 | `Netlist.exists_isTrajOn`, `Netlist.isTrajOn_unique` | `Circuit/WellPosed.lean` |
| THM L2.3 | `Netlist.rail_invariance` (also `rail_invariance_set`, `rail_invariance_node`) | `Circuit/Rails.lean` |
| THM L2.4 | `Netlist.exists_dist_le_gronwallBound`, `Netlist.exists_lipschitz_dependence` | `Circuit/WellPosed.lean` |
| THM L2.5 | `Netlist.slew_bound`, `Netlist.slew_lipschitz`, pointwise `Netlist.abs_vf_le` | `Circuit/Rails.lean` |
| Parameter sheet, K0–K14 | `Params`, `Params.Consistent` | `Params.lean` |
| Logic levels | `Params.validIn`, `Params.validOut` | `Cells/Levels.lean` |
| THM L3.1 (INV) | `Netlist.IsInverter.propagation` | `Cells/Inverter.lean` |
| THM L3.2 (INV) | `Netlist.IsInverter.contamination` | `Cells/Inverter.lean` |
| INV as a composable cell | `Netlist.IsInverter.behaves` | `Cells/InverterCell.lean` |
| Clock pins, flip-flop contract | `EdgesOK`, `ClockOK` (fixed), `ClockOKSpec` (spec), `FFRun`, `FFContract` | `Cells/FlipFlop.lean` |
| THM L3.3 | `buridan` | `Cells/Buridan.lean` |
| THM L3.4 | `CombDAG.timing` | `Cells/Compose.lean` |
| U_ENV, Inv_L4, setup/hold | `SyncNet.UEnv`, `SyncNet.InvL4`, `SyncNet.SetupOK`, `SyncNet.HoldOK` | `Sync/Refinement.lean` |
| THM L4.1 | `SyncNet.refinement`, `SyncNet.refinement_out` | `Sync/Refinement.lean` |
| THM End-to-end | `end_to_end` | `Shell/EndToEnd.lean` |

## Non-vacuity witnesses

| Bundle | Witness | File |
| --- | --- | --- |
| FET contracts for every sheet satisfying K0–K14 | `Params.Consistent.exists_fetContract` (clamp devices) | `Witness/Devices.lean` |
| The handoff's toy sheet | `Witness.sheet_consistent`, `Witness.toy_contract` | `Witness/Toy.lean` |
| Every hypothesis of THM L3.1 (INV) | `Witness.inv_propagation_hypotheses`, `inv_rises`, `inv_falls` | `Witness/ToyInverter.lean` |
| The adopted ClockOK | `Witness.exists_clockOK` (continuous periodic clock, every consistent sheet) | `Witness/Clock.lean` |
| A static storage loop holds its bit | `keeper_hold` (cross-coupled inverters, all contract devices) | `Cells/Keeper.lean` |
| A transistor-level flip-flop meets FF1–FF2 | `tgff_contract`: TGMS26, every contract device family and capacitance law in range, every sheet with `I_off = 0` and N1–N7 | `Cells/TGFFCapture.lean` |
| H_cells' flip-flop clause, with reachable hold tubes | `Witness.toy_tgff_contract`, `toy_tgffHold_nonempty`, `toy_tgff_reachable` | `Witness/ToyFlipFlop.lean` |
| Every hypothesis of THM L3.3 | `Witness.toy_buridan_hyps` (and its conclusion, `toy_buridan`) | `Witness/ToyFlipFlop.lean` |
| U_ENV, Inv_L4 for a synchronous netlist (THM L4.1) | none yet (F13) | — |

## Next steps

1. Owner decisions: K13–K14, the F5 timing conditions, and the open decisions of the handoff
   (library name, `bv_decide`, Sail pin, licensing for L0). The ClockOK fix is adopted.
2. Flip-flop follow-ups ([SPIKE-FLIPFLOP.md](SPIKE-FLIPFLOP.md) §12): an `IsTGFF` predicate so
   the contract applies to instances embedded in larger netlists (stage 2), a toy instance with
   non-constant capacitance ranges, leakage via charge-sum tubes and K15 (F14), and an L4 witness
   once the owner picks the toy timing (F13).
3. M5: the RV32I-subset step, a verified compilation from bit-vector datapath descriptions to
   NAND2/NOR2/INV DAGs (so THM L5.1 reduces to bit-level lemmas), and the Sail agreement.
4. THM Core on top of `SyncNet.refinement`, with MF_k choosing edges only up to k + 1 (F9).
5. M7: THM L0.1–L0.4 on Mathlib.
