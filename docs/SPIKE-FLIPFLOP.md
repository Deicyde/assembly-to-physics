# Flip-flop spike: TGMS26

2026-10-25. **Outcome: positive.** Stage 1 is accepted: milestones A, B and C (§12) are proved
with no `sorry` and only the standard axioms. `tgff_contract` already meets stage 2's first
acceptance item (every sheet with `I_off = 0` satisfying N1–N7, every contract device family, every
capacitance law in range); the embedded-instance predicate `IsTGFF` and a toy with non-constant
ranges remain. The high case of `pair_settle` is proved with deficits clipped at `V_OH` for every
`V_DD` in range, so the `V_DD^min = V_DD^max` shortcut below was not needed. `toy_buridan` states
L3.3's conclusion; `toy_buridan_hyps` states its hypotheses.

**Goal** (handoff §5): build a transistor-level master–slave positive-edge flip-flop with reachable hold tubes, and prove it meets `FFContract` under the adopted `ClockOK`. The proof must hold for every device family that meets the per-polarity contracts and every capacitance law in range.

**Repo state:** `lake build` is clean and there is no `sorry`. `Circuit/Tube.lean`, `Cells/Keeper.lean`, `Circuit/Charge.lean` and `Witness.exists_clockOK` are proved. The task brief's notes that these are "being proved" or "sorry'd" are out of date.

## 1. Decision

| Design | FETs / state nodes | Judge 1 | Judge 2 | Outcome |
|---|---|---|---|---|
| TGMS26: transmission-gate master–slave, internal clock inverter, delayed slave feed | 26 / 11 | 7.5 | 8 | **chosen** |
| MS-NAND/NOR: static-CMOS SR latches with a NOR non-overlap enable | 44 / 22 | 6 | 6 | rejected; v1 parts kept |
| C2MOS-SK: clocked inverters with clocked keepers | 26 / 15 | 5.5 | 5 | rejected; stack tube kept |

What the judges said about TGMS26:

- **No counterexample in scope.** Neither judge broke it. They tried a dithering rise, full-swing glitches in the fall slot, V_DD < V_DD^max, and stale chain values at the rise. The scope is:
  - every sheet with I_off^n = I_off^p = 0, the toy sheet included;
  - every contract-meeting device family (devices of one polarity may differ);
  - every capacitance law in its `NodeCap` range.
- **Toy fit.** On the toy sheet only the placeholders t_su, t_h and t_cq change. The ENV numbers stay as they are.
- **Cheapest of the three.** It has no series stacks, no phase detector, and no charge functions at I_off = 0. Estimate: 3–4.5k lines, 1.5–3 agent-weeks. FF1 lands first.
- **Simple Hold.** Hold does not depend on time. At I_off = 0 it also does not depend on the devices or the capacitance laws, so `SyncNet.Hold` and Inv_L4 need no hold sets that depend on the chip.
- **Weak points:**
  - The toy margins are thin. §7 widens them with C_B1 = C_B2 = 52 and t_su = 550.
  - I_off > 0 needs charge-sum tubes and a new condition K15 (stage 3).
  - It gives no stack lemma for v1 NAND2/NOR2.
  - The L4 setup budget is only 29.

Why the other two were rejected:

- **MS-NAND/NOR.** With the existing delay lemmas, its clock chain cannot both last long enough and settle in time at t_slew = 10. Contamination ≥ t_slew needs C_k1 + C_clkd ≥ 100; settling within t_high needs C_k1 + C_clkd ≤ 44.4. Its toy witness got around this by changing the ENV number t_slew to 4.
- **C2MOS-SK.** With V_DD^min < V_DD^max, its fall-phase budget ΣY breaks FF1 while Y is still valid. Judge 1's example: V_DD = 0.95, with a_K2 > V_DD draining through K2.Pd. Its sSup phase detector, four time-dependent tubes and piecewise-linear moving tubes also make it the costliest to formalize.

Kept for the v1 NAND2/NOR2 work. This runs in parallel and is not part of the spike.

- **C2MOS-SK's cut-corner tube**, for a NAND2 with output o and stack node x held low: {q_o(o) ≤ q_o(V_OL), q_o(o) + q_x(x) ≤ q_o(V_OL) + q_x(V_OL/2)}.
  - On the first face x ≤ V_OL/2, so the top n-FET is on (K10).
  - On the second face x ≥ V_OL/2, so the bottom n-FET is on.
  - Each face drains at least min(G_on^n·V_OL/2, I_sat^n) against at most 2·I_off^p of p-leakage.
  - So K11 as stated is enough for NAND2 output-low hold, and MS-NAND/NOR's K11★ is not a finding.
- **MS-NAND/NOR's top-off faces and bottom-off charge-sharing lemma**, for NAND2 output high.

## 2. Netlist

Boundary nodes (Fin 4): 0 GND, 1 VDD, 2 CLK (this flip-flop's clock pin), 3 D. CLK and D drive gates only (F8).

| # | State node | Driven by | Channel terminals | Gate of | Value storing b | Toy C |
|---|---|---|---|---|---|---|
| 0 | CKB | INV(CLK) | f0, f1 | f4, f11, f19, f24 | — | 0.01 |
| 1 | A1 | INV(D); side TG1 | f2–f5 | — | ¬b | 0.1 |
| 2 | X | TG1, TG2 (master storage) | f4, f5, f10, f11 | f6, f7 | ¬b | 0.1 |
| 3 | Y | INV(X) | f6, f7 | f8, f9, f12, f13 | b | 0.1 |
| 4 | A2 | INV(Y); side TG2 | f8–f11 | — | ¬b | 0.1 |
| 5 | B1 | INV(Y) | f12, f13 | f14, f15 | ¬b | 52 |
| 6 | B2 | INV(B1) | f14, f15 | f16, f17 | b | 52 |
| 7 | B | INV(B2); side TG3 | f16–f19 | — | ¬b | 0.1 |
| 8 | Z | TG3, TG4 (slave storage) | f18, f19, f24, f25 | f20, f21 | ¬b | 0.1 |
| 9 | Q | INV(Z), the output | f20, f21 | f22, f23, fanout | b | 0.1 |
| 10 | A4 | INV(Q); side TG4 | f22–f25 | — | ¬b | 0.1 |

| f | pol | gate | drain | source | role |
|---|---|---|---|---|---|
| 0 / 1 | n / p | CLK | CKB | GND / VDD | clock inverter |
| 2 / 3 | n / p | D | A1 | GND / VDD | input inverter |
| 4 / 5 | n / p | CKB / CLK | A1 | X | TG1, master input, on while CLK is low |
| 6 / 7 | n / p | X | Y | GND / VDD | master forward inverter |
| 8 / 9 | n / p | Y | A2 | GND / VDD | master feedback inverter |
| 10 / 11 | n / p | CLK / CKB | A2 | X | TG2, master feedback, on while CLK is high |
| 12 / 13 | n / p | Y | B1 | GND / VDD | delay stage 1 |
| 14 / 15 | n / p | B1 | B2 | GND / VDD | delay stage 2 |
| 16 / 17 | n / p | B2 | B | GND / VDD | slave input driver |
| 18 / 19 | n / p | CLK / CKB | B | Z | TG3, slave input, on while CLK is high |
| 20 / 21 | n / p | Z | Q | GND / VDD | output inverter |
| 22 / 23 | n / p | Q | A4 | GND / VDD | slave feedback inverter |
| 24 / 25 | n / p | CKB / CLK | A4 | Z | TG4, slave feedback, on while CLK is low |

Structure. Each fact is checked by `fin_cases` or `decide` on the table.

- **Pure inverters** (`IsInverter`, gate-only loads): CKB, Y, B1, B2, Q.
- **Inverter cores** whose only extra channel is one transmission gate (TG): A1 (TG1), A2 (TG2), B (TG3), A4 (TG4).
- **Storage nodes:** X has channels to TG1 and TG2 only; Z to TG3 and TG4 only.
- **The same latch appears twice:**
  - Master: storage X, forward inverter Y, input core A1 fed from D through TG1, feedback core A2 fed from Y through TG2.
  - Slave: storage Z, forward inverter Q, input core B fed from B2 through TG3, feedback core A4 fed from Q through TG4.
- **No series stacks**, so K11 is not used.
- **Storage is static.** In every hold phase the storage node is driven by an inverter core through a TG that is on. The restriction I_off = 0 only affects the shape of the tube (§4, stage 3), not the storage.
- **No ratioed logic.** No step compares two devices of the same polarity class.

Capacitance levers:

- C_CKB small: this sets p_c.
- C_B1 and C_B2 large, with tight ranges: they set the race margin (N5) against the chain delay (N3).
- All other nodes small.

Toy: constant laws via `nodeCap_const`, values as in the table, with Q's fanout folded into C_Q.

## 3. Clocking

Notation for one edge: T = t_k^r, R := T + t_slew, F := R + t_high, L := F + t_slew, and T' := t_{k+1}^r. The internal clock delay is p_c := tpdINV(C_CKB^max), which is 0.09 on the toy sheet.

Transmission-gate (TG) facts. They hold for both FETs, in either drain/source orientation, with terminals in [0, V_DD^max]. J is the current through the gate.

- (a) n-gate ≤ V_IL and p-gate ≥ V_IH: K1 and K4 turn both FETs off, and |J| ≤ I_off^n + I_off^p, which is 0 when I_off = 0.
- (b) n-gate ≥ V_IH and lower terminal ≤ V_OL: K10 turns the n-FET on, and |J| ≥ min(G_on^n·|Δv|, I_sat^n).
- (c) p-gate ≤ V_IL and upper terminal ≥ V_OH: K10 turns the p-FET on, and |J| ≥ min(G_on^p·|Δv|, I_sat^p).
- (d) By C1, J flows from the higher terminal to the lower one, through both FETs.

Nothing is guaranteed between two mid-band nodes. That is why each TG sits between a storage node and an inverter core, whose output reaches V_OL or V_OH.

CKB = INV(CLK). THM L3.1 gives CKB ≤ V_OL on [R + p_c, F] and CKB ≥ V_OH on [L + p_c, T'], and it keeps CKB ≥ V_OH for as long as CLK ≤ V_IL.

| Window | ClockOK gives | CKB | TG1, TG4 (n-gate CKB, p-gate CLK) | TG2, TG3 (n-gate CLK, p-gate CKB) |
|---|---|---|---|---|
| (T, R] | CLK > V_IL (`pin`, unused) | free | may conduct | may conduct |
| [R, R + p_c) | CLK ≥ V_IH | settling | may conduct | may conduct |
| [R + p_c, F] | CLK ≥ V_IH | ≤ V_OL | off, by (a) | pass both levels, by (b) and (c) |
| (F, L) | rails only | free | may conduct, any number of times | may conduct, any number of times |
| [L, L + p_c) | CLK ≤ V_IL | settling | may conduct | may conduct |
| [L + p_c, T'] | CLK ≤ V_IL | ≥ V_OH | pass both levels | off |

The two overlap windows are U_r := (T, R + p_c) and U_f := (F, L + p_c). Each is t_slew + p_c long.

- **U_r, master.** N1 keeps D valid until R + p_c. So A1 and A2 drive X the same way, and C1 keeps X on their side whatever TG1 and TG2 do. CLK may sit just above V_IL for the whole rise and keep TG1's p-FET fully on, which is why this design needs t_h ≥ t_slew + p_c.
- **U_r, slave.** B and A4 may fight through TG3 and TG4. Nothing is claimed there: t_cq^min = 0, and the slave restarts from an arbitrary state once TG4 is off.
- **U_f, slave.** N5 keeps B2 validIn by contamination for t_cd(Y) + t_cd(B1) + t_cd(B2) ≥ t_slew + p_c, so B and A4 agree.
- **U_f, master.** TG1 may pass a new D into X. Nothing is claimed about the master.

Each latch settles while its loop is open: the master in the low phase with TG2 off, the slave in the high phase with TG4 off. No bistable decision ever occurs.

`ClockOK` fields used: `low_between`, `high`, `rail`. Fields not used: `low`, `pin`. `EdgesOK` together with K8 gives T' + t_cq^max < t_{k+2}^r.

## 4. Hold tubes

Levels:

- θ_L := (V_OL + V_IL)/2, θ_H := (V_IH + V_OH)/2, δ₀ := min(NM_L, NM_H)/2. Toy: 0.2, 0.8 and 0.1.
- K0 gives V_OL + δ₀ ≤ θ_L, θ_L + δ₀ ≤ V_IL, V_IH + δ₀ ≤ θ_H and θ_H + δ₀ ≤ V_OH.
- Lvl(0, v) :⇔ v ≤ θ_L, and Lvl(1, v) :⇔ v ≥ θ_H.

The contract tube is constant in clk and t, so it is trivially causal:

Hold(clk, b, t) := { e : 0 ≤ e_k ≤ V_DD^max for all 11 nodes k; e_CKB ≥ V_OH; Lvl(¬b, e_Z); Lvl(¬b, e_A4); validOut(b, e_Q) }

- **b = 1:** Z ≤ θ_L, A4 ≤ θ_L, Q ≥ V_OH, CKB ≥ V_OH.
- **b = 0:** Z ≥ θ_H, A4 ≥ θ_H, Q ≤ V_OL, CKB ≥ V_OH.

Why each part is there:

- The rails use V_DD^max because Hold takes no V_DD argument.
- CKB ≥ V_OH is needed for FF1. If a run starts with CKB low, TG3's p-FET is on and the transparent master overwrites the slave.
- A time-independent Hold is legal here. N6 places every instant at which FF1 or FF2 evaluates Hold inside [L + p_c, T'], where the slave is closed.

Tubes used inside the proofs (b is the bit held; the b = 0 case mirrors b = 1):

| Tube | Inequalities for b = 1 | Invariant while |
|---|---|---|
| MAgree(b) | A1, X, A2 ≤ θ_L; Y ≥ V_OH | D validIn(b); clock arbitrary |
| MHold(b) | X, A2 ≤ θ_L; Y ≥ V_OH | TG1 off (a); D arbitrary |
| Chain(b) | B1 ≤ V_OL; B2 ≥ V_OH | Y validIn(b) |
| SAgree(b) | B, Z, A4 ≤ θ_L; Q ≥ V_OH | B2 validIn(b); clock arbitrary |
| SHold(b) | Z, A4 ≤ θ_L; Q ≥ V_OH | TG3 off (a) |

MAgree and SAgree are the same latch lemma (`agree_invariant`); MHold and SHold are another (`hold_invariant`). Hold = rails ∧ CKB ≥ V_OH ∧ SHold.

Phases of FF2 for capture edge T'. The old bit is d and the new bit is b. Define t₁ := T' − t_su + σ_m and s₀ := max(R' + p_c, t₁ + δ_ch). Toy times are relative to T' and use the sizing of §7.

| Interval | Toy | Clock | Master | Chain | Slave |
|---|---|---|---|---|---|
| [s, T' − t_su] | ≤ −550 | low; CKB ≥ V_OH | free | free | SHold(d) |
| [T' − t_su, t₁] | −550 to −545.2 | low | settles: (A1, X), then Y, then A2 | free | SHold(d) |
| [t₁, T'] | −545.2 to 0 | low | MAgree(b) | settling | SHold(d) |
| (T', R' + p_c) | 0 to 10.09 | rise | MAgree(b) | settling | free |
| [R' + p_c, s₀] | 10.09 to 390.8 | high; CKB ≤ V_OL | MHold(b) | Chain(b) from t₁ + δ_ch | follows B (TG3 on, TG4 off) |
| [s₀, s₀ + σ_s] | 390.8 to 395.6 | high | MHold(b) | Chain(b) | settles: (B, Z), then Q, then A4 |
| [s₀ + σ_s, F'] | 395.6 to 410 | high | MHold(b) | Chain(b) | SAgree(b) |
| [F', L' + p_c] | 410 to 420.09 | free | free | B2 validIn(b) | SAgree(b) |
| [L' + p_c, t_{k+2}^r] | 420.09 to ≥ 1000 | low; CKB ≥ V_OH | free | free | SHold(b); τ = T' + 421 lies here |

**Nonempty.** CKB = Q = V_OH with every other node at 0 lies in Hold(·, 1, ·). CKB = Z = A4 = V_OH with every other node at 0 lies in Hold(·, 0, ·). K0 and K13 give V_OH ≤ V_DD^max.

**Reachable.**

- FF2's argument uses the state at T' − t_su only through the rails and CKB ≥ V_OH. CKB ≥ V_OH holds p_c after the start of any low phase.
- So every state on the rails at any s in a low phase with s + p_c ≤ T' − t_su reaches Hold(b) at T' + t_cq^max, provided D is validIn(b) on [T' − t_su, T' + t_h]. This is `tgff_capture`.
- Toy: take the clock from `exists_clockOK` (edges at k·1000) and a constant D. Every rail state at t = 421 gives a trajectory (`exists_isTrajOn`) with e(1421) ∈ Hold(b).

**I_off > 0 (stage 3).** The box above is not invariant. At Z = A4 = θ_L, TG4 carries no current while the off TG3 leaks into Z. Use charge-sum tubes instead, with q_k = `charge (C k)` and ℓ := I_off^n + I_off^p:

- b = 1: Z ≤ θ_L, A4 ≤ θ_L, q_Z(Z) + q_A4(A4) ≤ q_Z(θ_L) + q_A4(V_OL), Q ≥ V_OH.
- b = 0: Z ≥ θ_H, A4 ≥ θ_H, q_Z(Z) + q_A4(A4) ≥ q_Z(θ_H) + q_A4(V_OH), Q ≤ V_OL.

Faces for b = 1:

- On Z = θ_L, the charge constraint forces A4 ≤ V_OL. TG4's n-FET then drains at least min(G_on^n·NM_L/2, I_sat^n), which exceeds ℓ.
- On the charge face, A4 ≥ V_OL and TG4's current cancels. A4's core drains at least min(G_on^n·V_OL, I_sat^n), which exceeds ℓ + I_off^p.
- The A4 and Q faces are as at I_off = 0.

Under K15 every face is strict, so `invariant_of_strict` applies. Hold then depends on the capacitance laws.

## 5. FF1

Premises: a trajectory on [a, b] with FFRun; k, d, and s ∈ [a, b] with t_k^r + t_cq^max ≤ s < T'; e(s) ∈ Hold(d). Write b' := min b T'.

1. **Rails.** Only GND (at 0) and VDD (at most V_DD^max) touch channels, and e(s) lies in [0, V_DD^max]. `Netlist.rail_invariance` with V = V_DD^max keeps all 11 nodes there on [s, b].
2. **Clock low.** N6 gives s ≥ t_k^r + 2t_slew + t_high, so `ClockOK.low_between k` gives CLK ≤ V_IL on [s, T'].
3. **CKB stays high.** CKB ≥ V_OH at s and CLK is validIn 0 on [s, b'], so `IsInverter.propagation_rail` (b) keeps CKB ≥ V_OH on [s, b'].
4. **TG3 is off.** CLK ≤ V_IL, CKB ≥ V_IH and I_off = 0, so `IsTG.abs_J_le_Ioff` gives J(TG3) = 0 on [s, b'].
5. **The slave holds.** `IsTGLatch.hold_invariant` for the slave, with TG3 off, keeps SHold(d) on [s, b']. Its band faces, for d = 1 (d = 0 mirrors), take the face component to be the largest of the family and within δ₀ of its bound:
   - Z: A4 ≤ Z, so by C1 TG4 carries current out of Z or none, and TG3 carries none. Hence F_Z ≤ 0. This face is not strict, which is why the band maximum principle is needed.
   - A4: Q ≥ V_OH − δ₀ ≥ V_IH and A4 ≥ V_OL, so the core gives at most −I_fall (K3, K4, K6). Z ≤ A4, so TG4 only adds current flowing out of A4.
   - Q: Z ≤ θ_L + δ₀ ≤ V_IL and Q ≤ V_OH, so F_Q ≥ I_rise (K1, K2, K5).
6. **Conclusions.** Steps 1, 3 and 5 give e(t) ∈ Hold(d) for t ∈ [s, T') ∩ [a, b]. Step 5 gives validOut(d, Q) on [s, T'] ∩ [a, b]. With t_cq^min = 0 (N7) that interval is [s, T' + t_cq^min] ∩ [a, b].

Used: `low_between`, `rail`, and C1–C4. No D hypothesis, no C5 and no C6 are needed.

Variant with t_cq^min > 0: after T', Z has 4 channels with terminals on the rails, so `abs_vf_le` keeps Z ≤ V_IL until T' + NM·C_Z^min/(8·I_M). THM L3.1(b) then keeps Q.

## 6. FF2

Premises: as for FF1, plus t_k^r + t_cq^max ≤ s ≤ T' − t_su, D validIn(b) on [T' − t_su, T' + t_h], T' + t_h ≤ b, and τ := T' + t_cq^max ∈ [a, b]. R', F' and L' belong to edge T'.

0. **Clock facts.** `EdgesOK` and K8 give τ < t_{k+2}^r, as in `FFContract.validOut_of_capture`. ClockOK gives CLK ≤ V_IL on [s, T'] and on [L', t_{k+2}^r], and CLK ≥ V_IH on [R', F'].
1. **Up to the setup window.** FF1's steps 1–3 give the rails on [s, b] and CKB ≥ V_OH at T' − t_su. From this point on, `tgff_capture` uses nothing else about e(s).
2. **Master settles, [T' − t_su, t₁].** CKB ≥ V_IH and CLK ≤ V_IL make TG1 pass both levels and turn TG2 off with J = 0. `IsTGLatch.settle` for the master, with D validIn(b):
   - `pair_settle` puts A1 and X at Lvl(¬b) after Φ(A1, X);
   - THM L3.1 then gives validOut(b, Y) after t_pd(Y);
   - `propagation_side` with zero side current gives validOut(¬b, A2) after t_pd(A2).
   N2 gives t₁ ≤ T', so MAgree(b) holds at t₁.
3. **Master through the rise, [t₁, R' + p_c].** N1 keeps D validIn(b) until R' + p_c. `agree_invariant` keeps MAgree(b) with no clock hypothesis.
4. **Master holds, [R' + p_c, F'].** THM L3.1(a) from R' gives CKB ≤ V_OL, and CLK ≥ V_IH, so TG1 is off. `hold_invariant` keeps MHold(b) whatever D does. So Y is validOut(b) on all of [t₁, F'].
5. **Chain.** THM L3.1 for B1 and then B2 gives Chain(b) on [t₁ + δ_ch, F'].
6. **Slave settles, [s₀, s₀ + σ_s] ⊆ [R' + p_c, F'].** N3 and N4 give the inclusion. TG3 passes both levels, TG4 is off with J = 0, and B2 is validIn(b). `IsTGLatch.settle` for the slave, starting from an arbitrary state, gives SAgree(b) at s₀ + σ_s, and `agree_invariant` keeps it until F'.
7. **Fall race, [F', L' + p_c].** At F', Y is validOut(b), B1 is validOut(¬b) and B2 is validOut(b). `contamination_chain3` keeps B2 validIn(b) on [F', F' + ρ], which contains [F', L' + p_c] by N5. `agree_invariant` keeps SAgree(b) whatever the master and the clock do.
8. **Slave holds, [L' + p_c, τ].** THM L3.1(a) from L' gives CKB ≥ V_OH from L' + p_c on, and CLK ≤ V_IL, so TG3 is off. SAgree(b) ⊆ SHold(b) (drop the first conjunct), so SHold(b) holds at L' + p_c, and `hold_invariant` keeps it until τ (N6 gives τ ≥ L' + p_c). With the rails and CKB ≥ V_OH, e(τ) ∈ Hold(b).

Phases are glued with `IsTrajOn.mono`. Used: `low_between`, `high`, `rail`; C1–C4, plus C6 in step 7. No clock level inside U_r or U_f is used, and C5 is not used.

## 7. Timing

All formulas are for I_off = 0.

| Quantity | Formula | Toy |
|---|---|---|
| I_rise, I_fall | `Params.Irise`, `Params.Ifall` | 0.1, 0.1 |
| P_inv | max(V_OH/I_rise, (V_DD^max − V_OL)/I_fall) | 9 |
| t_pd(k) | `tpdINV (Cmax k)` = C_k^max·P_inv | 9·C |
| t_cd(k) | `tcdINV (Cmin k)` = NM·C_k^min/(2·I_M) | 0.1·C |
| R | t_pd/t_cd per stage = 2·I_M·P_inv·C^max/(NM·C^min) | 90 |
| p_c | t_pd(CKB) | 0.09 |
| Φ_n(A, X) | (C_A^max + C_X^max)·V_DD^max/min(G_on^n·V_OL, I_sat^n) + C_X^max·V_DD^max/min(G_on^n·NM_L/2, I_sat^n) | 3 |
| Φ_p(A, X) | (C_A^max + C_X^max)·V_DD^max/min(G_on^p·(V_DD^min − V_OH), I_sat^p) + C_X^max·V_DD^max/min(G_on^p·NM_H/2, I_sat^p) | 3 |
| Φ(A, X) | max(Φ_n, Φ_p) (`PhiTG`) | 3 |
| σ_m | Φ(A1, X) + t_pd(Y) + t_pd(A2) | 4.8 |
| σ_s | Φ(B, Z) + t_pd(Q) + t_pd(A4) | 4.8 |
| δ_ch | t_pd(B1) + t_pd(B2) | 936 |
| ρ | t_cd(Y) + t_cd(B1) + t_cd(B2) | 10.41 |
| t_h | ≥ t_slew + p_c | 10.09, so 11 |
| t_su | ≥ max(σ_m, σ_m + δ_ch + σ_s − t_slew − t_high) | 535.6, so 550 |
| t_cq^max | ≥ 2·t_slew + t_high + p_c | 420.09, so 421 |
| t_cq^min | 0 | 0 |

Checks on the toy sheet:

| Check | Value |
|---|---|
| K8 | 421 + 550 + 0 = 971 < 1000 |
| F5 (t_h ≤ t_cq^max) | 11 ≤ 421 |
| N3 | 945.6 ≤ 960 |
| N4 | 4.89 ≤ 400 |
| N5 | 10.41 ≥ 10.09 |
| F11's necessary conditions (§9) | 561 ≥ 10; 421 ≥ 10 |
| K12 | unchanged, 820 ≤ 1000 |

**B1/B2 tolerance at t_su = 550:** C_B1^min + C_B2^min ≥ 100.8 and C_B1^max + C_B2^max ≤ 105.6, a spread of about 4.8%. At the K8 limit (t_su < 579) the spread reaches about 8%.

**Thinner alternative** (judge 2): C_B = 51 and t_su = 520 give ρ = 10.21, N3 927.6 ≤ 930, and K8 941 < 1000.

**Sheet-level feasibility** for this design with the current lemmas: N3, N5, N6 and K8 combine to roughly (R + 1)·(t_slew + p_c) < T_clk − s_max. On the toy sheet that is 918 < 1000.

**Variant for the L4 witness** (t_slew = 1; this needs the owner, see F13):

- Sizing: C_B1 = C_B2 = 6, ρ = 1.21 ≥ 1.09, δ_ch = 108.
- Contract numbers: t_h = 2, t_su = 10, t_cq = [0, 403]. K8: 413 < 1000.
- A Q → INV → INV → D path with C = 10 has Σt_cd = 2 ≥ t_h + s_max and setup 403 + 180 + 10 = 593 ≤ 1000.

**Sanity simulation.** These scripts are evidence only, not proof:

- `/private/tmp/claude-501/-Users-jack-Desktop-LEAN/dbecccda-ee39-4363-b000-34f1db912678/scratchpad/tgff_sim52.py` uses this plan's sizing (52, 550), toy clamp devices, a dithering rise, full-swing glitches in the fall slot, and D opposite outside every window. It gives Q = 1, 0, 1 on [T + 421, T + 1000] in all three cycles.
- `tgff_sim3.py` in the same directory is the negative control. With C_B = 0.1 the bit is lost in every cycle.

## 8. Conditions beyond K0–K14

| ID | Condition | Toy | Tag | Finding |
|---|---|---|---|---|
| N1 | t_h ≥ t_slew + p_c | 11 ≥ 10.09 | MODEL (H_cells timing) | no |
| N2 | t_su ≥ σ_m | 550 ≥ 4.8 | MODEL | no |
| N3 | σ_m + δ_ch + σ_s ≤ t_su + t_slew + t_high | 945.6 ≤ 960 | MODEL | no |
| N4 | p_c + σ_s ≤ t_high | 4.89 ≤ 400 | MODEL | no |
| N5 (race) | t_cd(Y) + t_cd(B1) + t_cd(B2) ≥ t_slew + p_c | 10.41 ≥ 10.09 | MEAS (capacitance design) | F10 |
| N6 | t_cq^max ≥ 2·t_slew + t_high + p_c | 421 ≥ 420.09 | MODEL | F12 |
| N7 | t_cq^min = 0, or 0 ≤ t_cq^min ≤ NM·C_Z^min/(8·I_M) | 0 | MODEL | no |
| hI | I_off^n = I_off^p = 0 | holds | scope of stages 1–2 | removed in stage 3 |
| K15 | with ℓ := I_off^n + I_off^p: ℓ + I_off^p < min(G_on^n·V_OL/2, I_sat^n); ℓ < min(G_on^n·NM_L/2, I_sat^n); ℓ + I_off^n < min(G_on^p·(V_DD^min − V_OH)/2, I_sat^p); ℓ < min(G_on^p·NM_H/2, I_sat^p). Re-derive the exact clauses with the leaky settle lemma. | 0 < 0.05; 0 < 0.1 | MEAS | F14 (stage 3) |
| NodeCap | per-node ranges of §2 | constant laws | MEAS (design) | no |
| existing | K8 with the new numbers; F5 t_h ≤ t_cq^max | 971 < 1000; 11 ≤ 421 | — | — |
| derived | t_su + t_h ≥ t_slew; t_cq^max − t_cq^min ≥ t_slew | 561; 421 | THM (paper) | F11 |

K10 is load-bearing (TG conduction). K1–K6, K13 and K14 are used as they stand. K11 is not used. No new conditions on voltage levels or device parameters are needed at I_off = 0.

## 9. Findings for the owner

These are drafts for docs/FINDINGS.md. None has been applied.

**F10 (major): whether a verifiable flip-flop exists is a sheet condition.**

- **Problem.**
  - ClockOK leaves the fall slot free within the rails, and in the rise slot it only requires CLK > V_IL.
  - Contract devices are unconstrained for gate drives in (V_off, V_on), so in both slots every latch may conduct.
  - The stored bit is then protected only by a contamination delay of at least t_slew + p_c on the master-to-slave path (N5). The other two designs need the same thing, and the negative-control simulation loses the bit in every cycle without it.
  - With C6-based bounds, every unit of contamination costs R units of propagation, R = 2·I_M·P_inv·C^max/(NM·C^min). R is 90 on the toy sheet, and about 17.5 with one-sided contamination and staircase rise bounds.
  - For TGMS26 this works out to roughly (R + 1)(t_slew + p_c) < T_clk − s_max (toy: 918 < 1000). K0–K14 do not imply it.
  - Monotone slews would not remove it, because the partial overlap of t_slew + p_c remains.
- **Proposed fix.** Keep the requirement as part of H_cells' MODEL timing, and record that K0–K14 alone do not guarantee that a verifiable flip-flop exists. Whether some design works for every consistent sheet is open.

**F11 (major): the pin does not remove F6's alternative conditions.**

- **Setup.** Take:
  - a continuous ClockOK clock c₀;
  - a causal Hold;
  - a state e₀ ∈ Hold(c₀, d, s) with t_k + t_cq^max ≤ s ≤ T' − t_su.
- **Two clocks.**
  - Clock A follows c₀ up to T', sits at V_IL + ε on (T', T' + t_slew − η], and then rises.
  - Clock B follows c₀ up to T', sits at V_IL until T'_B := T' + t_slew − η, and then rises the same way.
  - Both are continuous and ClockOK: A with edge T', B with edge T'_B. Both stay high until T'_B + t_slew + t_high and agree afterwards, and |A − B| ≤ ε everywhere.
  - Causality puts e₀ in Hold for both clocks.
  - THM L2.4 (`exists_lipschitz_dependence`) keeps the two trajectories from e₀ within K·ε of each other on a bounded window.
- **First contradiction.** Suppose t_su + t_h < t_slew − η. Let D be valid d' on A's window and ¬d' on B's window. FF2 and then FF1 give Q valid d' under A and ¬d' under B at T'_B + t_cq^max.
- **Second contradiction.** Suppose t_cq^max − t_cq^min < t_slew − η. FF1 under B keeps Q valid d up to T'_B + t_cq^min. FF2 under A, with D valid ¬d, gives Q valid ¬d at T' + t_cq^max ≤ T'_B + t_cq^min.
- **Conclusion.** For small ε each case contradicts K0. So a nonempty causal Hold forces t_su + t_h ≥ t_slew and t_cq^max − t_cq^min ≥ t_slew. The pin makes the edge a function of the waveform, but not a continuous one, while every trajectory depends continuously on the clock.
- **Proposed fix.** Add both conditions as MODEL fields next to F2's; TGMS26 meets them with 561 and 421. Keep the pin: it is harmless, though unused here. An optional Lean theorem `FFContract.slew_conditions` would take about 200 lines, built like `buridan`.

**F12 (minor): a spec remark is wrong.**

- **Problem.** The L3 sentence "No time-independent set works" is false when t_cq^max ≥ 2·t_slew + t_high + settling time. TGMS26 uses a time-independent Hold.
- **Proposed fix.** Replace the sentence with: "a time-independent set works when t_cq^max reaches past the fall slot; a smaller t_cq^max needs a phase-dependent set."

**F13 (owner decision): timing for an L4 non-vacuity witness.**

- **Problem.**
  - TGMS26 has t_h = 11 and t_cq^min = 0, and t_cd/t_pd = 1/90 per stage.
  - A register-to-register path therefore needs Σt_cd ≥ 11, which means Σt_pd ≈ 990.
  - The setup budget is only T_clk − s_max − t_cq^max − t_su = 29.
  - So an L4 witness with a feedback path is infeasible on the toy timing.
- **Proposed fix.** Add a second toy timing with t_slew = 1 (an ENV change), with the numbers in §7. F5 item 3 (t_in) still needs its own fix.

**F14 (stage 3): leakage.**

- **Problem.** With I_off > 0 the box Hold is false, so the tubes become charge-sum tubes (§4).
- **Consequences.**
  - The tubes need K15, which K0–K14 do not imply: K5 and K6 cover only an inverter's own off device, and NM/2 can be smaller than V_OL.
  - Hold then depends on the chip's capacitance laws. `SyncNet.Hold` is per netlist, so this is allowed. But H_cells' "fix any capacitance laws" then gives one Hold per chip, and Inv_L4 sees it.

## 10. Lemmas, in build order

Existing lemmas reused (all proved):

| Lemma | File | Use |
|---|---|---|
| `invariant_of_strict` | Circuit/Tube.lean | charge-sum tubes (stage 3) |
| `keeper_hold` | Cells/Keeper.lean | pattern for `agree_invariant` and `hold_invariant` (the loops here close through TGs) |
| `max_principle` | Circuit/Rails.lean | pattern for `max_principle_band` |
| `Netlist.rail_invariance`, `rail_invariance_set`, `rail_invariance_node` | Circuit/Rails.lean | rails at V_DD^max (standalone and embedded) |
| `abs_vf_le`, `abs_F_le_of_channel`, `F_nonpos_of_neighbours_le`, `F_nonneg_of_le_neighbours` | Circuit/Rails.lean | slew bounds; pattern for the side-sign lemmas |
| `Passive.apply_self`, `Passive.nonpos_of_le`, `Passive.nonneg_of_le`, `Regular.continuous` | Circuit/Rails.lean | TG direction (d) |
| `barrier_of_deriv_right_nonneg`, `linear_rise_of_deriv_right_ge`, `reach_of_deriv_right_ge`, `IsTrajOn.mono` | Circuit/Rails.lean | delays, Lyapunov reach, phase gluing |
| `IsInverter.F_out`, `current_n`, `current_p`, `out_mem_rails`, `Irise_le_F_out`, `F_out_le_neg_Ifall`, `propagation`, `contamination`, `Params.tpdINV`, `Params.tcdINV` | Cells/Inverter.lean | CKB, Y, B1, B2, Q |
| `charge`, `hasDerivAt_charge`, `charge_mem_Icc`, `strictMono_charge`, `IsTrajOn.hasDerivWithinAt_charge`, `HasDerivWithinAt.min_Ici` | Circuit/Charge.lean | pair-settle Lyapunov function; stage 3 tubes |
| `exists_isTrajOn`, `exists_lipschitz_dependence` | Circuit/WellPosed.lean | reachability witness; F11 |
| `Witness.exists_clockOK`, `Witness.dev`, `toy_contract`, `nodeCap_const`, `sheet_consistent` | Witness/ | toy instance |
| `FFContract.validOut_of_capture`, `buridan` | Cells/Buridan.lean | τ < t_{k+2}^r pattern; THM L3.3 witness |

New lemmas. Unless stated otherwise, assume `variable {n m : ℕ} {N : Netlist n m} {S : Params}`. The run hypotheses ⟨run⟩ abbreviate `(hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0) (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)`.

```lean
/-! L0 — locality (Circuit/Netlist.lean) -/
def Netlist.inflow (N : Netlist n m) (u : Fin m → ℝ) (e : Fin n → ℝ) (k : Fin n)
    (i : Fin N.nf) : ℝ :=
  (if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
    (if (N.fet i).d = .state k then (N.fet i).current u e else 0)
theorem Netlist.F_eq_sum_inflow {k : Fin n} {T : Finset (Fin N.nf)}
    (hT : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → i ∈ T)
    (u : Fin m → ℝ) (e : Fin n → ℝ) : N.F u e k = ∑ i ∈ T, N.inflow u e k i
def Params.par (S : Params) : Polarity → FETParams | .n => S.pn | .p => S.pp
def Netlist.ContractOn (N : Netlist n m) (S : Params) (T : Finset (Fin N.nf)) : Prop :=
  ∀ i ∈ T, FETContract (N.fet i).pol (S.par (N.fet i).pol) S.VDDmax (N.fet i).I

/-! L1 — band maximum principle (Circuit/Tube.lean); max_principle's ε-barrier for every
ε ≤ δ/(b − a + 1), then its limit step. Needed because a storage-node face is only non-strict (F_X ≤ 0). -/
theorem max_principle_band {ι : Type*} [Fintype ι] {x x' : ℝ → ι → ℝ} {a b V δ : ℝ}
    (hδ : 0 < δ) (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t) (ha : ∀ k, x a k ≤ V)
    (hface : ∀ t ∈ Ico a b, ∀ k, x t k ∈ Icc V (V + δ) → (∀ j, x t j ≤ x t k) → x' t k ≤ 0) :
    ∀ t ∈ Icc a b, ∀ k, x t k ≤ V

/-! L2 — band levels (Cells/Levels.lean) -/
def Params.θL (S : Params) : ℝ := (S.VOL + S.VIL) / 2
def Params.θH (S : Params) : ℝ := (S.VIH + S.VOH) / 2
def Params.δ₀ (S : Params) : ℝ := min S.NML S.NMH / 2
def Params.Lvl (S : Params) : Bool → ℝ → Prop | false, v => v ≤ S.θL | true, v => S.θH ≤ v
theorem Params.Consistent.band (hS : S.Consistent) : 0 < S.δ₀ ∧ S.VOL + S.δ₀ ≤ S.θL ∧
    S.θL + S.δ₀ ≤ S.VIL ∧ S.VIH + S.δ₀ ≤ S.θH ∧ S.θH + S.δ₀ ≤ S.VOH

/-! L3 — inverter core with side channels (Cells/InverterCore.lean) -/
structure Netlist.IsInvCore (N : Netlist n m) (inp : Node n m) (out : Fin n) (gnd vdd : Fin m)
    (iN iP : Fin N.nf) (side : Finset (Fin N.nf)) : Prop where
  ne : iN ≠ iP
  pol_n : (N.fet iN).pol = .n
  pol_p : (N.fet iP).pol = .p
  gate_n : (N.fet iN).g = inp
  gate_p : (N.fet iP).g = inp
  drain_n : (N.fet iN).d = .state out
  source_n : (N.fet iN).s = .bdry gnd
  drain_p : (N.fet iP).d = .state out
  source_p : (N.fet iP).s = .bdry vdd
  n_nmem : iN ∉ side
  p_nmem : iP ∉ side
  only : ∀ i, i ≠ iN → i ≠ iP → i ∉ side → (N.fet i).d ≠ .state out ∧ (N.fet i).s ≠ .state out
theorem Netlist.IsInverter.toCore (h : N.IsInverter inp out gnd vdd iN iP) :
    N.IsInvCore inp out gnd vdd iN iP ∅
theorem Netlist.IsInvCore.F_out (h : N.IsInvCore inp out gnd vdd iN iP side) (u e) :
    N.F u e out = -(N.fet iN).current u e - (N.fet iP).current u e + ∑ i ∈ side, N.inflow u e out i
-- common: (hS : S.Consistent) (h : N.IsInvCore inp out gnd vdd iN iP side)
--   (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I) (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)
--   (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) (hgnd : u gnd = 0) (hvdd : u vdd = VDD)
theorem Netlist.IsInvCore.core_le_neg_Ifall … (hin : S.validIn true (pot u e inp))
    (hout : e out ∈ Icc S.VOL S.VDDmax) :      -- above VDD: p-FET off (K4), conducts out (C1)
    -(N.fet iN).current u e - (N.fet iP).current u e ≤ -S.Ifall
theorem Netlist.IsInvCore.Irise_le_core … (hin : S.validIn false (pot u e inp))
    (hout : e out ∈ Icc 0 S.VOH) : S.Irise ≤ -(N.fet iN).current u e - (N.fet iP).current u e
theorem Netlist.IsInvCore.core_le_Ioff … (hin : S.validIn true (pot u e inp))
    (hout : e out ∈ Icc 0 S.VDDmax) : -(N.fet iN).current u e - (N.fet iP).current u e ≤ S.pp.Ioff
theorem Netlist.IsInvCore.neg_Ioff_le_core … (hin : S.validIn false (pot u e inp))
    (hout : e out ∈ Icc 0 VDD) : -S.pn.Ioff ≤ -(N.fet iN).current u e - (N.fet iP).current u e

/-! L4 — side-channel signs -/
theorem Netlist.sum_inflow_nonpos {k : Fin n} {T : Finset (Fin N.nf)} {u e}
    (hpr : ∀ i ∈ T, Passive (N.fet i).I ∧ Regular (N.fet i).I)
    (hfar : ∀ i ∈ T, ((N.fet i).s = .state k → pot u e (N.fet i).d ≤ e k) ∧
      ((N.fet i).d = .state k → pot u e (N.fet i).s ≤ e k)) : ∑ i ∈ T, N.inflow u e k i ≤ 0
theorem Netlist.sum_inflow_nonneg … -- far terminals ≥ e k ⇒ 0 ≤ ∑ i ∈ T, N.inflow u e k i

/-! L5 — propagation with side current; rails at V_DD^max -/
noncomputable def Params.tpdSide (S : Params) (ε Cmax : ℝ) : ℝ :=
  Cmax * max (S.VOH / (S.Irise - ε)) ((S.VDDmax - S.VOL) / (S.Ifall - ε))   -- tpdSide 0 = tpdINV
theorem Netlist.IsInvCore.propagation_side (hS) (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn) (hp) {Cmin Cmax : ℝ} (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax) {VDD u e t₀ t₁}
    (he : N.IsTrajOn u e t₀ t₁) ⟨run⟩ (hrail : ∀ t ∈ Icc t₀ t₁, e t out ∈ Icc 0 S.VDDmax)
    {x : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn x (pot (u t) (e t) inp))
    {ε : ℝ} (hε : 0 ≤ ε) (hεr : ε < min S.Irise S.Ifall)
    (hside : ∀ t ∈ Icc t₀ t₁, |∑ i ∈ side, N.inflow (u t) (e t) out i| ≤ ε) :
    (∀ t ∈ Icc (t₀ + S.tpdSide ε Cmax) t₁, S.validOut (!x) (e t out)) ∧
      ∀ t₂ ∈ Icc t₀ t₁, S.validOut (!x) (e t₂ out) → ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out)
theorem Netlist.IsInverter.propagation_rail …    -- `propagation`, with rails [0, V_DD^max] as hypothesis
theorem Netlist.IsInverter.contamination_rail …  -- `contamination`, likewise

/-! L6 — transmission gate (Cells/TransGate.lean) -/
structure Netlist.IsTG (N : Netlist n m) (x y : Fin n) (gn gp : Node n m) (jN jP : Fin N.nf) :
    Prop where
  ne : jN ≠ jP
  xy : x ≠ y
  pol_n : (N.fet jN).pol = .n
  pol_p : (N.fet jP).pol = .p
  gate_n : (N.fet jN).g = gn
  gate_p : (N.fet jP).g = gp
  chan_n : ((N.fet jN).d = .state y ∧ (N.fet jN).s = .state x) ∨
    ((N.fet jN).d = .state x ∧ (N.fet jN).s = .state y)
  chan_p : ((N.fet jP).d = .state y ∧ (N.fet jP).s = .state x) ∨
    ((N.fet jP).d = .state x ∧ (N.fet jP).s = .state y)
/-- Current through the gate from `y` into `x`. -/
def Netlist.IsTG.J (_ : N.IsTG x y gn gp jN jP) (u e) : ℝ := N.inflow u e x jN + N.inflow u e x jP
theorem Netlist.IsTG.inflow_y (h) : N.inflow u e y jN + N.inflow u e y jP = -h.J u e
theorem Netlist.IsTG.J_mul_nonneg (h) (C1, C2 for jN, jP) : 0 ≤ (e y - e x) * h.J u e
theorem Netlist.IsTG.abs_J_le_Ioff (hS) (h) (contracts) (hgn : pot u e gn ≤ S.VIL)
    (hgp : S.VIH ≤ pot u e gp) (hx : e x ∈ Icc 0 S.VDDmax) (hy : e y ∈ Icc 0 S.VDDmax) :
    |h.J u e| ≤ S.pn.Ioff + S.pp.Ioff                                          -- K1, K4
theorem Netlist.IsTG.J_ge_of_n_on (hS) (h) (contracts) (hgn : S.VIH ≤ pot u e gn)
    (hlo : min (e x) (e y) ≤ S.VOL) (hx) (hy) :
    min (S.pn.Gon * |e x - e y|) S.pn.Isat ≤ |h.J u e|                         -- K10
theorem Netlist.IsTG.J_ge_of_p_on (hS) (h) (contracts) (hgp : pot u e gp ≤ S.VIL)
    (hhi : S.VOH ≤ max (e x) (e y)) (hx) (hy) :
    min (S.pp.Gon * |e x - e y|) S.pp.Isat ≤ |h.J u e|                         -- K10
theorem Netlist.IsTG.abs_J_le_Imax … (gates and terminals in [0, V_DD^max]) :
    |h.J u e| ≤ S.pn.Imax + S.pp.Imax

/-! L7 — TG latch and its hold tube (Cells/TGLatch.lean) -/
structure Netlist.IsTGLatch (N : Netlist n m) (gnd vdd : Fin m) (i₁ : Node n m)
    (x y a₁ a₂ : Fin n) (g₁n g₁p g₂n g₂p : Node n m)
    (c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp : Fin N.nf) : Prop where
  core₁ : N.IsInvCore i₁ a₁ gnd vdd c₁n c₁p {t₁n, t₁p}
  core₂ : N.IsInvCore (.state y) a₂ gnd vdd c₂n c₂p {t₂n, t₂p}
  tg₁ : N.IsTG x a₁ g₁n g₁p t₁n t₁p
  tg₂ : N.IsTG x a₂ g₂n g₂p t₂n t₂p
  fwd : N.IsInverter (.state x) y gnd vdd yn yp
  only_x : ∀ i, ((N.fet i).d = .state x ∨ (N.fet i).s = .state x) → i ∈ ({t₁n, t₁p, t₂n, t₂p} : Finset _)
  distinct : a₁ ≠ a₂ ∧ x ≠ y      -- plus the remaining distinctness facts the proofs need
def latchAgree (S : Params) (b : Bool) (x y a₁ a₂ : Fin n) (e : Fin n → ℝ) : Prop :=
  S.Lvl (!b) (e a₁) ∧ S.Lvl (!b) (e x) ∧ S.Lvl (!b) (e a₂) ∧ S.validOut b (e y)
def latchHold (S : Params) (b : Bool) (x y a₂ : Fin n) (e : Fin n → ℝ) : Prop :=
  S.Lvl (!b) (e x) ∧ S.Lvl (!b) (e a₂) ∧ S.validOut b (e y)
-- common: (hS) (hL : N.IsTGLatch gnd vdd i₁ x y a₁ a₂ g₁n g₁p g₂n g₂p …)
--   (hc : N.ContractOn S {c₁n, c₁p, c₂n, c₂p, t₁n, t₁p, t₂n, t₂p, yn, yp})
--   (he : N.IsTrajOn u e t₀ t₁) ⟨run⟩
--   (hrail : ∀ t ∈ Icc t₀ t₁, ∀ k ∈ ({x, y, a₁, a₂} : Finset (Fin n)), e t k ∈ Icc 0 S.VDDmax)
theorem Netlist.IsTGLatch.hold_invariant … (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)
    (hoff : ∀ t ∈ Icc t₀ t₁, pot (u t) (e t) g₁n ≤ S.VIL ∧ S.VIH ≤ pot (u t) (e t) g₁p)
    {b : Bool} (h0 : latchHold S b x y a₂ (e t₀)) : ∀ t ∈ Icc t₀ t₁, latchHold S b x y a₂ (e t)

/-! L8 — the concrete netlist (Cells/TGFF.lean) -/
-- TGFF.gnd vdd clk d : Fin 4 := 0 1 2 3;  TGFF.CKB … TGFF.A4 : Fin 11 := 0 … 10
-- TGFF.pol : Fin 26 → Polarity;  TGFF.gate TGFF.drain TGFF.source : Fin 26 → Node 11 4  (§2 table)
def tgff (S : Params) (dev : Fin 26 → ℝ → ℝ → ℝ → ℝ) (C : Fin 11 → ℝ → ℝ)
    (hC : ∀ k v, 0 < C k v) : Netlist 11 4 where
  nf := 26
  fet i := ⟨TGFF.pol i, S.par (TGFF.pol i), dev i, TGFF.gate i, TGFF.drain i, TGFF.source i⟩
  C := C
  C_pos := hC
theorem tgff_inv_CKB : (tgff S dev C hC).IsInverter (.bdry TGFF.clk) TGFF.CKB TGFF.gnd TGFF.vdd 0 1
-- likewise Y (6 7), B1 (12 13), B2 (14 15), Q (20 21)
theorem tgff_master : (tgff S dev C hC).IsTGLatch TGFF.gnd TGFF.vdd (.bdry TGFF.d)
    TGFF.X TGFF.Y TGFF.A1 TGFF.A2 (.state TGFF.CKB) (.bdry TGFF.clk) (.bdry TGFF.clk)
    (.state TGFF.CKB) 2 3 8 9 4 5 10 11 6 7
theorem tgff_slave : (tgff S dev C hC).IsTGLatch TGFF.gnd TGFF.vdd (.state TGFF.B2)
    TGFF.Z TGFF.Q TGFF.B TGFF.A4 (.bdry TGFF.clk) (.state TGFF.CKB) (.state TGFF.CKB)
    (.bdry TGFF.clk) 16 17 22 23 18 19 24 25 20 21
theorem tgff_touchesChannel (j : Fin 4) : (tgff S dev C hC).TouchesChannel j ↔ j = TGFF.gnd ∨ j = TGFF.vdd
def tgffHold (S : Params) : (ℝ → ℝ) → Bool → ℝ → Set (Fin 11 → ℝ) := fun _ b _ =>
  {e | (∀ k, e k ∈ Icc 0 S.VDDmax) ∧ S.VOH ≤ e TGFF.CKB ∧ latchHold S b TGFF.Z TGFF.Q TGFF.A4 e}
theorem tgff_ff1 …   -- the `ff1` field of FFContract for tgff (§5), under hI and N6, N7
-- ▸ milestone A

/-! L9 — agree tube: no clock hypothesis -/
theorem Netlist.IsTGLatch.agree_invariant … {b : Bool}
    (hin : ∀ t ∈ Icc t₀ t₁, S.validIn b (pot (u t) (e t) i₁))
    (h0 : latchAgree S b x y a₁ a₂ (e t₀)) : ∀ t ∈ Icc t₀ t₁, latchAgree S b x y a₁ a₂ (e t)

/-! L10 — right derivative of max (Circuit/Charge.lean; dual of min_Ici) -/
theorem HasDerivWithinAt.max_Ici {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivWithinAt f f' (Ici t) t) (hg : HasDerivWithinAt g g' (Ici t) t) :
    HasDerivWithinAt (fun s => max (f s) (g s))
      (if g t < f t then f' else if f t < g t then g' else max f' g') (Ici t) t

/-! L11 — Lyapunov reach (Circuit/Tube.lean) -/
theorem reach_of_lyapunov {Φ Φ' : ℝ → ℝ} {P : ℝ → Prop} {t₀ t₁ : ℝ}
    (hΦ : ContinuousOn Φ (Icc t₀ t₁)) (hΦ' : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt Φ (Φ' t) (Ici t) t)
    (hdec : ∀ t ∈ Ico t₀ t₁, ¬ P t → Φ' t ≤ -1) (hpos : ∀ t ∈ Icc t₀ t₁, ¬ P t → 0 < Φ t)
    (hT : t₀ + max 0 (Φ t₀) ≤ t₁) : ∃ t ∈ Icc t₀ (t₀ + max 0 (Φ t₀)), P t

/-! L12 — settle with the loop open.
Lyapunov function for the low case: (q_A + q_X)/r₁ + (max(A, X) − θ_L)·C_X^max/r₂, where
r₁ = min(G_on^n V_OL, I_sat^n) and r₂ = min(G_on^n NM_L/2, I_sat^n).
The high case uses deficits clipped at V_OH; stage 1 may assume S.VDDmin = S.VDDmax there. -/
noncomputable def Params.PhiTG (S : Params) (CA CX : ℝ) : ℝ :=
  max ((CA + CX) * S.VDDmax / min (S.pn.Gon * S.VOL) S.pn.Isat
        + CX * S.VDDmax / min (S.pn.Gon * (S.NML / 2)) S.pn.Isat)
      ((CA + CX) * S.VDDmax / min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat
        + CX * S.VDDmax / min (S.pp.Gon * (S.NMH / 2)) S.pp.Isat)
theorem Netlist.IsTGLatch.pair_settle … (hI) {CminA CmaxA CminX CmaxX : ℝ}
    (hcA : NodeCap CminA CmaxA (N.C a₁)) (hcX : NodeCap CminX CmaxX (N.C x)) {b : Bool}
    (hin : ∀ t ∈ Icc t₀ t₁, S.validIn b (pot (u t) (e t) i₁))
    (hon : ∀ t ∈ Icc t₀ t₁, S.VIH ≤ pot (u t) (e t) g₁n ∧ pot (u t) (e t) g₁p ≤ S.VIL)
    (hoff₂ : ∀ t ∈ Icc t₀ t₁, pot (u t) (e t) g₂n ≤ S.VIL ∧ S.VIH ≤ pot (u t) (e t) g₂p) :
    ∀ t ∈ Icc (t₀ + S.PhiTG CmaxA CmaxX) t₁, S.Lvl (!b) (e t a₁) ∧ S.Lvl (!b) (e t x)
theorem Netlist.IsTGLatch.settle … (pair_settle's hypotheses) (hcY : NodeCap CminY CmaxY (N.C y))
    (hcA₂ : NodeCap CminA₂ CmaxA₂ (N.C a₂)) :
    ∀ t ∈ Icc (t₀ + S.PhiTG CmaxA CmaxX + S.tpdINV CmaxY + S.tpdINV CmaxA₂) t₁,
      latchAgree S b x y a₁ a₂ (e t)

/-! L13 — contamination chain of three pure inverters -/
theorem contamination_chain3 (hS) (h₀ : N.IsInverter inp y₀ gnd vdd i₀n i₀p)
    (h₁ : N.IsInverter (.state y₀) y₁ gnd vdd i₁n i₁p) (h₂ : N.IsInverter (.state y₁) y₂ gnd vdd i₂n i₂p)
    (hc : contracts of the six FETs) {C₀ C₁ C₂ : ℝ} (hcap : the three lower capacitance bounds)
    {VDD u e t₁ t₂} (he : N.IsTrajOn u e t₁ t₂) ⟨run⟩
    (hin : ∀ t ∈ Icc t₁ t₂, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax)
    (hrail : y₀, y₁, y₂ in [0, V_DD^max] on [t₁, t₂]) {b : Bool}
    (hb : S.validOut b (e t₁ y₀) ∧ S.validOut (!b) (e t₁ y₁) ∧ S.validOut b (e t₁ y₂)) :
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV C₀ + S.tcdINV C₁ + S.tcdINV C₂)), S.validIn b (e t y₂)

/-! L14 — timing bundle, capture, contract (Cells/TGFF.lean) -/
noncomputable def Params.σm (S : Params) (Cmax : Fin 11 → ℝ) : ℝ :=
  S.PhiTG (Cmax TGFF.A1) (Cmax TGFF.X) + S.tpdINV (Cmax TGFF.Y) + S.tpdINV (Cmax TGFF.A2)
noncomputable def Params.σs (S : Params) (Cmax : Fin 11 → ℝ) : ℝ :=
  S.PhiTG (Cmax TGFF.B) (Cmax TGFF.Z) + S.tpdINV (Cmax TGFF.Q) + S.tpdINV (Cmax TGFF.A4)
structure TGFFTiming (S : Params) (Cmin Cmax : Fin 11 → ℝ) : Prop where
  N1 : S.tslew + S.tpdINV (Cmax TGFF.CKB) ≤ S.th
  N2 : S.σm Cmax ≤ S.tsu
  N3 : S.σm Cmax + S.tpdINV (Cmax TGFF.B1) + S.tpdINV (Cmax TGFF.B2) + S.σs Cmax ≤
    S.tsu + S.tslew + S.thigh
  N4 : S.tpdINV (Cmax TGFF.CKB) + S.σs Cmax ≤ S.thigh
  N5 : S.tslew + S.tpdINV (Cmax TGFF.CKB) ≤
    S.tcdINV (Cmin TGFF.Y) + S.tcdINV (Cmin TGFF.B1) + S.tcdINV (Cmin TGFF.B2)
  N6 : 2 * S.tslew + S.thigh + S.tpdINV (Cmax TGFF.CKB) ≤ S.tcqmax
  N7 : S.tcqmin = 0
-- common: (hS : S.Consistent) (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)
--   (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))
--   (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (C k)) (ht : TGFFTiming S Cmin Cmax)
theorem tgff_capture … {VDD u e a b tg tr} (he : (tgff S dev C hC).IsTrajOn u e a b)
    (hrun : FFRun S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd VDD u e a b tg tr)
    {k : ℕ} {d' : Bool} (hs : tr (k + 1) - S.tsu ∈ Icc a b)
    (hlow : tr k + 2 * S.tslew + S.thigh ≤ tr (k + 1) - S.tsu)
    (hrail : ∀ j, e (tr (k + 1) - S.tsu) j ∈ Icc 0 S.VDDmax)
    (hckb : S.VOH ≤ e (tr (k + 1) - S.tsu) TGFF.CKB) (hb : tr (k + 1) + S.th ≤ b)
    (hD : ∀ t ∈ Icc (tr (k + 1) - S.tsu) (tr (k + 1) + S.th), S.validIn d' (u t TGFF.d))
    (hτ : tr (k + 1) + S.tcqmax ∈ Icc a b) :
    e (tr (k + 1) + S.tcqmax) ∈ tgffHold S (fun t => u t TGFF.clk) d' (tr (k + 1) + S.tcqmax)
theorem tgff_contract … :
    FFContract S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold S)
-- ▸ milestone B

/-! Witness (Witness/ToyFlipFlop.lean). `Witness.sheet` placeholders become
tsu := 550, th := 11, tcqmin := 0, tcqmax := 421. -/
def toyC : Fin 11 → ℝ := ![0.01, 0.1, 0.1, 0.1, 0.1, 52, 52, 0.1, 0.1, 0.1, 0.1]
def toyFF : Netlist 11 4 := tgff sheet (fun i => dev (TGFF.pol i) fetParams) (fun k _ => toyC k) _
theorem toy_timing : TGFFTiming sheet toyC toyC                                -- norm_num
theorem toy_tgff_contract :
    FFContract sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold sheet)
theorem toy_tgffHold_nonempty (clk : ℝ → ℝ) (b : Bool) (t : ℝ) : (tgffHold sheet clk b t).Nonempty
theorem toy_tgff_reachable (b : Bool) (e₀ : Fin 11 → ℝ) (he₀ : ∀ j, e₀ j ∈ Icc 0 1) :
    ∃ u e, toyFF.IsTrajOn u e 421 1421 ∧ e 421 = e₀ ∧
      FFRun sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd 1 u e 421 1421
        (fun k => k * 1000) (fun k => k * 1000) ∧
      e 1421 ∈ tgffHold sheet (fun t => u t TGFF.clk) b 1421
theorem toy_buridan …   -- every hypothesis of `buridan` for toyFF (k = 0, t_ρ = 1, t_obs = 1421)
-- ▸ milestone C

/-! Stage 2 — embedded instance -/
structure Netlist.IsTGFF (N : Netlist n m) (S : Params) (dPin : Node n m) (clk gnd vdd : Fin m)
    (ν : Fin 11 → Fin n) (φ : Fin 26 → Fin N.nf) : Prop where
  inj_ν : Function.Injective ν
  inj_φ : Function.Injective φ
  table : ∀ i, (N.fet (φ i)).pol = TGFF.pol i ∧ (N.fet (φ i)).P = S.par (TGFF.pol i) ∧
    (N.fet (φ i)).g = TGFF.relabel ν dPin clk gnd vdd (TGFF.gate i) ∧
    (N.fet (φ i)).d = TGFF.relabel ν dPin clk gnd vdd (TGFF.drain i) ∧
    (N.fet (φ i)).s = TGFF.relabel ν dPin clk gnd vdd (TGFF.source i)
  only : ∀ k j, ((N.fet j).d = .state (ν k) ∨ (N.fet j).s = .state (ν k)) → j ∈ Set.range φ
theorem Netlist.IsTGFF.contract (hS) (hI) (hff : N.IsTGFF S dPin clk gnd vdd ν φ)
    (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (N.fet (φ i)).I)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C (ν k))) (ht : TGFFTiming S Cmin Cmax) :
    FFContract S N dPin clk (ν TGFF.Q) gnd vdd (tgffHoldOn S ν)
```

## 11. Risks

Ranked, most serious first.

1. **Race margin.** It is thin and depends on the sheet. N5 is 10.41 against 10.09; N3 is 945.6 against 960. The B1/B2 capacitance spread must stay within about 4.8% at t_su = 550. The witness uses constant laws. One-sided contamination and staircase rise bounds (MS-NAND/NOR's L6′, about 250 lines) would widen the margin. See F10.
2. **`pair_settle` is new mathematics, checked only by hand (judge 1).** Its Lyapunov function involves right derivatives of max(A, X) with tie cases, and the high case uses clipped deficits once V_DD^min < V_DD^max. If a face sign fails, fall back as described in §12.
3. **`max_principle_band`.** The storage face satisfies only F_X ≤ 0, so `invariant_of_strict` does not apply at I_off = 0. The lemma is a near copy of `max_principle`, so the risk is low.
4. **I_off > 0.** The box Hold is false. The fix needs charge-sum tubes, K15, and a Hold that depends on the capacitance laws (F14). This is an owner decision for H_cells and Inv_L4.
5. **Rails at V_DD^max.** Hold has no V_DD, so the inverter lemmas need the V_DD^max versions (L5). Outputs in (VDD, V_DD^max] are handled by C1 and K4.
6. **Lean cost and the machine.** The machine is short on memory. A 26-FET `Netlist.F` must never be unfolded: go through `F_eq_sum_inflow`, prove one incidence lemma per node, and keep the files small. Do not use `decide` over large structures.
7. **L4.** The setup budget is 29 and t_cq^min = 0, so register feedback paths fail the hold checks on the toy timing (F13).
8. **t_cq^max = 421.** This follows from the time-independent Hold and the late slave settle at T' + 395.6. A smaller value needs a causal Hold and a faster chain; neither is needed for the spike.
9. **Embedding (stage 2).** The relabelling lemma for `IsTGFF` is needed. Q's fanout must be folded into C_Q's range. FFContract's timing is sheet-global, so every instance must share the same capacitance ranges.
10. **Evidence.** The argument is on paper; the simulation is a sanity check. The scripts live in a temp directory and should be copied into the repo's `scratch/` (not committed) before it is cleared.
11. **v1 coupling capacitance.** Explicit coupling capacitance would break the passivity and maximum-principle arguments the agree tubes rest on, as it breaks THM L2.3.

## 12. Stages

**Stage 1: toy devices (this decides the spike)**

- **Scope:**
  - `Witness.sheet` with t_su = 550, t_h = 11, t_cq^min = 0, t_cq^max = 421;
  - the toy clamp devices `Witness.dev`;
  - the constant capacitances of §2.
- **Proof route.** The lemmas carry contract hypotheses, since proofs specific to the toy devices are no shorter. `pair_settle`'s high case may assume `S.VDDmin = S.VDDmax`.
- **Milestones:**

| Milestone | Content | Lines | Agent-days |
|---|---|---|---|
| A | L0–L8 and `tgff_ff1`: the first nonempty invariant flip-flop hold tube | ~1.6k | ~5 |
| B | L9–L14, `tgff_capture`, FF2, `tgff_contract` | ~1.5k | ~5 |
| C | Witness/ToyFlipFlop.lean | ~250 | ~1 |

- **Acceptance:**
  1. `Witness.toy_tgff_contract` is proved.
  2. `toy_tgffHold_nonempty` (both bits) and `toy_tgff_reachable` are proved. The latter says every rail state at t = 421 reaches Hold(b) at t = 1421 along a trajectory with an `FFRun`.
  3. `toy_buridan` is proved, which makes THM L3.3 non-vacuous.
  4. `sheet_consistent`, `toy_contract`, `exists_clockOK` and the inverter witnesses still build. `lake build` is clean, there is no `sorry`, and the axioms are only `propext`, `Classical.choice` and `Quot.sound`.
  5. Docs are updated:
     - a CHANGELOG row for the placeholder timing;
     - STATUS rows for the H_cells flip-flop witness and the non-vacuous THM L3.3;
     - F10–F13 drafted in FINDINGS for the owner;
     - the pointer in `Charge.lean`'s module docstring corrected (TGMS26 has no stacks; charge sums apply to stage 3 and the v1 work).
- **Verdict.** The spike's answer is positive when acceptance items 1–3 hold. Milestone A is the first go/no-go point.

**Stage 2: all contract devices**

- **Scope:**
  - every sheet with I_off = 0 that satisfies `TGFFTiming`;
  - every device family in which each device meets its polarity's `FETContract`;
  - every capacitance law with `NodeCap` in [C_k^min, C_k^max];
  - V_DD^min < V_DD^max allowed.
- **Work:**
  - clipped-deficit `pair_settle` for the high case;
  - a symbolic `TGFFTiming`;
  - `IsTGFF` with its relabelling lemma, and `IsTGFF.contract`.
- **Effort:** ~0.6–1k lines, 3–5 agent-days.
- **Acceptance:**
  1. `tgff_contract` is proved with hypotheses hS, hI, hdev, hcap and ht only.
  2. `IsTGFF.contract` holds for an instance inside any netlist. D may be a state node of the driving cell, and Q's fanout must be gates only.
  3. A toy instance with non-constant ranges closes `TGFFTiming` by `norm_num`: C_B1, C_B2 ∈ [51, 52.5] with the other nodes constant (ΣC^min = 102 ≥ 100.8; ΣC^max = 105 ≤ 105.6, N3 954.6 ≤ 960).
  4. The same build and axiom criteria as stage 1.

**Stage 3: follow-ups (not part of the spike decision)**

- **I_off > 0.** Charge-sum Hold, K15 in `Params` (owner), a leaky `pair_settle`, and `invariant_of_strict`. About 500 lines, 1.5 days. Owner decision F14.
- **L4 non-vacuity witness.** Waits for the owner's decision on toy timing (F13).
- **`FFContract.slew_conditions`** (F11). About 200 lines.
- **v1 NAND2/NOR2, in parallel.** The cut-corner stack tube with its reach lemma, the top-off faces, and bottom-off charge sharing.

**Fallback triggers**

- **A face sign fails in Lean for a mathematical reason** (in `pair_settle`, `agree_invariant` or `hold_invariant`):
  - stop and record the counterexample;
  - switch to C2MOS-SK with the judges' fixes: clip internal-node charges at V_DD^min; use the time-independent Hold_L with t_cq^max ≈ 425; drop the phase detector.
- **Elaborating the 26-FET table is too slow on this machine:**
  - give each node one `F_eq_sum_inflow` instance in its own file;
  - never use `decide` over `Netlist.F`.