# Findings for the spec owner

Each entry is a problem found while formalizing, with its consequence and a proposed fix. Nothing
here has been applied to the spec; the owner maintains the living copy. Entries also appear in the
change log ([CHANGELOG.md](CHANGELOG.md)).

## F1 (critical): ClockOK does not exclude undeclared edges, so every hold set must be empty

**Where.** L3 "Clock pins" (ClockOK_r), the flip-flop contract FF1–FF2, hence H_cells, Inv_L4,
THM L4.1, THM Core and the hypotheses of THM L3.3.

**Problem.** ClockOK_r constrains the clock only near each declared edge: low on
[t_k^r − t_low, t_k^r] and high on [t_k^r + t_slew, t_k^r + t_slew + t_high]. Between those windows
it may do anything within the rails, and edges need only be at least T_clk apart. So deleting a
declared edge from an admissible sequence leaves an admissible sequence for the same waveform:
ClockOK's clauses for the shorter sequence are a subset of those for the longer one, and the new
gap is at least 2·T_clk.

**Argument.** Take any continuous ClockOK clock for edges E2 = (…, t_k, p, t_{k+2}, …) and let E1
be E2 without p. Hold the D pin at a valid ¬d level, and start one trajectory (THM L2.2 existence)
in Hold(d, s) at s = t_k + t_cq^max. Trajectories do not depend on the declared edges, and Hold
depends only on the clock waveform ("through the clock waveform" in the spec; its type in Lean).

- Under E1, FF1 from s gives validOut(d, Q(t)) for all t ∈ [s, t_{k+2} + t_cq^min].
- Under E2, FF2 at p gives Hold(¬d) at τ = p + t_cq^max (K8 with t_su ≥ 0 places s before
  p − t_su), and FF1 then gives validOut(¬d, Q(τ)).
- τ < t_{k+2} + t_cq^min, since t_{k+2} − p ≥ T_clk > t_cq^max.

Q(τ) cannot be both ≤ V_OL and ≥ V_OH (K0). Every ClockOK clock can play the role of E2's clock
(delete any one of its edges), so FF1–FF2 force Hold(clk, d, s) = ∅ for every continuous ClockOK
clock, every k and every s ∈ [t_k^r + t_cq^max, t_{k+1}^r), which contains s_k. The argument needs
THM L2.2 existence, K0, K8, t_su ≥ 0 and t_cq^min ≥ 0. An independent adversarial review
(2026-10-24) checked every step and could not refute it.

**Consequence.** Empty Hold sets satisfy FF1–FF2 trivially, but then Inv_L4 fails for every
u ∈ U_ENV, THM L4.1 and THM L3.3 hold only vacuously, and MF_k holds only where dig(y_{k−1}) is
undefined. The MODEL bound then forces ε_cycle ≥ μ(G_mfg ∩ {dig(y_{k−1}) defined}); for k = 1 that
is at least 1 − ε_init − ε_mfg, so 1 − (ε_init + ε_mfg + N·ε_cycle) ≤ 0 for N ≥ 1 and the end-to-end
bound says nothing. This is the same failure mode as the missing K9. It also means the
non-vacuity witness for H_cells must exhibit a reachable state in Hold(d, s), not just FF1–FF2.

The only reading that escapes is Hold depending on the declared edges; then only
Hold_{E1} ∩ Hold_{E2} = ∅ follows. The spec says Hold depends on time through the clock waveform.

**Proposed fix.** Make the declared edges the only rising transitions. For every k:

1. CLK_r(t) ≤ V_IL on [t_k^r + 2·t_slew + t_high, t_{k+1}^r] (and on [t_0^r − t_low, t_0^r]);
2. CLK_r(t) ≥ V_IH on [t_k^r + t_slew, t_k^r + t_slew + t_high];
3. CLK_r(t) ∈ [0, V_DD] at all times.

Deleting an edge from a sequence admissible for this condition violates item 1 at the deleted
pulse, so the argument above no longer applies. K12 makes the low phase in item 1 last at least
t_low, since t_{k+1}^r − t_k^r ≥ T_clk − s_max. If the high phase should be allowed to last longer
than t_high, replace the fixed fall time by f_k ∈ [t_k^r + t_slew + t_high, t_{k+1}^r − t_slew − t_low].
Monotone slews (nondecreasing on [t_k^r, t_k^r + t_slew], nonincreasing on the fall) are an optional
realism strengthening for the v1 transistor-level tubes; they are not needed for non-vacuity. The fix
breaks nothing else: THM L3.3 and THM L4.1 use ClockOK only to build the flip-flop run conditions.
F6 is a second, independent way the declared edge escapes the waveform.

**Status in Lean.** Fix adopted by the owner on 2026-10-24, together with F6's: `ClockOK` in
`AsmPhys/Cells/FlipFlop.lean` is the fixed condition, and the spec's version is kept as
`ClockOKSpec` (`ClockOK.toSpec` shows the fixed one implies it). The monotone-slew strengthening
was not adopted. THM L3.3 and THM L4.1 were re-checked unchanged. The living spec still has the old
condition.

## F2 (minor): sign conditions on flip-flop and cell timing are missing

THM L4.1 and the window condition of THM L3.4 need t_su ≥ 0, t_h ≥ 0, t_cq^min ≥ 0, and t_pd,
t_cd ≥ 0 for every cell. For example, s_k < t_{k+1}^r follows from K8 only when t_su ≥ 0. The
clock-to-Q bounds must also be strictly ordered: with t_cq^min = t_cq^max, FF1 for one edge and FF2
then FF1 for the next give Q both levels at t_{k+1}^r + t_cq^max. Change made in Lean: these are
fields of `FFContract` (MODEL, part of H_cells) and of `Cell.Behaves`. For the inverter, t_pd and
t_cd are nonnegative by their formulas under K0–K14.

## F3 (major): K0–K12 do not keep the FET contract inhabited

**Where.** L1 FET contract with the parameter sheet.

**Problem.** Some consistency conditions that the contract clauses force are missing from K0–K12,
so a sheet can satisfy K0–K12 while no device meets C1–C6. Then every theorem quantifying over
contract-meeting devices holds vacuously for that sheet, the same failure mode K9 closed.

- C3 lets the gate be anything, so off-leakage at `d = s = 0` forces `I_off ≥ 0`.
- C4 at full swing (`|v_ds| = V_DD^max`, gate on and on the rail) with C6 forces
  `min(G_on·V_DD^max, I_sat) ≤ I_max`.
- A fixed Lipschitz constant `L_I` in C2, against C3 and C4 at `d = V_max`, `s = 0` with the gate
  at `V_off` and then `V_on`, forces `L_I·(V_on − V_off) ≥ min(G_on·V_max, I_sat) − I_off`.
  Counterexample: the toy levels with `L_I = 1` satisfy K0–K12, but `|I(0.55, 1, 0)| ≥ 1` and
  `|I(0.3, 1, 0)| ≤ 0` cannot both hold for a 1-Lipschitz `I`.
- Nothing requires `V_DD^min ≤ V_DD^max`, so U_ENV can be empty.

**Change made in Lean** (change log, 2026-10-24). C2 asserts that some Lipschitz constant exists (no
theorem uses its value), and K13 adds `I_off ≥ 0`, `min(G_on·V_DD^max, I_sat) ≤ I_max` for each
polarity, and `V_DD^min ≤ V_DD^max`. With these, every sheet satisfying K0–K13 has clamp devices
meeting both contracts (`Params.Consistent.exists_fetContract`). The owner should confirm K13 and
the removal of `L_I` from the sheet.

## F4 (minor): THM L2.5 needs the initial state on the rails

The spec's THM L2.5 assumes only that the boundary potentials lie in the rails. It is false without
`e(a)` on the rails as well; the counterexample is in the change log. The Lean statement adds the
hypothesis, which is how the spec's proof (via THM L2.3) already uses it.

## F5 (major): THM L4.1's windows reach outside the cycle the shell re-anchors

**Where.** L4 timing constraints and THM L4.1, as used by THM Core through MF_k.

MF_k supplies a model trajectory only on one cycle, `[s_{k−1}, s_k]`, started from Inv_L4, which
constrains flip-flop states and the rails but says nothing about combinational nodes. Two windows in
the L4.1 proof leave that interval:

1. **Hold window.** FF2 at edge `t_k^r` needs `D` valid until `t_k^r + t_h`, and
   `t_k^r ≤ t_k + s_max`, so the trajectory must reach `t_k + s_max + t_h`. It ends at
   `s_k = t_k + s_max + t_cq^max`, which is far enough only if `t_h ≤ t_cq^max`. The spec
   does not state this; the per-path hold check implies it only for a direct Q-to-D wire.
2. **Primary-input setup.** U_ENV makes a primary input valid from `t_k + t_in`, and the setup
   check for input paths is `t_in + Σ t_pd + t_su ≤ T_clk`. The model trajectory of the cycle
   starts at `s_k = t_k + s_max + t_cq^max`, with combinational nodes unconstrained there, so when
   `t_in < s_max + t_cq^max` the input's earlier validity cannot be used: arrival at a D pin is
   `max(t_in, s_max + t_cq^max) + Σ t_pd`, not `t_in + Σ t_pd`.

3. **Input windows overlap.** The input window of cycle k ends at `t_{k+1} + s_max + t_h` and that
   of cycle k+1 starts at `t_{k+1} + t_in`. When `t_in ≤ s_max + t_h` they overlap, the input must
   read as both `x_k` and `x_{k+1}` there, and K0 forces `x_{k+1} = x_k`: every admissible input
   sequence is constant. The toy sheet (`t_in = 0`, `s_max = 0`, `t_h = 1`) is such a case.

**Proposed fix.** Add `t_h ≤ t_cq^max` to the flip-flop timing conditions (MODEL, with F2), replace
`t_in` by `max(t_in, s_max + t_cq^max)` in the input-path setup check (or require
`t_in ≥ s_max + t_cq^max` in U_ENV), and require `s_max + t_h < t_in` (ENV). The v0 core has no
primary inputs, so items 2 and 3 do not affect THM Core.

**Status in Lean.** THM L4.1 (`SyncNet.refinement`) assumes `t_h ≤ t_cq^max` and uses
`max(t_in, s_max + t_cq^max)` as the input arrival offset. Item 3 is not yet enforced.

## F6 (critical for causal hold sets): a declared edge can slide within the slew window

**Where.** ClockOK_r with FF1–FF2; found by the adversarial review of 2026-10-24. F1's fix does not
remove it.

**Problem.** ClockOK does not determine t_k^r from the waveform. If the clock is at most V_IL until
c and rises above V_IH within ε < t_slew, then both t_k^r = c and t_k^r = c − t_slew + ε satisfy
ClockOK. FF1 for the later declaration keeps Q valid (old value) up to c + t_cq^min; FF2 then FF1
for the earlier one make Q valid (new value) at c − t_slew + ε + t_cq^max. Both hold whenever
ε ≤ t_slew − (t_cq^max − t_cq^min). A second variant contradicts when t_su + t_h < t_slew, with D
valid ¬d around one declaration and d around the other.

**Consequence.** For such fast clocks Hold must be empty. A clock that crosses V_IL exactly at
t_k and V_IH exactly at t_k + t_slew is unambiguous, so MF_k could still choose it. But a hold tube
built from a transistor-level circuit is causal (it depends on the clock only up to the current
time), and a slow clock's past can be continued by a fast edge, so causal Hold sets must be empty
for every clock whenever t_cq^max − t_cq^min < t_slew or t_su + t_h < t_slew. K0–K14 allow such
sheets.

**Proposed fix.** Either pin the edge to the waveform, by adding CLK_r(t) > V_IL on
(t_k^r, t_k^r + t_slew] (then t_k^r is the last time the clock is at most V_IL before the rise), or
add the MODEL conditions t_cq^max − t_cq^min ≥ t_slew and t_su + t_h ≥ t_slew (the flip-flop's
timing absorbs the edge uncertainty). With the pin and F1's fix, the edge sequence is a function of
the waveform.

**Status in Lean.** The pin was adopted by the owner on 2026-10-24 (`ClockOK.pin`). For a
continuous clock it forces the clock to equal `V_IL` exactly at each declared edge.

## F7 (major): sign conditions on the clock parameters are missing

**Where.** Parameter sheet (K8, K12), EdgesOK, ClockOK.

**Problem.** Nothing requires 0 < t_slew or 0 ≤ t_low, t_high, s_max, η, and K8 and K12 only
get easier when these are negative or zero. With t_slew ≤ 0 ≤ t_slew + t_high the instant t_k^r lies
in both the low and the high window, so no clock meets ClockOK; with s_max < 0 no edges meet the skew
condition; with t_high < 0 a dead clock is ClockOK; with η < 0 MF_k never holds. In each case
U_ENV is empty or FF1–FF2 hold trivially, and every theorem above L3 is vacuous. Counterexample:
the toy sheet with t_slew = −1 still satisfies K0–K13.

**Change made in Lean.** K14: 0 < t_slew, 0 ≤ t_low, 0 ≤ t_high, 0 ≤ s_max, 0 ≤ η.

## F8 (minor): flip-flop D pins must be gate-only

**Where.** H_cells and the static-CMOS rule for cells (THM L3.1–L3.2 need the output to touch only
the cell's own channels).

**Problem.** The textbook transmission-gate master–slave flip-flop puts a pass-transistor channel
on its D pin. The cell driving that D pin then has a foreign channel at its output, so THM L3.1–L3.2
do not apply to the last cell of any setup or hold path, which blocks THM L4.1.

**Proposed fix.** Require gate-only D inputs (an input inverter or a C²MOS input stage) as a
design constraint for the flip-flop spike, and add a structural `IsFlipFlop` predicate to H_cells.

## F9 (minor): primary outputs and the shell's view of future edges

1. **Primary outputs.** The spec's THM L4.1 says every primary output is valid on its THM L3.4
   window. The Lean `SyncNet.refinement_out` covers outputs driven by a cell. An output wired
   straight to a Q node or a primary input needs its own case (FF1 or U_ENV), and nothing in the
   netlist structure says what a primary output may be wired to. The v0 core has no primary
   outputs that THM Core uses.
2. **MF_k and edges past cycle k.** U_ENV constrains every edge of the sequence. If MF_k
   instantiates the edges with the chip's actual edges `edges(ω)` for all k ∈ ℕ, then a clock fault
   at any cycle j ≫ N falsifies MF_k for every k ≤ N, and ε_cycle must bound the probability of a
   clock fault over the chip's whole future. Proposed fix: MF_k may choose any edge sequence that
   agrees with `edges(ω)` on indices up to k + 1 (THM L4.1 already takes an arbitrary sequence).

<!-- F10–F14 come from the flip-flop spike design (docs/SPIKE-FLIPFLOP.md §9), reviewed by two
independent judges on 2026-10-25. They are drafts for the owner; nothing in them has been applied to
the spec. -->

## F10 (major): whether a verifiable flip-flop exists is a sheet condition.

- **Problem.**
  - ClockOK leaves the fall slot free within the rails, and in the rise slot it only requires CLK > V_IL.
  - Contract devices are unconstrained for gate drives in (V_off, V_on), so in both slots every latch may conduct.
  - The stored bit is then protected only by a contamination delay of at least t_slew + p_c on the master-to-slave path (N5). The other two designs need the same thing, and the negative-control simulation loses the bit in every cycle without it.
  - With C6-based bounds, every unit of contamination costs R units of propagation, R = 2·I_M·P_inv·C^max/(NM·C^min). R is 90 on the toy sheet, and about 17.5 with one-sided contamination and staircase rise bounds.
  - For TGMS26 this works out to roughly (R + 1)(t_slew + p_c) < T_clk − s_max (toy: 918 < 1000). K0–K14 do not imply it.
  - Monotone slews would not remove it, because the partial overlap of t_slew + p_c remains.
- **Proposed fix.** Keep the requirement as part of H_cells' MODEL timing, and record that K0–K14 alone do not guarantee that a verifiable flip-flop exists. Whether some design works for every consistent sheet is open.

## F11 (major): the pin does not remove F6's alternative conditions.

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

## F12 (minor): a spec remark is wrong.

- **Problem.** The L3 sentence "No time-independent set works" is false when t_cq^max ≥ 2·t_slew + t_high + settling time. TGMS26 uses a time-independent Hold.
- **Proposed fix.** Replace the sentence with: "a time-independent set works when t_cq^max reaches past the fall slot; a smaller t_cq^max needs a phase-dependent set."

## F13 (owner decision): timing for an L4 non-vacuity witness.

- **Problem.**
  - TGMS26 has t_h = 11 and t_cq^min = 0, and t_cd/t_pd = 1/90 per stage.
  - A register-to-register path therefore needs Σt_cd ≥ 11, which means Σt_pd ≈ 990.
  - The setup budget is only T_clk − s_max − t_cq^max − t_su = 29.
  - So an L4 witness with a feedback path is infeasible on the toy timing.
- **Proposed fix.** Add a second toy timing with t_slew = 1 (an ENV change), with the numbers in §7. F5 item 3 (t_in) still needs its own fix.

## F14 (stage 3): leakage.

- **Problem.** With I_off > 0 the box Hold is false, so the tubes become charge-sum tubes (§4).
- **Consequences.**
  - The tubes need K15, which K0–K14 do not imply: K5 and K6 cover only an inverter's own off device, and NM/2 can be smaller than V_OL.
  - Hold then depends on the chip's capacitance laws. `SyncNet.Hold` is per netlist, so this is allowed. But H_cells' "fix any capacitance laws" then gives one Hold per chip, and Inv_L4 sees it.
