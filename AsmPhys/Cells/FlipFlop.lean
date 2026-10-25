import AsmPhys.Cells.Levels
import AsmPhys.Circuit.Netlist

/-!
# Clock pins and the flip-flop contract

The run has actual clock edges `t₀ < t₁ < …` at least `T_clk` apart (not on a fixed grid), and
flip-flop `r`'s `k`-th edge `t_k^r` lies in `[t_k, t_k + s_max]` (ENV).

`ClockOK` is the waveform condition on one clock pin. It strengthens the spec's condition
(`ClockOKSpec`, doc rev 46) with the fixes for docs/FINDINGS.md F1 and F6, adopted by the owner on
2026-10-24. Under the spec's version the clock may pulse between declared edges and a declared edge
may slide along a fast rise; FF1–FF2 then force every hold set to be empty. Under `ClockOK` the
declared edges are the only rising transitions, and each is the last instant at or below `V_IL`
before its rise.

The flip-flop contract FF1–FF2 is part of the cell-library hypothesis H_cells (MODEL in v0). It is
stated for one flip-flop instance of a netlist, with hold tubes `Hold clk d t` that may depend on
time through the clock waveform `clk`.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- Edge times (ENV): actual edges `tg` at least `T_clk` apart, and one flip-flop's edges `tr`
within the skew window `[t_k, t_k + s_max]`. -/
structure EdgesOK (S : Params) (tg tr : ℕ → ℝ) : Prop where
  /-- Actual edges are at least `T_clk` apart (ENV). -/
  spacing : ∀ k, S.Tclk ≤ tg (k + 1) - tg k
  /-- The flip-flop's edge lies in the skew window (ENV). -/
  skew : ∀ k, tr k ∈ Icc (tg k) (tg k + S.smax)

/-- The spec's ClockOK (doc rev 46), kept for reference: at most `V_IL` for `t_low` before each
edge, at least `V_IH` for `t_high` after the slew, and within `[0, V_DD]` at all times. It leaves
the clock free between those windows (FINDINGS F1) and does not tie the declared edge to the
waveform (F6). -/
structure ClockOKSpec (S : Params) (VDD : ℝ) (clk : ℝ → ℝ) (tr : ℕ → ℝ) : Prop where
  /-- Low phase before each edge (ENV). -/
  low : ∀ k, ∀ t ∈ Icc (tr k - S.tlow) (tr k), clk t ≤ S.VIL
  /-- High phase after each edge's slew (ENV). -/
  high : ∀ k, ∀ t ∈ Icc (tr k + S.tslew) (tr k + S.tslew + S.thigh), S.VIH ≤ clk t
  /-- The clock stays within the rails (ENV). -/
  rail : ∀ t, clk t ∈ Icc 0 VDD

/-- **ClockOK** (ENV) for a clock-pin waveform `clk` and the flip-flop's edges `tr`: the spec's
conditions, plus the fixes for F1 (low from the end of each fall, `t_k^r + 2·t_slew + t_high`, to
the next edge) and F6 (above `V_IL` throughout `(t_k^r, t_k^r + t_slew]`). -/
structure ClockOK (S : Params) (VDD : ℝ) (clk : ℝ → ℝ) (tr : ℕ → ℝ) : Prop where
  /-- Low phase before each edge (ENV). -/
  low : ∀ k, ∀ t ∈ Icc (tr k - S.tlow) (tr k), clk t ≤ S.VIL
  /-- Low from the end of each fall to the next edge, so the declared edges are the only rising
  transitions (ENV; fix for F1). -/
  low_between : ∀ k, ∀ t ∈ Icc (tr k + 2 * S.tslew + S.thigh) (tr (k + 1)), clk t ≤ S.VIL
  /-- Above `V_IL` throughout the rise, so the edge is the last instant at or below `V_IL`
  before it (ENV; fix for F6). -/
  pin : ∀ k, ∀ t ∈ Ioc (tr k) (tr k + S.tslew), S.VIL < clk t
  /-- High phase after each edge's slew (ENV). -/
  high : ∀ k, ∀ t ∈ Icc (tr k + S.tslew) (tr k + S.tslew + S.thigh), S.VIH ≤ clk t
  /-- The clock stays within the rails (ENV). -/
  rail : ∀ t, clk t ∈ Icc 0 VDD

/-- The adopted ClockOK implies the spec's. -/
theorem ClockOK.toSpec {S : Params} {VDD : ℝ} {clk : ℝ → ℝ} {tr : ℕ → ℝ}
    (h : ClockOK S VDD clk tr) : ClockOKSpec S VDD clk tr :=
  ⟨h.low, h.high, h.rail⟩

/-- The run conditions a flip-flop contract assumes: supply in range, ground at `0`, supply pin at
`V_DD`, valid edges, a ClockOK clock pin, and `D` within the rails on `[a, b]`. -/
structure FFRun (S : Params) (N : Netlist n m) (dPin : Node n m) (clk gnd vdd : Fin m)
    (VDD : ℝ) (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ) (a b : ℝ) (tg tr : ℕ → ℝ) : Prop where
  /-- Supply in range (ENV). -/
  vdd_mem : VDD ∈ Icc S.VDDmin S.VDDmax
  /-- Ground pin at `0` (ENV). -/
  gnd_eq : ∀ t ∈ Icc a b, u t gnd = 0
  /-- Supply pin at `V_DD` (ENV). -/
  vdd_eq : ∀ t ∈ Icc a b, u t vdd = VDD
  /-- Edge times (ENV). -/
  edges : EdgesOK S tg tr
  /-- Clock waveform (ENV). -/
  clockOK : ClockOK S VDD (fun t => u t clk) tr
  /-- `D` within the rails. -/
  d_rail : ∀ t ∈ Icc a b, pot (u t) (e t) dPin ∈ Icc 0 VDD

/-- **Flip-flop contract** FF1–FF2 (MODEL in v0, part of H_cells) for a flip-flop with data pin
`dPin`, clock pin `clk`, output state node `q`, ground and supply pins, and hold tubes `Hold`.
It quantifies over every trajectory on every interval `[a, b]`. -/
structure FFContract (S : Params) (N : Netlist n m) (dPin : Node n m) (clk : Fin m) (q : Fin n)
    (gnd vdd : Fin m) (Hold : (ℝ → ℝ) → Bool → ℝ → Set (Fin n → ℝ)) : Prop where
  /-- Setup time is nonnegative (MODEL; see docs/FINDINGS.md, F2). -/
  tsu_nonneg : 0 ≤ S.tsu
  /-- Hold time is nonnegative (MODEL; see docs/FINDINGS.md, F2). -/
  th_nonneg : 0 ≤ S.th
  /-- Minimum clock-to-Q delay is nonnegative (MODEL; see docs/FINDINGS.md, F2). -/
  tcqmin_nonneg : 0 ≤ S.tcqmin
  /-- Clock-to-Q bounds are strictly ordered (MODEL; see docs/FINDINGS.md, F2): with equality,
  FF1 for one edge and FF2 then FF1 for the next would give `Q` both levels at
  `t_{k+1}^r + t_cq^max`. -/
  tcqmin_lt_tcqmax : S.tcqmin < S.tcqmax
  /-- **FF1** (hold): from a hold state at some `s ∈ [t_k^r + t_cq^max, t_{k+1}^r)`, the state
  stays in the hold tube until `t_{k+1}^r` and `Q` stays `validOut d` until
  `t_{k+1}^r + t_cq^min`. -/
  ff1 : ∀ (VDD : ℝ) (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ) (a b : ℝ) (tg tr : ℕ → ℝ),
    N.IsTrajOn u e a b → FFRun S N dPin clk gnd vdd VDD u e a b tg tr →
    ∀ (k : ℕ) (d : Bool) (s : ℝ), s ∈ Icc a b → tr k + S.tcqmax ≤ s → s < tr (k + 1) →
      e s ∈ Hold (fun t => u t clk) d s →
      (∀ t ∈ Icc a b, s ≤ t → t < tr (k + 1) → e t ∈ Hold (fun t => u t clk) d t) ∧
        ∀ t ∈ Icc a b, s ≤ t → t ≤ tr (k + 1) + S.tcqmin → S.validOut d (e t q)
  /-- **FF2** (capture): from a hold state at some `s ∈ [t_k^r + t_cq^max, t_{k+1}^r − t_su]`,
  if `D` is `validIn d'` on `[t_{k+1}^r − t_su, t_{k+1}^r + t_h]`, then at
  `τ = t_{k+1}^r + t_cq^max` the state is in the hold tube of `d'`. The trajectory must cover the
  hold window and `τ`, since `IsTrajOn` says nothing about `e` outside `[a, b]`. -/
  ff2 : ∀ (VDD : ℝ) (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ) (a b : ℝ) (tg tr : ℕ → ℝ),
    N.IsTrajOn u e a b → FFRun S N dPin clk gnd vdd VDD u e a b tg tr →
    ∀ (k : ℕ) (d d' : Bool) (s : ℝ), s ∈ Icc a b → tr k + S.tcqmax ≤ s →
      s ≤ tr (k + 1) - S.tsu → e s ∈ Hold (fun t => u t clk) d s →
      tr (k + 1) + S.th ≤ b →
      (∀ t ∈ Icc (tr (k + 1) - S.tsu) (tr (k + 1) + S.th),
        S.validIn d' (pot (u t) (e t) dPin)) →
      tr (k + 1) + S.tcqmax ∈ Icc a b →
      e (tr (k + 1) + S.tcqmax) ∈ Hold (fun t => u t clk) d' (tr (k + 1) + S.tcqmax)

end AsmPhys
