import AsmPhys.Circuit.Tellegen
import AsmPhys.Circuit.WellPosed
import AsmPhys.Cells.InverterCell
import AsmPhys.Cells.Keeper
import AsmPhys.Cells.Buridan
import AsmPhys.Cells.TGFFCapture
import AsmPhys.Sync.Refinement
import AsmPhys.Shell.EndToEnd
import AsmPhys.Witness.ToyInverter
import AsmPhys.Witness.ToyFlipFlop

/-!
# Claims

The library's results (the spec's theorems, the flip-flop contract and the non-vacuity witnesses),
restated in terms of `AsmPhys.Spec` (the trusted model), the design layer `AsmPhys.Design` (the
circuits and toy instances the claims are about) and Mathlib. Each
statement below is copied from the theorem that proves it and closed by that theorem, so Lean
checks that the restated claim is exactly what was proved. `scripts/Audit.lean` checks that every
constant a claim mentions comes from `AsmPhys.Spec`, `AsmPhys.Design`, Mathlib or the Lean core,
and that every claim depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

To know what has been proved, read `AsmPhys/Spec`, `AsmPhys/Design` and this file. The rest of the
library (tubes, Lyapunov functions, charge functions, transmission gates, latches, the per-node
timing recursions) is proof machinery: its definitions appear in no claim, so a mistake in one of
them can make a proof fail but cannot change what is claimed.

Each hypothesis carries the tag of what justifies it (spec, "Assumption tags"): LAW, MODEL, MEAS,
ENV, THM or TCB. A bundle (`FETContract`, `NodeCap`, `UEnv`) is tagged by its fields, and its
comment summarizes them. Premises that only constrain the claim's own variables (trajectories,
initial states, logic values, observation times, the cell driving an output) carry no tag.
docs/ASSUMPTIONS.md lists the tagged hypotheses by tag.
-/

namespace AsmPhys.Claims

open Set MeasureTheory
open scoped NNReal

variable {n m : ℕ}

/-! ## L2 — Circuit model -/

section L2

open Matrix

/-- **THM L2.1** (Tellegen): for any directed multigraph, if `v = Aᵀ e` and `A i = 0`, then
`v ⬝ i = 0`. -/
theorem tellegen {V Br : Type*} [Fintype V] [DecidableEq V] [Fintype Br] (tail head : Br → V)
    (e : V → ℝ) (v i : Br → ℝ) (hv : v = (incidence tail head)ᵀ *ᵥ e)
    (hi : incidence tail head *ᵥ i = 0) : v ⬝ᵥ i = 0 :=
  AsmPhys.tellegen tail head e v i hv hi

/-- **THM L2.1** (Tellegen), for any matrix: if `v = Aᵀ e` and `A i = 0`, then `v ⬝ i = 0`. -/
theorem tellegen_matrix {V Br : Type*} [Fintype V] [Fintype Br] (A : Matrix V Br ℝ)
    (e : V → ℝ) (v i : Br → ℝ) (hv : v = Aᵀ *ᵥ e) (hi : A *ᵥ i = 0) : v ⬝ᵥ i = 0 :=
  AsmPhys.tellegen_matrix A e v i hv hi

/-- **THM L2.2** (well-posedness), existence: for continuous boundary waveforms, every initial
state has a trajectory on `[a, b]`. -/
theorem exists_isTrajOn (N : Netlist n m) {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))        -- MEAS range, MODEL Lipschitz law
    {u : ℝ → Fin m → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b))                        -- ENV
    (hab : a ≤ b) (e₀ : Fin n → ℝ) :
    ∃ e, N.IsTrajOn u e a b ∧ e a = e₀ :=
  N.exists_isTrajOn hreg hcap hu hab e₀

/-- **THM L2.2** (well-posedness), uniqueness: two trajectories on `[a, b]` with the same initial
state agree on `[a, b]`. -/
theorem isTrajOn_unique (N : Netlist n m) {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))        -- MEAS range, MODEL Lipschitz law
    {u : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b) (he' : N.IsTrajOn u e' a b) (h : e a = e' a) :
    EqOn e e' (Icc a b) :=
  N.isTrajOn_unique hreg hcap he he' h

/-- **THM L2.3** (rail invariance): if every device satisfies C1 and C2, every boundary node that
touches a channel stays in `[0, V]`, and the initial state lies in `[0, V]ⁿ`, then the trajectory
stays in `[0, V]ⁿ` on `[a, b]`. Gate-only boundary nodes are unconstrained. -/
theorem rail_invariance (N : Netlist n m)
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, N.TouchesChannel j → ∀ t ∈ Icc a b, u t j ∈ Icc 0 V)   -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, ∀ k, e t k ∈ Icc 0 V :=
  N.rail_invariance hpass hreg he hu h0

/-- Local rail invariance (from C1 and C2, as THM L2.3): let `K` be a set of state nodes whose
devices satisfy C1 and C2. Suppose that on `[a, b]` the other channel terminal of every device
with a drain or source in `K` is in `K` or has potential in `[0, V]`. If `K` starts in `[0, V]`,
it stays in `[0, V]` on `[a, b]`. -/
theorem rail_invariance_set (N : Netlist n m) {K : Set (Fin n)}
    (hpass : ∀ i, ∀ k ∈ K, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Passive (N.fet i).I)                                           -- MODEL (C1)
    (hreg : ∀ i, ∀ k ∈ K, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Regular (N.fet i).I)                                           -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hnb : ∀ t ∈ Icc a b, ∀ i, ∀ k ∈ K,
      ((N.fet i).d = .state k →
        (∃ j ∈ K, (N.fet i).s = .state j) ∨ pot (u t) (e t) (N.fet i).s ∈ Icc 0 V) ∧
      ((N.fet i).s = .state k →
        (∃ j ∈ K, (N.fet i).d = .state j) ∨ pot (u t) (e t) (N.fet i).d ∈ Icc 0 V))  -- ENV
    (h0 : ∀ k ∈ K, e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, ∀ k ∈ K, e t k ∈ Icc 0 V :=
  N.rail_invariance_set hpass hreg he hnb h0

/-- Local rail invariance for one state node (from C1 and C2): if the devices with a channel
terminal at `k` satisfy C1 and C2, and on `[a, b]` the other channel terminal of each of them is `k`
itself or has potential in `[0, V]`, then `e_k` stays in `[0, V]` once it starts there. -/
theorem rail_invariance_node (N : Netlist n m) {k : Fin n}
    (hpass : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Passive (N.fet i).I)                                           -- MODEL (C1)
    (hreg : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Regular (N.fet i).I)                                           -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hnb : ∀ t ∈ Icc a b, ∀ i,
      ((N.fet i).d = .state k →
        (N.fet i).s = .state k ∨ pot (u t) (e t) (N.fet i).s ∈ Icc 0 V) ∧
      ((N.fet i).s = .state k →
        (N.fet i).d = .state k ∨ pot (u t) (e t) (N.fet i).d ∈ Icc 0 V))  -- ENV
    (h0 : e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, e t k ∈ Icc 0 V :=
  N.rail_invariance_node hpass hreg he hnb h0

/-- **THM L2.4** (continuous dependence): the state at time `t ∈ [a, b]` depends
Lipschitz-continuously on the initial state and on the boundary waveform in the sup norm over
`[a, b]`, with constants depending only on the netlist and on `t − a`. -/
theorem exists_lipschitz_dependence (N : Netlist n m) {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :      -- MEAS range, MODEL Lipschitz law
    ∃ K Lu : ℝ≥0, ∀ {u u' : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b δ : ℝ},
      N.IsTrajOn u e a b → N.IsTrajOn u' e' a b →
      (∀ t ∈ Icc a b, ‖u t - u' t‖ ≤ δ) →
      ∀ t ∈ Icc a b, ‖e t - e' t‖ ≤
        Real.exp (K * (t - a)) * ‖e a - e' a‖ + Lu * (t - a) * Real.exp (K * (t - a)) * δ :=
  N.exists_lipschitz_dependence hreg hcap

/-- **THM L2.4**, Grönwall form: there are constants `K` (Lipschitz in the state) and `Lu`
(Lipschitz in the boundary waveform), depending only on the netlist, such that trajectories driven
by waveforms within `δ` of each other on `[a, b]` stay within the Grönwall bound. -/
theorem exists_dist_le_gronwallBound (N : Netlist n m) {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k)) :      -- MEAS range, MODEL Lipschitz law
    ∃ K Lu : ℝ≥0, ∀ {u u' : ℝ → Fin m → ℝ} {e e' : ℝ → Fin n → ℝ} {a b δ : ℝ},
      N.IsTrajOn u e a b → N.IsTrajOn u' e' a b →
      (∀ t ∈ Icc a b, ‖u t - u' t‖ ≤ δ) →
      ∀ t ∈ Icc a b, ‖e t - e' t‖ ≤ gronwallBound ‖e a - e' a‖ K (Lu * δ) (t - a) :=
  N.exists_dist_le_gronwallBound hreg hcap

/-- **THM L2.5** (slew bound): if all boundary potentials lie in `[0, Vmax]` and the initial state
does too, then `|ė_k(t)| ≤ n_k · I_max / C_k^min` on `[a, b]`, where `n_k` is the number of channel
terminals at node `k`. -/
theorem slew_bound (N : Netlist n m) {Cmin : Fin n → ℝ} {Imax Vmax : ℝ}
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hbd : ∀ i, BoundedOnRail Imax Vmax (N.fet i).I)       -- MEAS (C6)
    (hCmin : ∀ k, 0 < Cmin k)                              -- MEAS
    (hC : ∀ k v, Cmin k ≤ N.C k v)                         -- MEAS
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, ∀ t ∈ Icc a b, u t j ∈ Icc 0 Vmax)          -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 Vmax) :
    ∀ t ∈ Icc a b, ∀ k, |N.vf (u t) (e t) k| ≤ N.nChan k * Imax / Cmin k :=
  N.slew_bound hpass hreg hbd hCmin hC he hu h0

/-- **THM L2.5**, pointwise: if every terminal of every device with a channel terminal at `k`
lies in `[0, Vmax]`, those devices satisfy C6, and `0 < Cmin ≤ C_k(e_k)`, then
`|ė_k| ≤ n_k · I_max / C_min`. -/
theorem abs_vf_le (N : Netlist n m) {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n}
    {Cmin Imax Vmax : ℝ}
    (hbd : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      BoundedOnRail Imax Vmax (N.fet i).I)                           -- MEAS (C6)
    (hpot : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      pot u e (N.fet i).g ∈ Icc 0 Vmax ∧ pot u e (N.fet i).d ∈ Icc 0 Vmax ∧
        pot u e (N.fet i).s ∈ Icc 0 Vmax)
    (hCmin : 0 < Cmin) (hC : Cmin ≤ N.C k (e k)) :                   -- MEAS
    |N.vf u e k| ≤ N.nChan k * Imax / Cmin :=
  N.abs_vf_le hbd hpot hCmin hC

/-- **THM L2.5**, integrated form: each state potential is Lipschitz in time on `[a, b]` with
constant `n_k · I_max / C_k^min`. -/
theorem slew_lipschitz (N : Netlist n m) {Cmin : Fin n → ℝ} {Imax Vmax : ℝ}
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)                      -- MODEL (C2)
    (hbd : ∀ i, BoundedOnRail Imax Vmax (N.fet i).I)       -- MEAS (C6)
    (hCmin : ∀ k, 0 < Cmin k)                              -- MEAS
    (hC : ∀ k v, Cmin k ≤ N.C k v)                         -- MEAS
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, ∀ t ∈ Icc a b, u t j ∈ Icc 0 Vmax)          -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 Vmax) :
    ∀ k, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |e t k - e s k| ≤ N.nChan k * Imax / Cmin k * |t - s| :=
  N.slew_lipschitz hpass hreg hbd hCmin hC he hu h0

end L2

/-! ## L3 — Cells, flip-flops and combinational timing -/

section L3

/-- **THM L3.1** (propagation) for INV: if the input is `validIn x` on `[t₀, t₁]` and the output
starts in the rails, then (a) the output is `validOut (¬x)` on `[t₀ + t_pd, t₁]`, and (b) once it is
`validOut (¬x)` at some `t₂ ∈ [t₀, t₁]` it stays so on `[t₂, t₁]`. -/
theorem inverter_propagation {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m}
    {iN iP : Fin N.nf} {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    {x : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn x (pot (u t) (e t) inp))
    (h0 : e t₀ out ∈ Icc 0 VDD) :
    (∀ t ∈ Icc (t₀ + S.tpdINV Cmax) t₁, S.validOut (!x) (e t out)) ∧
      ∀ t₂ ∈ Icc t₀ t₁, S.validOut (!x) (e t₂ out) →
        ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out) :=
  Netlist.IsInverter.propagation hS hinv hn hp hcap hVDD he hgnd hvdd hin h0

/-- **THM L3.2** (contamination) for INV: if the output is `validOut b` at `t₁` (and in the rails),
then it is `validIn b` on `[t₁, t₁ + t_cd]`, whatever the input does within the rails. -/
theorem inverter_contamination {N : Netlist n m} {inp : Node n m} {out : Fin n}
    {gnd vdd : Fin m} {iN iP : Fin N.nf} {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hCmin : 0 < Cmin)                               -- MEAS
    (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)                          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₁ t₂ : ℝ}
    (he : N.IsTrajOn u e t₁ t₂)
    (hgnd : ∀ t ∈ Icc t₁ t₂, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₁ t₂, u t vdd = VDD)                          -- ENV
    (hin : ∀ t ∈ Icc t₁ t₂, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax)
    {b : Bool} (h1 : S.validOut b (e t₁ out)) (hrail : e t₁ out ∈ Icc 0 VDD) :
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV Cmin)), S.validIn b (e t out) :=
  Netlist.IsInverter.contamination hS hinv hn hp hCmin hcap hVDD he hgnd hvdd hin h1 hrail

/-- An inverter instance behaves as a cell (THM L3.1(a) and THM L3.2 with its delays) along any
trajectory on `[A, B]` whose output and input stay in the rails. -/
theorem inverter_behaves {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m}
    {iN iP : Fin N.nf} {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hCmin : 0 < Cmin)                               -- MEAS
    (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)                          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {A B : ℝ}
    (he : N.IsTrajOn u e A B)
    (hgnd : ∀ t ∈ Icc A B, u t gnd = 0)                              -- ENV
    (hvdd : ∀ t ∈ Icc A B, u t vdd = VDD)                            -- ENV
    (hout : ∀ t ∈ Icc A B, e t out ∈ Icc 0 VDD)
    (hin : ∀ t ∈ Icc A B, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax) :
    (hinv.cell S Cmin Cmax).Behaves S u e A B :=
  Netlist.IsInverter.behaves hS hinv hn hp hCmin hcap hVDD he hgnd hvdd hout hin

/-- **Keeper hold.** A cross-coupled inverter pair started with `x` a valid `0` and `y` a valid
`1`, both on the rails, keeps them so on `[a, b]`. -/
theorem keeper_hold {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
    {N : Netlist n m} {x y : Fin n} {gnd vdd : Fin m} {i1n i1p i2n i2p : Fin N.nf}
    (h1 : N.IsInverter (.state y) x gnd vdd i1n i1p)
    (h2 : N.IsInverter (.state x) y gnd vdd i2n i2p)
    (h1n : FETContract .n S.pn S.VDDmax (N.fet i1n).I)                -- MODEL/MEAS (C1–C6)
    (h1p : FETContract .p S.pp S.VDDmax (N.fet i1p).I)                -- MODEL/MEAS (C1–C6)
    (h2n : FETContract .n S.pn S.VDDmax (N.fet i2n).I)                -- MODEL/MEAS (C1–C6)
    (h2p : FETContract .p S.pp S.VDDmax (N.fet i2p).I)                -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                    -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hgnd : ∀ t ∈ Icc a b, u t gnd = 0)                               -- ENV
    (hvdd : ∀ t ∈ Icc a b, u t vdd = VDD)                             -- ENV
    (hx0 : e a x ∈ Icc 0 S.VOL) (hy0 : e a y ∈ Icc S.VOH VDD) :
    ∀ t ∈ Icc a b, e t x ≤ S.VOL ∧ S.VOH ≤ e t y :=
  AsmPhys.keeper_hold hS h1 h2 h1n h1p h2n h2p hVDD he hgnd hvdd hx0 hy0

/-- The adopted ClockOK (docs/FINDINGS.md F1, F6) implies the spec's. -/
theorem clockOK_toSpec {S : Params} {VDD : ℝ} {clk : ℝ → ℝ} {tr : ℕ → ℝ}
    (h : ClockOK S VDD clk tr) : ClockOKSpec S VDD clk tr :=
  h.toSpec

/-- **TGMS26 meets the flip-flop contract.** Without leakage, for every device family meeting the
per-polarity contracts, every capacitance law in range and every sheet satisfying N1–N7, the
transistor-level flip-flop satisfies FF1–FF2 with the time-independent hold tube `tgffHold`. -/
theorem tgff_contract {S : Params} (hS : S.Consistent)                -- THM (norm_num)
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {dev : Fin 26 → ℝ → ℝ → ℝ → ℝ} {C : Fin 11 → ℝ → ℝ}
    (hC : ∀ k v, 0 < C k v)                                          -- MEAS (implied by hcap)
    (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))  -- MODEL/MEAS
    {Cmin Cmax : Fin 11 → ℝ} (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (C k))       -- MEAS
    (ht : TGFFTiming S Cmin Cmax) :                                              -- MODEL
    FFContract S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd
      (tgffHold S) :=
  AsmPhys.tgff_contract (hC := hC) hS hI hdev hcap ht

/-- **THM L3.3** (Buridan): for a flip-flop meeting its contract, some start `τ` of a rise of the
data pin leaves `Q` exactly at `(V_IL + V_IH)/2` at an observation time one cycle later. -/
theorem buridan {S : Params} (hS : S.Consistent)                      -- THM (norm_num)
    {N : Netlist n m} {jD clk gnd vdd : Fin m} {q : Fin n}
    {Hold : (ℝ → ℝ) → Bool → ℝ → Set (Fin n → ℝ)}
    (hff : FFContract S N (.bdry jD) clk q gnd vdd Hold)              -- MODEL (H_cells)
    {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                                 -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))                   -- MEAS range, MODEL law
    (hD : jD ≠ clk ∧ jD ≠ gnd ∧ jD ≠ vdd)                             -- THM (pin check)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                    -- ENV
    {u₀ : ℝ → Fin m → ℝ} (hu₀ : Continuous u₀)                        -- ENV
    (hgnd : ∀ t, u₀ t gnd = 0) (hvdd : ∀ t, u₀ t vdd = VDD)           -- ENV
    {tg tr : ℕ → ℝ} (hedges : EdgesOK S tg tr)                        -- ENV
    (hclk : ClockOK S VDD (fun t => u₀ t clk) tr)                     -- ENV
    {ρ : ℝ → ℝ} {tρ : ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x ≤ 0, ρ x = 0)  -- ENV (data input)
    (hρ1 : ∀ x, tρ ≤ x → ρ x = VDD) (hρr : ∀ x, ρ x ∈ Icc 0 VDD)     -- ENV (data input)
    {k : ℕ} (hfit : tr k + S.tcqmax + tρ ≤ tr (k + 1) - S.tsu)       -- ENV (data input)
    {d₀ : Bool} {e₀ : Fin n → ℝ}
    (h0 : e₀ ∈ Hold (fun t => u₀ t clk) d₀ (tr k + S.tcqmax))
    {tobs : ℝ} (hobs : tobs ∈ Icc (tr (k + 1) + S.tcqmax) (tr (k + 2) + S.tcqmin)) :
    ∃ τ ∈ Icc (tr k + S.tcqmax) (tr (k + 1) + S.th), ∃ e : ℝ → Fin n → ℝ,
      N.IsTrajOn (fun t => Function.update (u₀ t) jD (ρ (t - τ))) e (tr k + S.tcqmax) tobs ∧
        e (tr k + S.tcqmax) = e₀ ∧ e tobs q = (S.VIL + S.VIH) / 2 :=
  AsmPhys.buridan hS hff hreg hcap hD hVDD hu₀ hgnd hvdd hedges hclk hρ hρ0 hρ1 hρr hfit h0 hobs

/-- **THM L3.4** (combinational timing, per node). Every cell behaves along `e` on `[A, B]`, and
every DAG input slot is `validIn` of its value on its window `[a, b]`, which starts no earlier than
`A`. If `a(i') ≤ min_{In(i')} b` for every cell `i'` in the fan-in cone of `i`, then `i`'s output is
`validIn` of its value on `[a(i), b(i)]`, up to `B`. -/
theorem combinational_timing (D : CombDAG n m) {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {A B : ℝ}
    (hbeh : ∀ i, (D.cell i).Behaves S u e A B)                    -- MODEL (H_cells)
    (x : Node n m → Bool) (a b : Node n m → ℝ)
    (hin : ∀ i j, D.src i j = none →
      A ≤ a ((D.cell i).ins j) ∧
        ∀ t ∈ Icc (a ((D.cell i).ins j)) (b ((D.cell i).ins j)), t ≤ B →
          S.validIn (x ((D.cell i).ins j)) (pot (u t) (e t) ((D.cell i).ins j)))
    (i : Fin D.nc)
    (hwin : ∀ i', D.InCone i' i → D.arr a i' ≤ D.inB b i') :          -- THM (finite check)
    ∀ t ∈ Icc (D.arr a i) (D.exp b i), t ≤ B → S.validIn (D.val x i) (e t (D.cell i).out) :=
  D.timing hS hbeh x a b hin i hwin

end L3

/-! ## L4 — Synchronous refinement -/

section L4

open SyncNet (samp)

/-- **THM L4.1** (synchronous refinement), on one cycle `[s_k, s_{k+1}]`. Under the flip-flop
contracts, C1 and C2, setup and hold, `t_h ≤ t_cq^max`, U_ENV, cells behaving along the trajectory
and Inv_L4(σ) at `s_k`: Inv_L4(δ(σ, x_k)) holds at `s_{k+1}`, every Q node is `validOut (σ r)` from
`s_k` to `t_{k+1} + t_cq^min`, and every Q node is `validOut (δ(σ, x_k) r)` at `s_{k+1}`. -/
theorem refinement (Y : SyncNet n m) {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
                                                                    -- MODEL (H_cells)
    (hpass : ∀ i, Passive (Y.N.fet i).I)                            -- MODEL (C1)
    (hreg : ∀ i, Regular (Y.N.fet i).I)                             -- MODEL (C2)
    (hsetup : Y.SetupOK S) (hhold : Y.HoldOK S)                     -- THM (finite checks)
    (hth : S.th ≤ S.tcqmax)                                         -- MODEL (FINDINGS F5)
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)   -- ENV
    (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
                                                                    -- MODEL (H_cells)
    {σ : Fin Y.nr → Bool} (hinv : Y.InvL4 VDD u σ (samp S tg k) (e (samp S tg k))) :
    Y.InvL4 VDD u (Y.δ σ (xs k)) (samp S tg (k + 1)) (e (samp S tg (k + 1))) ∧
      (∀ r, ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), t ≤ tg (k + 1) + S.tcqmin →
        S.validOut (σ r) (e t (Y.qPin r))) ∧
      ∀ r, S.validOut (Y.δ σ (xs k) r) (e (samp S tg (k + 1)) (Y.qPin r)) :=
  Y.refinement hS hff hpass hreg hsetup hhold hth henv k he hcells hinv

/-- **THM L4.1**, primary outputs: a primary output driven by cell `i` is `validIn` of
`λ(σ, x_k)` on its THM L3.4 window `[t_k + a(i), t_{k+1} + b(i)]` (up to `s_{k+1}`), when THM
L3.4's window condition holds on `i`'s fan-in cone. -/
theorem refinement_out (Y : SyncNet n m) {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
                                                                    -- MODEL (H_cells)
    (hpass : ∀ i, Passive (Y.N.fet i).I)                            -- MODEL (C1)
    (hreg : ∀ i, Regular (Y.N.fet i).I)                             -- MODEL (C2)
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)   -- ENV
    (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
                                                                    -- MODEL (H_cells)
    {σ : Fin Y.nr → Bool} (hinv : Y.InvL4 VDD u σ (samp S tg k) (e (samp S tg k)))
    (o : Fin Y.npo) (i : Fin Y.D.nc) (hpo : Y.po o = .state (Y.D.cell i).out)
    (hwin : ∀ i', Y.D.InCone i' i →                                 -- THM (finite check)
      tg k + Y.D.arr (Y.aRel S) i' ≤ tg (k + 1) + Y.D.inB (Y.bRel S) i') :
    ∀ t ∈ Icc (tg k + Y.D.arr (Y.aRel S) i) (tg (k + 1) + Y.D.exp (Y.bRel S) i),
      t ≤ samp S tg (k + 1) → S.validIn (Y.out σ (xs k) o) (e t (Y.D.cell i).out) :=
  Y.refinement_out hS hff hpass hreg henv k he hcells hinv o i hpo hwin

end L4

/-! ## Probabilistic shell -/

/-- **THM End-to-end**: `μ{ω | ∃ k ≤ N, ω ∈ bad k} ≤ ε_init + ε_mfg + N·ε_cycle`. -/
theorem end_to_end {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ginit Gmfg : Set Ω) (MF bad : ℕ → Set Ω) (N : ℕ) (εinit εmfg εcycle : ENNReal)
    (hinit : μ Ginitᶜ ≤ εinit)                                        -- MEAS
    (hmfg : μ Gmfgᶜ ≤ εmfg)                                           -- MEAS
    (hcyc : ∀ k ∈ Finset.Icc 1 N, μ ((MF k)ᶜ ∩ Gmfg) ≤ εcycle)        -- MODEL
    (hcore : ∀ ω ∈ Ginit ∩ Gmfg, (∀ k ∈ Finset.Icc 1 N, ω ∈ MF k) →   -- THM (THM Core)
      ∀ k ≤ N, ω ∉ bad k) :
    μ {ω | ∃ k ≤ N, ω ∈ bad k} ≤ εinit + εmfg + N * εcycle :=
  AsmPhys.end_to_end μ Ginit Gmfg MF bad N εinit εmfg εcycle hinit hmfg hcyc hcore

/-! ## Non-vacuity witnesses

The device contracts, the consistency conditions, ClockOK and the flip-flop contract are
satisfiable, and every hypothesis of THM L3.1 (INV) and of THM L3.3 holds for a concrete circuit.
THM L3.4, THM L4.1 and `keeper_hold` have no witness yet (docs/FINDINGS.md, F13). The toy objects
are defined in `AsmPhys.Design.Toy`. -/

section Witness

open AsmPhys.Toy

/-- Every sheet satisfying K0–K14 has devices of both polarities meeting their contracts (the
clamp devices). -/
theorem exists_fetContract {S : Params} (hS : S.Consistent) :
    FETContract .n S.pn S.VDDmax (dev .n S.pn) ∧ FETContract .p S.pp S.VDDmax (dev .p S.pp) :=
  hS.exists_fetContract

/-- The toy sheet satisfies K0–K14. -/
theorem sheet_consistent : sheet.Consistent :=
  AsmPhys.Witness.sheet_consistent

/-- The toy devices meet their contracts on the rail `[0, 1]`. -/
theorem toy_contract (pol : Polarity) : FETContract pol fetParams 1 (dev pol fetParams) :=
  AsmPhys.Witness.toy_contract pol

/-- Every hypothesis of THM L3.1 for INV holds for the toy inverter with its input held low. -/
theorem inv_propagation_hypotheses : ∃ (u : ℝ → Fin 3 → ℝ) (e : ℝ → Fin 1 → ℝ),
    sheet.Consistent ∧ inv.IsInverter (.bdry 2) 0 0 1 (0 : Fin 2) (1 : Fin 2) ∧
    FETContract .n sheet.pn sheet.VDDmax (inv.fet (0 : Fin 2)).I ∧
    FETContract .p sheet.pp sheet.VDDmax (inv.fet (1 : Fin 2)).I ∧
    (∀ v, inv.C 0 v ∈ Icc 1 1) ∧ (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax ∧
    inv.IsTrajOn u e 0 20 ∧ (∀ t ∈ Icc (0 : ℝ) 20, u t 0 = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 20, u t 1 = 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 20, sheet.validIn false (pot (u t) (e t) (.bdry 2))) ∧
    e 0 0 ∈ Icc 0 1 :=
  AsmPhys.Witness.inv_propagation_hypotheses

/-- The toy inverter with its input held low has a trajectory from `0` on `[0, 20]`, and its output
is `validOut 1` on `[9, 20]`. -/
theorem inv_rises : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 0]) e 0 20 ∧ e 0 = 0 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut true (e t 0) :=
  AsmPhys.Witness.inv_rises

/-- With the input held high, the toy inverter's output, started at `1`, is `validOut 0` on
`[9, 20]`. -/
theorem inv_falls : ∃ e : ℝ → Fin 1 → ℝ,
    inv.IsTrajOn (fun _ => ![0, 1, 1]) e 0 20 ∧ e 0 = 1 ∧
      ∀ t ∈ Icc 9 20, sheet.validOut false (e t 0) :=
  AsmPhys.Witness.inv_falls

/-- A continuous clock meeting the adopted ClockOK exists for every consistent sheet, with edges
`k·T_clk`. -/
theorem exists_clockOK {S : Params} (hS : S.Consistent) {VDD : ℝ}
    (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) :
    ∃ clk : ℝ → ℝ, Continuous clk ∧
      EdgesOK S (fun k => k * S.Tclk) (fun k => k * S.Tclk) ∧
      ClockOK S VDD clk (fun k => k * S.Tclk) :=
  AsmPhys.Witness.exists_clockOK hS hVDD

/-- H_cells' flip-flop clause is satisfiable: the toy flip-flop meets the flip-flop contract. -/
theorem toy_tgff_contract :
    FFContract sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold sheet) :=
  AsmPhys.Witness.toy_tgff_contract

/-- The toy flip-flop's hold tube of each bit is nonempty. -/
theorem toy_tgffHold_nonempty (clk : ℝ → ℝ) (b : Bool) (t : ℝ) :
    (tgffHold sheet clk b t).Nonempty :=
  AsmPhys.Witness.toy_tgffHold_nonempty clk b t

/-- The hold tube is reachable: from any state on the rails at `t = 421`, with a continuous ClockOK
clock (edges every 1000) and `D` held at `b`, the toy flip-flop's trajectory is in the hold tube of
`b` at `t = 1421`. -/
theorem toy_tgff_reachable (b : Bool) (e₀ : Fin 11 → ℝ) (he₀ : ∀ j, e₀ j ∈ Icc 0 1) :
    ∃ (u : ℝ → Fin 4 → ℝ) (e : ℝ → Fin 11 → ℝ), Continuous u ∧
      (∀ t, u t TGFF.d = if b then 1 else 0) ∧ toyFF.IsTrajOn u e 421 1421 ∧ e 421 = e₀ ∧
      FFRun sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd 1 u e 421 1421
        (fun k => (k : ℝ) * 1000) (fun k => (k : ℝ) * 1000) ∧
      e 1421 ∈ tgffHold sheet (fun t => u t TGFF.clk) b 1421 :=
  AsmPhys.Witness.toy_tgff_reachable b e₀ he₀

/-- Every hypothesis of THM L3.3 holds for the toy flip-flop. -/
theorem toy_buridan_hyps : ∃ clk : ℝ → ℝ,
    FFContract sheet toyFF (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd (tgffHold sheet) ∧
    (∀ i, Regular (toyFF.fet i).I) ∧ (∀ k, NodeCap (toyC k) (toyC k) (toyFF.C k)) ∧
    (TGFF.d ≠ TGFF.clk ∧ TGFF.d ≠ TGFF.gnd ∧ TGFF.d ≠ TGFF.vdd) ∧
    (1 : ℝ) ∈ Icc sheet.VDDmin sheet.VDDmax ∧
    Continuous (toyU clk 0) ∧ (∀ t, toyU clk 0 t TGFF.gnd = 0) ∧
    (∀ t, toyU clk 0 t TGFF.vdd = 1) ∧
    EdgesOK sheet (fun k => (k : ℝ) * sheet.Tclk) (fun k => (k : ℝ) * sheet.Tclk) ∧
    ClockOK sheet 1 (fun t => toyU clk 0 t TGFF.clk) (fun k => (k : ℝ) * sheet.Tclk) ∧
    Continuous (fun x : ℝ => max 0 (min 1 x)) ∧ (∀ x ≤ 0, max 0 (min 1 x) = 0) ∧
    (∀ x, 1 ≤ x → max 0 (min 1 x) = 1) ∧ (∀ x, max 0 (min 1 x) ∈ Icc (0 : ℝ) 1) ∧
    ((0 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax + 1 ≤ ((0 + 1 : ℕ) : ℝ) * sheet.Tclk - sheet.tsu ∧
    toyHoldState true ∈
      tgffHold sheet (fun t => toyU clk 0 t TGFF.clk) true (((0 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax) ∧
    (1421 : ℝ) ∈ Icc (((0 + 1 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmax)
      (((0 + 2 : ℕ) : ℝ) * sheet.Tclk + sheet.tcqmin) :=
  AsmPhys.Witness.toy_buridan_hyps

/-- THM L3.3 holds non-vacuously: for the toy flip-flop with a continuous ClockOK clock, started in
its hold tube at `t = 421`, some start `τ` of a unit-slope rise of `D` leaves `Q` exactly at
`(V_IL + V_IH)/2` at `t = 1421`. -/
theorem toy_buridan : ∃ clk : ℝ → ℝ, Continuous clk ∧ ClockOK sheet 1 clk (fun k => (k : ℝ) * 1000) ∧
    ∃ τ ∈ Icc (421 : ℝ) 1011, ∃ e : ℝ → Fin 11 → ℝ,
      toyFF.IsTrajOn
        (fun t => Function.update ![0, 1, clk t, 0] TGFF.d (max 0 (min 1 (t - τ)))) e 421 1421 ∧
      e 421 ∈ tgffHold sheet clk true 421 ∧ e 1421 TGFF.Q = (sheet.VIL + sheet.VIH) / 2 :=
  AsmPhys.Witness.toy_buridan

end Witness

end AsmPhys.Claims
