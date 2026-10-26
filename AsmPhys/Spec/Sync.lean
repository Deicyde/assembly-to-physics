import AsmPhys.Spec.Cells
import AsmPhys.Spec.FlipFlop

/-!
# L4 — Synchronous netlists

Part of the trusted specification: definitions only, importing only Mathlib and
`AsmPhys.Spec`. See README.md for how the layers fit together.

A synchronous netlist is a circuit netlist with a combinational DAG of cells, flip-flops (each
with a D pin, a Q output node, its own clock pin and hold tubes), primary inputs and outputs. Its
Boolean semantics is a Mealy machine `(δ, λ)`: Q pins read the register state, primary inputs the
input bits, and cell outputs the DAG values.

Timing is checked once per netlist, relative to the clock edges, by per-node recursions (equal to
the spec's maximum and minimum over paths):

- arrival offsets after edge `t_k`: a Q pin at `s_max + t_cq^max` (the sampling instant), a
  primary input at `max(t_in, s_max + t_cq^max)` (docs/FINDINGS.md, F5);
- expiry offsets after edge `t_{k+1}`: a Q pin at `t_cq^min`, a primary input at `s_max + t_h`;
- setup: every D pin arrives by `T_clk − t_su`; hold: every D pin expires no earlier than
  `s_max + t_h`.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- A synchronous netlist (L4). -/
structure SyncNet (n m : ℕ) where
  /-- The circuit. -/
  N : Netlist n m
  /-- The combinational DAG of cells. -/
  D : CombDAG n m
  /-- Number of flip-flops (registers). -/
  nr : ℕ
  /-- D pin of each flip-flop. -/
  dPin : Fin nr → Node n m
  /-- Q output node of each flip-flop. -/
  qPin : Fin nr → Fin n
  /-- Clock pin of each flip-flop (one boundary node each). -/
  clk : Fin nr → Fin m
  /-- Hold tubes of each flip-flop, depending on its clock waveform. -/
  Hold : Fin nr → (ℝ → ℝ) → Bool → ℝ → Set (Fin n → ℝ)
  /-- Number of primary inputs. -/
  npi : ℕ
  /-- Primary input pins (boundary nodes). -/
  pi : Fin npi → Fin m
  /-- Number of primary outputs. -/
  npo : ℕ
  /-- Primary output nodes. -/
  po : Fin npo → Node n m
  /-- Ground pin. -/
  gnd : Fin m
  /-- Supply pin. -/
  vdd : Fin m
  /-- Distinct flip-flops have distinct Q nodes. -/
  qPin_inj : Function.Injective qPin
  /-- Distinct primary inputs have distinct pins. -/
  pi_inj : Function.Injective pi
  /-- No cell drives a Q node. -/
  out_ne_qPin : ∀ i r, (D.cell i).out ≠ qPin r
  /-- Every DAG input is a Q node or a primary input. -/
  slot_src : ∀ i j, D.src i j = none →
    (∃ r, (D.cell i).ins j = .state (qPin r)) ∨ ∃ p, (D.cell i).ins j = .bdry (pi p)
  /-- Every D pin is a cell output, a Q node or a primary input. -/
  dPin_src : ∀ r, (∃ i, dPin r = .state (D.cell i).out) ∨ (∃ r', dPin r = .state (qPin r')) ∨
    ∃ p, dPin r = .bdry (pi p)

namespace SyncNet

variable (Y : SyncNet n m)

open Classical in
/-- Value of a Q node or primary input under register state `σ` and input bits `x`
(`false` elsewhere). -/
noncomputable def srcVal (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (v : Node n m) : Bool :=
  if h : ∃ r, v = .state (Y.qPin r) then σ h.choose
  else if h : ∃ p, v = .bdry (Y.pi p) then x h.choose
  else false

open Classical in
/-- Value of any node: a cell output carries its DAG value, other nodes their `srcVal`. -/
noncomputable def nodeVal (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (v : Node n m) : Bool :=
  if h : ∃ i, v = .state (Y.D.cell i).out then Y.D.val (Y.srcVal σ x) h.choose
  else Y.srcVal σ x v

/-- Mealy next-state function `δ`. -/
noncomputable def δ (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) : Fin Y.nr → Bool :=
  fun r => Y.nodeVal σ x (Y.dPin r)

/-- Mealy output function `λ`. -/
noncomputable def out (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) : Fin Y.npo → Bool :=
  fun o => Y.nodeVal σ x (Y.po o)

open Classical in
/-- Arrival offset of a DAG input after its edge: `s_max + t_cq^max` for a Q node,
`max(t_in, s_max + t_cq^max)` for a primary input. -/
noncomputable def aRel (S : Params) (v : Node n m) : ℝ :=
  if ∃ r, v = .state (Y.qPin r) then S.smax + S.tcqmax else max S.tin (S.smax + S.tcqmax)

open Classical in
/-- Expiry offset of a DAG input after the next edge: `t_cq^min` for a Q node, `s_max + t_h` for a
primary input. -/
noncomputable def bRel (S : Params) (v : Node n m) : ℝ :=
  if ∃ r, v = .state (Y.qPin r) then S.tcqmin else S.smax + S.th

open Classical in
/-- Arrival offset of any node (cell outputs by the THM L3.4 recursion). -/
noncomputable def arrRel (S : Params) (v : Node n m) : ℝ :=
  if h : ∃ i, v = .state (Y.D.cell i).out then Y.D.arr (Y.aRel S) h.choose else Y.aRel S v

open Classical in
/-- Expiry offset of any node (cell outputs by the THM L3.4 recursion). -/
noncomputable def expRel (S : Params) (v : Node n m) : ℝ :=
  if h : ∃ i, v = .state (Y.D.cell i).out then Y.D.exp (Y.bRel S) h.choose else Y.bRel S v

/-- Setup on every path (THM, finite check): every D pin arrives by `T_clk − t_su`. -/
def SetupOK (S : Params) : Prop := ∀ r, Y.arrRel S (Y.dPin r) + S.tsu ≤ S.Tclk

/-- Hold on every path (THM, finite check): every D pin expires no earlier than `s_max + t_h`
after the next edge. -/
def HoldOK (S : Params) : Prop := ∀ r, S.th + S.smax ≤ Y.expRel S (Y.dPin r)

/-- The sampling instant `s_k = t_k + s_max + t_cq^max`. -/
def samp (S : Params) (tg : ℕ → ℝ) (k : ℕ) : ℝ := tg k + S.smax + S.tcqmax

/-- **U_ENV** (ENV): continuous boundary waveforms, ground at `0`, a constant supply in range, every
boundary node in the rails, edges at least `T_clk` apart, each flip-flop's edges in the skew window
with a ClockOK clock pin, and primary inputs valid from `t_k + t_in` to `t_{k+1} + s_max + t_h`. -/
structure UEnv (S : Params) (VDD : ℝ) (u : ℝ → Fin m → ℝ) (tg : ℕ → ℝ)
    (tr : Fin Y.nr → ℕ → ℝ) (xs : ℕ → Fin Y.npi → Bool) : Prop where
  /-- Supply in range (ENV). -/
  vdd_mem : VDD ∈ Icc S.VDDmin S.VDDmax
  /-- Continuous waveforms (ENV). -/
  cont : Continuous u
  /-- Ground at `0` (ENV). -/
  gnd_eq : ∀ t, u t Y.gnd = 0
  /-- Supply at `V_DD` (ENV). -/
  vdd_eq : ∀ t, u t Y.vdd = VDD
  /-- Every boundary node in the rails (ENV). -/
  rail : ∀ t j, u t j ∈ Icc 0 VDD
  /-- Actual edges are at least `T_clk` apart (ENV). -/
  spacing : ∀ k, S.Tclk ≤ tg (k + 1) - tg k
  /-- Edge spacing and skew for every flip-flop (ENV). -/
  edges : ∀ r, EdgesOK S tg (tr r)
  /-- ClockOK for every flip-flop's clock pin (ENV). -/
  clockOK : ∀ r, ClockOK S VDD (fun t => u t (Y.clk r)) (tr r)
  /-- Primary-input timing (ENV). -/
  pi_valid : ∀ k p, ∀ t ∈ Icc (tg k + S.tin) (tg (k + 1) + S.smax + S.th),
    S.validIn (xs k p) (u t (Y.pi p))

/-- **Inv_L4**: at time `s`, every flip-flop's state is in its hold tube for `σ`, and every state
node is in the rails. -/
def InvL4 (VDD : ℝ) (u : ℝ → Fin m → ℝ) (σ : Fin Y.nr → Bool) (s : ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ r, x ∈ Y.Hold r (fun t => u t (Y.clk r)) (σ r) s) ∧ ∀ k, x k ∈ Icc 0 VDD

end SyncNet

end AsmPhys
