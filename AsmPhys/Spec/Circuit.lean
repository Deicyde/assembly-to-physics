import AsmPhys.Spec.Device
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul

/-!
# L2 — Circuit model

Part of the trusted specification: definitions only, importing only Mathlib and
`AsmPhys.Spec`. See README.md for how the layers fit together.

The chip is modelled as a nodal ODE: one state per non-boundary node, grounded nonlinear
capacitance, and channel currents from the device functions (spec, "L2"):

  `C_k(e_k(t)) · ė_k(t) = F_k(t, e(t))`,   `k ∈ Fin n`.

Boundary nodes `j ∈ Fin m` carry prescribed potentials `u : ℝ → (Fin m → ℝ)` (ground, supply,
one clock pin per flip-flop, primary inputs). Trajectories live on an interval `[a, b]` and satisfy
the ODE as a right derivative on `[a, b)`.

Transistors are indexed by `Fin N.nf` rather than listed, so that sums over them are `Finset`
sums. The incidence matrix of a directed multigraph (THM L2.1) is defined at the end.
-/

namespace AsmPhys

noncomputable section

open Set

/-- A circuit node: a state node `k ∈ Fin n` or a boundary node `j ∈ Fin m`. -/
inductive Node (n m : ℕ)
  | state (k : Fin n)
  | bdry (j : Fin m)
  deriving DecidableEq

/-- A transistor: polarity, parameters, device function, and gate, drain and source terminals.
There is no body terminal, and the gate draws no current (MODEL, L1: gate and body currents are
zero; gate leakage is charged to the fidelity hypothesis MF_k). -/
structure FET (n m : ℕ) where
  /-- Polarity. -/
  pol : Polarity
  /-- Parameter sheet of this device's polarity. -/
  P : FETParams
  /-- Device function: channel current from drain to source at `(v_g, v_d, v_s)`. -/
  I : ℝ → ℝ → ℝ → ℝ
  /-- Gate terminal. -/
  g : Node n m
  /-- Drain terminal. -/
  d : Node n m
  /-- Source terminal. -/
  s : Node n m

/-- A netlist with `n` state nodes and `m` boundary nodes. -/
structure Netlist (n m : ℕ) where
  /-- Number of transistors. -/
  nf : ℕ
  /-- The transistors. -/
  fet : Fin nf → FET n m
  /-- Capacitance law `C_k` of each state node (MODEL; its range is MEAS, see `NodeCap`). -/
  C : Fin n → ℝ → ℝ
  /-- Every capacitance is positive (MEAS: implied by `NodeCap`'s positive lower bound). -/
  C_pos : ∀ k v, 0 < C k v

variable {n m : ℕ}

/-- Potential of a node, given boundary potentials `u` and state potentials `e`. -/
def pot (u : Fin m → ℝ) (e : Fin n → ℝ) : Node n m → ℝ
  | .state k => e k
  | .bdry j => u j

/-- Channel current of a transistor, drain to source, at node potentials `(u, e)`. -/
def FET.current (f : FET n m) (u : Fin m → ℝ) (e : Fin n → ℝ) : ℝ :=
  f.I (pot u e f.g) (pot u e f.d) (pot u e f.s)

namespace Netlist

variable (N : Netlist n m)

/-- Net channel current into state node `k` (drain-to-source convention): the currents of the
transistors with source at `k`, minus those with drain at `k`. Only channel currents enter, since
gate and body currents are zero (MODEL, see `FET`). -/
def F (u : Fin m → ℝ) (e : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, ((if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
    (if (N.fet i).d = .state k then (N.fet i).current u e else 0))

/-- The vector field of the nodal ODE: `ė_k = F_k(u, e) / C_k(e_k)`. Dividing by the node's own
capacitance encodes that all capacitance is grounded (MODEL: coupling capacitance is folded in
with Miller factors, the residual crosstalk is charged to MF_k). -/
def vf (u : Fin m → ℝ) (e : Fin n → ℝ) : Fin n → ℝ :=
  fun k => N.F u e k / N.C k (e k)

/-- A trajectory on `[a, b]` driven by boundary waveform `u`: continuous on `[a, b]`, with the
nodal ODE holding as a right derivative at every `t ∈ [a, b)`. -/
structure IsTrajOn (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ) (a b : ℝ) : Prop where
  /-- Continuity on the closed interval. -/
  continuousOn : ContinuousOn e (Icc a b)
  /-- The ODE, as a right derivative on `[a, b)`. -/
  hasDerivWithinAt : ∀ t ∈ Ico a b, HasDerivWithinAt e (N.vf (u t) (e t)) (Ici t) t

/-- Boundary node `j` is a drain or source terminal of some transistor. -/
def TouchesChannel (j : Fin m) : Prop :=
  ∃ i, (N.fet i).d = .bdry j ∨ (N.fet i).s = .bdry j

/-- Number of channel terminals at state node `k`: transistors with drain at `k` plus transistors
with source at `k` (a transistor with both terminals at `k` counts twice). -/
def nChan (k : Fin n) : ℕ :=
  (Finset.univ.filter fun i => (N.fet i).d = .state k).card +
    (Finset.univ.filter fun i => (N.fet i).s = .state k).card

end Netlist

/-- Incidence matrix of a directed multigraph whose branch `β` runs from `tail β` to `head β`:
`A k β = +1` if `k = tail β`, `−1` if `k = head β`, and `0` otherwise (so `0` on a self-loop). -/
def incidence {V Br : Type*} [DecidableEq V] (tail head : Br → V) : Matrix V Br ℝ :=
  Matrix.of fun k β => (if k = tail β then 1 else 0) - (if k = head β then 1 else 0)

end

end AsmPhys
