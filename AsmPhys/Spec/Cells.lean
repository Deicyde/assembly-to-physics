import AsmPhys.Spec.Levels
import AsmPhys.Spec.Circuit
import Mathlib.Data.Finset.Lattice.Fold

/-!
# L3 — Inverters, cells and combinational DAGs

Part of the trusted specification: definitions only, importing only Mathlib and
`AsmPhys.Spec`. See README.md for how the layers fit together.

The inverter instance and its delays are the objects of THM L3.1–L3.2. A cell instance carries a
Boolean function, input nodes, an output state node and delays; along a trajectory on `[A, B]` it
*behaves* when it meets THM L3.1(a) and THM L3.2 with those delays. That is a theorem for INV
(`AsmPhys.Claims.inverter_behaves`) and part of the cell-library hypothesis H_cells for NAND2 and
NOR2.

A combinational DAG lists its cells in topological order. Each input slot of a cell is driven by an
earlier cell's output or is a DAG input. Arrival and expiry times propagate as
`a(n) = max_{In(n)} a + t_pd(n)` and `b(n) = min_{In(n)} b + t_cd(n)`; values propagate by the
cells' Boolean functions.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- A static CMOS inverter instance: input node `inp`, output state node `out`, ground and supply
boundary nodes `gnd` and `vdd`, an n-FET `iN` with drain at `out` and source at `gnd`, a p-FET `iP`
with drain at `out` and source at `vdd`, and no other channel terminal at `out`. -/
structure Netlist.IsInverter (N : Netlist n m) (inp : Node n m) (out : Fin n) (gnd vdd : Fin m)
    (iN iP : Fin N.nf) : Prop where
  ne : iN ≠ iP
  pol_n : (N.fet iN).pol = .n
  pol_p : (N.fet iP).pol = .p
  gate_n : (N.fet iN).g = inp
  gate_p : (N.fet iP).g = inp
  drain_n : (N.fet iN).d = .state out
  source_n : (N.fet iN).s = .bdry gnd
  drain_p : (N.fet iP).d = .state out
  source_p : (N.fet iP).s = .bdry vdd
  only : ∀ i, i ≠ iN → i ≠ iP → (N.fet i).d ≠ .state out ∧ (N.fet i).s ≠ .state out

namespace Params

/-- Propagation delay of an inverter whose output capacitance is at most `Cmax`:
`t_pd(INV) = C_out^max · max(V_OH / I_rise, (V_DD^max − V_OL) / I_fall)`. -/
noncomputable def tpdINV (S : Params) (Cmax : ℝ) : ℝ :=
  Cmax * max (S.VOH / S.Irise) ((S.VDDmax - S.VOL) / S.Ifall)

/-- Contamination delay of an inverter whose output capacitance is at least `Cmin`:
`t_cd = min(NM_L, NM_H) · C_out^min / (n_out · I_max)` with `n_out = 2` channels at the output and
`I_max` the larger of the two polarities' current bounds. -/
noncomputable def tcdINV (S : Params) (Cmin : ℝ) : ℝ :=
  min S.NML S.NMH * Cmin / (2 * max S.pn.Imax S.pp.Imax)

end Params

/-- A combinational cell instance. -/
structure Cell (n m : ℕ) where
  /-- Number of inputs. -/
  ar : ℕ
  /-- A cell has at least one input. -/
  ar_pos : 0 < ar
  /-- Boolean function. -/
  f : (Fin ar → Bool) → Bool
  /-- Input nodes. -/
  ins : Fin ar → Node n m
  /-- Output state node. -/
  out : Fin n
  /-- Propagation delay `t_pd`. -/
  tpd : ℝ
  /-- Contamination delay `t_cd`. -/
  tcd : ℝ

/-- A cell behaves along a trajectory `e` on `[A, B]` driven by `u`: it meets THM L3.1(a)
(valid inputs on `[t₀, t₁]` give a valid output on `[t₀ + t_pd, t₁]`) and THM L3.2 (a valid
output at `t₁` stays a valid input level until `t₁ + t_cd`), with nonnegative delays. -/
structure Cell.Behaves (S : Params) (c : Cell n m) (u : ℝ → Fin m → ℝ) (e : ℝ → Fin n → ℝ)
    (A B : ℝ) : Prop where
  /-- Nonnegative propagation delay. -/
  tpd_nonneg : 0 ≤ c.tpd
  /-- Nonnegative contamination delay. -/
  tcd_nonneg : 0 ≤ c.tcd
  /-- THM L3.1(a) along `e`. -/
  prop : ∀ (x : Fin c.ar → Bool) (t₀ t₁ : ℝ), A ≤ t₀ → t₁ ≤ B →
    (∀ j, ∀ t ∈ Icc t₀ t₁, S.validIn (x j) (pot (u t) (e t) (c.ins j))) →
    ∀ t ∈ Icc (t₀ + c.tpd) t₁, S.validOut (c.f x) (e t c.out)
  /-- THM L3.2 along `e`. -/
  contam : ∀ (b : Bool) (t₁ : ℝ), t₁ ∈ Icc A B → S.validOut b (e t₁ c.out) →
    ∀ t ∈ Icc t₁ (min B (t₁ + c.tcd)), S.validIn b (e t c.out)

namespace Netlist.IsInverter

variable {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m} {iN iP : Fin N.nf}

/-- The inverter instance as a cell: one input `inp`, output `out`, function `¬x`, and the
inverter's propagation and contamination delays for output capacitance in `[Cmin, Cmax]`. -/
noncomputable def cell (_hinv : N.IsInverter inp out gnd vdd iN iP) (S : Params)
    (Cmin Cmax : ℝ) : Cell n m where
  ar := 1
  ar_pos := one_pos
  f := fun x => !x 0
  ins := fun _ => inp
  out := out
  tpd := S.tpdINV Cmax
  tcd := S.tcdINV Cmin

end Netlist.IsInverter

/-- A combinational DAG of cells in topological order. Input slot `j` of cell `i` is driven by an
earlier cell `i'` (`src i j = some i'`, and then the slot's node is `i'`'s output) or is a DAG
input (`src i j = none`, a node no cell drives). Cell outputs are distinct. -/
structure CombDAG (n m : ℕ) where
  /-- Number of cells. -/
  nc : ℕ
  /-- The cells, in topological order. -/
  cell : Fin nc → Cell n m
  /-- The driver of each input slot. -/
  src : (i : Fin nc) → Fin (cell i).ar → Option (Fin nc)
  /-- Drivers come earlier. -/
  src_lt : ∀ i j i', src i j = some i' → i' < i
  /-- A driven slot's node is its driver's output. -/
  src_some : ∀ i j i', src i j = some i' → (cell i).ins j = .state (cell i').out
  /-- An undriven slot's node is no cell's output. -/
  src_none : ∀ i j, src i j = none → ∀ i', (cell i).ins j ≠ .state (cell i').out
  /-- Cell outputs are distinct. -/
  out_inj : Function.Injective fun i => (cell i).out

namespace CombDAG

variable (D : CombDAG n m)

/-- Boolean value of each cell's output, given the values `x` of the DAG inputs. -/
def val (x : Node n m → Bool) (i : Fin D.nc) : Bool :=
  (D.cell i).f fun j =>
    match h : D.src i j with
    | none => x ((D.cell i).ins j)
    | some i' =>
      have : i' < i := D.src_lt i j i' h
      val x i'
termination_by i

/-- Latest arrival time at the inputs of cell `i`, `max_{In(i)} a`, given the DAG inputs'
arrival times `a`. -/
noncomputable def inA (a : Node n m → ℝ) (i : Fin D.nc) : ℝ :=
  Finset.univ.sup' ⟨⟨0, (D.cell i).ar_pos⟩, Finset.mem_univ _⟩ fun j =>
    match h : D.src i j with
    | none => a ((D.cell i).ins j)
    | some i' =>
      have : i' < i := D.src_lt i j i' h
      inA a i' + (D.cell i').tpd
termination_by i

/-- Earliest expiry time at the inputs of cell `i`, `min_{In(i)} b`, given the DAG inputs'
expiry times `b`. -/
noncomputable def inB (b : Node n m → ℝ) (i : Fin D.nc) : ℝ :=
  Finset.univ.inf' ⟨⟨0, (D.cell i).ar_pos⟩, Finset.mem_univ _⟩ fun j =>
    match h : D.src i j with
    | none => b ((D.cell i).ins j)
    | some i' =>
      have : i' < i := D.src_lt i j i' h
      inB b i' + (D.cell i').tcd
termination_by i

/-- Arrival time of cell `i`'s output: `a(i) = max_{In(i)} a + t_pd(i)`. -/
noncomputable def arr (a : Node n m → ℝ) (i : Fin D.nc) : ℝ := D.inA a i + (D.cell i).tpd

/-- Expiry time of cell `i`'s output: `b(i) = min_{In(i)} b + t_cd(i)`. -/
noncomputable def exp (b : Node n m → ℝ) (i : Fin D.nc) : ℝ := D.inB b i + (D.cell i).tcd

/-- `i'` lies in the fan-in cone of `i`: it is `i` or drives an input of a cell in the cone. -/
inductive InCone : Fin D.nc → Fin D.nc → Prop
  | refl (i : Fin D.nc) : InCone i i
  | step {i i' i'' : Fin D.nc} (j : Fin (D.cell i').ar) :
      InCone i' i → D.src i' j = some i'' → InCone i'' i

end CombDAG

end AsmPhys
