import AsmPhys.Cells.Compose
import AsmPhys.Cells.FlipFlop
import AsmPhys.Circuit.Rails

/-!
# L4 — Synchronous refinement

A synchronous netlist is a circuit netlist with a combinational DAG of cells, flip-flops (each
with a D pin, a Q output node, its own clock pin and hold tubes), primary inputs and outputs. Its
Boolean semantics is a Mealy machine `(δ, λ)`: Q pins read the register state, primary inputs the
input bits, and cell outputs the DAG values.

Timing is checked once per netlist, relative to the clock edges, by the per-node recursion of
THM L3.4, which equals the spec's maximum (minimum) over paths:

- arrival offsets after edge `t_k`: a Q pin at `s_max + t_cq^max` (the sampling instant), a
  primary input at `max(t_in, s_max + t_cq^max)` (docs/FINDINGS.md, F5);
- expiry offsets after edge `t_{k+1}`: a Q pin at `t_cq^min`, a primary input at `s_max + t_h`;
- setup: every D pin arrives by `T_clk − t_su`; hold: every D pin expires no earlier than
  `s_max + t_h`.

THM L4.1 runs on one cycle `[s_k, s_{k+1}]`, the interval the probabilistic shell re-anchors, so it
also needs `t_h ≤ t_cq^max` (F5).
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

namespace CombDAG

variable (D : CombDAG n m)

/-- If each slot's arrival time is at most `c`, then `max_{In(i)} a ≤ c`. -/
theorem inA_le {a : Node n m → ℝ} {i : Fin D.nc} {c : ℝ}
    (h : ∀ j, (D.src i j).elim (a ((D.cell i).ins j)) (D.arr a) ≤ c) : D.inA a i ≤ c := by
  rw [inA.eq_1]
  refine Finset.sup'_le _ _ fun j _ => le_trans (le_of_eq ?_) (h j)
  split <;> simp_all [arr]

/-- If `c` is at most each slot's expiry time, then `c ≤ min_{In(i)} b`. -/
theorem le_inB {b : Node n m → ℝ} {i : Fin D.nc} {c : ℝ}
    (h : ∀ j, c ≤ (D.src i j).elim (b ((D.cell i).ins j)) (D.exp b)) : c ≤ D.inB b i := by
  rw [inB.eq_1]
  refine Finset.le_inf' _ _ fun j _ => le_trans (h j) (le_of_eq ?_)
  split <;> simp_all [exp]

/-- Shifting every DAG input's arrival time by `c` shifts `max_{In(i)} a` by `c`. -/
theorem inA_const_add (c : ℝ) (a : Node n m → ℝ) (i : Fin D.nc) :
    D.inA (fun v => c + a v) i = c + D.inA a i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  have harr : ∀ j i', D.src i j = some i' → D.arr (fun v => c + a v) i' = c + D.arr a i' := by
    intro j i' hs
    rw [arr, arr, ih i' (D.src_lt i j i' hs)]
    ring
  refine le_antisymm (D.inA_le fun j => ?_) ?_
  · have h := D.le_inA a i j
    cases hs : D.src i j with
    | none =>
      rw [hs] at h
      simp only [Option.elim_none] at h ⊢
      linarith
    | some i' =>
      rw [hs] at h
      simp only [Option.elim_some] at h ⊢
      rw [harr j i' hs]
      linarith
  · have : D.inA a i ≤ D.inA (fun v => c + a v) i - c := D.inA_le fun j => by
      have h := D.le_inA (fun v => c + a v) i j
      cases hs : D.src i j with
      | none =>
        rw [hs] at h
        simp only [Option.elim_none] at h ⊢
        linarith
      | some i' =>
        rw [hs] at h
        simp only [Option.elim_some] at h ⊢
        rw [harr j i' hs] at h
        linarith
    linarith

/-- Shifting every DAG input's expiry time by `c` shifts `min_{In(i)} b` by `c`. -/
theorem inB_const_add (c : ℝ) (b : Node n m → ℝ) (i : Fin D.nc) :
    D.inB (fun v => c + b v) i = c + D.inB b i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  have hexp : ∀ j i', D.src i j = some i' → D.exp (fun v => c + b v) i' = c + D.exp b i' := by
    intro j i' hs
    rw [exp, exp, ih i' (D.src_lt i j i' hs)]
    ring
  refine le_antisymm ?_ (D.le_inB fun j => ?_)
  · have : D.inB (fun v => c + b v) i - c ≤ D.inB b i := D.le_inB fun j => by
      have h := D.inB_le (fun v => c + b v) i j
      cases hs : D.src i j with
      | none =>
        rw [hs] at h
        simp only [Option.elim_none] at h ⊢
        linarith
      | some i' =>
        rw [hs] at h
        simp only [Option.elim_some] at h ⊢
        rw [hexp j i' hs] at h
        linarith
    linarith
  · have h := D.inB_le b i j
    cases hs : D.src i j with
    | none =>
      rw [hs] at h
      simp only [Option.elim_none] at h ⊢
      linarith
    | some i' =>
      rw [hs] at h
      simp only [Option.elim_some] at h ⊢
      rw [hexp j i' hs]
      linarith

/-- Shifting every DAG input's arrival time by `c` shifts `a(i)` by `c`. -/
theorem arr_const_add (c : ℝ) (a : Node n m → ℝ) (i : Fin D.nc) :
    D.arr (fun v => c + a v) i = c + D.arr a i := by
  rw [arr, arr, inA_const_add]
  ring

/-- Shifting every DAG input's expiry time by `c` shifts `b(i)` by `c`. -/
theorem exp_const_add (c : ℝ) (b : Node n m → ℝ) (i : Fin D.nc) :
    D.exp (fun v => c + b v) i = c + D.exp b i := by
  rw [exp, exp, inB_const_add]
  ring

/-- With nonnegative propagation delays, arrival times grow along the fan-in cone:
`i'` in the cone of `i` gives `a(i') ≤ a(i)`. -/
theorem arr_le_arr_of_inCone (htpd : ∀ i, 0 ≤ (D.cell i).tpd) (a : Node n m → ℝ)
    {i' i : Fin D.nc} (h : D.InCone i' i) : D.arr a i' ≤ D.arr a i := by
  induction h with
  | refl => exact le_rfl
  | step j _ hs ih =>
    have h := D.le_inA a _ j
    rw [hs, Option.elim_some] at h
    exact (h.trans (le_add_of_nonneg_right (htpd _))).trans ih

/-- With nonnegative contamination delays, if every undriven slot's expiry time is at least `c`,
then `c ≤ min_{In(i)} b` for every cell `i`. -/
theorem le_inB_of_le (htcd : ∀ i, 0 ≤ (D.cell i).tcd) {b : Node n m → ℝ} {c : ℝ}
    (hb : ∀ i j, D.src i j = none → c ≤ b ((D.cell i).ins j)) (i : Fin D.nc) :
    c ≤ D.inB b i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  refine D.le_inB fun j => ?_
  cases hs : D.src i j with
  | none => exact hb i j hs
  | some i' =>
    rw [Option.elim_some, exp]
    exact (ih i' (D.src_lt i j i' hs)).trans (le_add_of_nonneg_right (htcd i'))

end CombDAG

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

/-! ### Helpers for THM L4.1 -/

/-- A Q node reads its register bit. -/
theorem srcVal_qPin (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (r : Fin Y.nr) :
    Y.srcVal σ x (.state (Y.qPin r)) = σ r := by
  have h : ∃ r', (Node.state (Y.qPin r) : Node n m) = .state (Y.qPin r') := ⟨r, rfl⟩
  rw [srcVal, dite_eq_left h]
  congr 1
  exact (Y.qPin_inj (Node.state.inj h.choose_spec)).symm

/-- A primary input reads its input bit. -/
theorem srcVal_pi (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (p : Fin Y.npi) :
    Y.srcVal σ x (.bdry (Y.pi p)) = x p := by
  have h₀ : ¬∃ r, (Node.bdry (Y.pi p) : Node n m) = .state (Y.qPin r) := by
    rintro ⟨_, ⟨⟩⟩
  have h : ∃ p', (Node.bdry (Y.pi p) : Node n m) = .bdry (Y.pi p') := ⟨p, rfl⟩
  rw [srcVal, dite_eq_right h₀, dite_eq_left h]
  congr 1
  exact (Y.pi_inj (Node.bdry.inj h.choose_spec)).symm

/-- A Q node arrives `s_max + t_cq^max` after its edge. -/
theorem aRel_qPin (S : Params) (r : Fin Y.nr) :
    Y.aRel S (.state (Y.qPin r)) = S.smax + S.tcqmax := by
  unfold aRel
  exact ite_eq_left ⟨r, rfl⟩

/-- A boundary node arrives `max(t_in, s_max + t_cq^max)` after its edge. -/
theorem aRel_bdry (S : Params) (j : Fin m) :
    Y.aRel S (.bdry j) = max S.tin (S.smax + S.tcqmax) := by
  unfold aRel
  exact ite_eq_right (by rintro ⟨_, ⟨⟩⟩)

/-- A Q node expires `t_cq^min` after the next edge. -/
theorem bRel_qPin (S : Params) (r : Fin Y.nr) : Y.bRel S (.state (Y.qPin r)) = S.tcqmin := by
  unfold bRel
  exact ite_eq_left ⟨r, rfl⟩

/-- A boundary node expires `s_max + t_h` after the next edge. -/
theorem bRel_bdry (S : Params) (j : Fin m) : Y.bRel S (.bdry j) = S.smax + S.th := by
  unfold bRel
  exact ite_eq_right (by rintro ⟨_, ⟨⟩⟩)

/-- No cell drives a Q node. -/
theorem not_exists_out_qPin (r : Fin Y.nr) :
    ¬∃ i, (Node.state (Y.qPin r) : Node n m) = .state (Y.D.cell i).out :=
  fun ⟨i, h⟩ => Y.out_ne_qPin i r (Node.state.inj h).symm

/-- No cell drives a boundary node. -/
theorem not_exists_out_bdry (j : Fin m) :
    ¬∃ i, (Node.bdry j : Node n m) = .state (Y.D.cell i).out := by
  rintro ⟨_, ⟨⟩⟩

/-- A cell output carries its DAG value. -/
theorem nodeVal_out (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (i : Fin Y.D.nc) :
    Y.nodeVal σ x (.state (Y.D.cell i).out) = Y.D.val (Y.srcVal σ x) i := by
  have h : ∃ i', (Node.state (Y.D.cell i).out : Node n m) = .state (Y.D.cell i').out := ⟨i, rfl⟩
  rw [nodeVal, dite_eq_left h]
  congr 1
  exact (Y.D.out_inj (Node.state.inj h.choose_spec)).symm

/-- No cell drives a Q node, so it carries its register bit. -/
theorem nodeVal_qPin (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (r : Fin Y.nr) :
    Y.nodeVal σ x (.state (Y.qPin r)) = σ r := by
  rw [nodeVal, dite_eq_right (Y.not_exists_out_qPin r), srcVal_qPin]

/-- No cell drives a primary input, so it carries its input bit. -/
theorem nodeVal_pi (σ : Fin Y.nr → Bool) (x : Fin Y.npi → Bool) (p : Fin Y.npi) :
    Y.nodeVal σ x (.bdry (Y.pi p)) = x p := by
  rw [nodeVal, dite_eq_right (Y.not_exists_out_bdry _), srcVal_pi]

/-- A cell output arrives by the THM L3.4 recursion. -/
theorem arrRel_out (S : Params) (i : Fin Y.D.nc) :
    Y.arrRel S (.state (Y.D.cell i).out) = Y.D.arr (Y.aRel S) i := by
  have h : ∃ i', (Node.state (Y.D.cell i).out : Node n m) = .state (Y.D.cell i').out := ⟨i, rfl⟩
  rw [arrRel, dite_eq_left h]
  congr 1
  exact (Y.D.out_inj (Node.state.inj h.choose_spec)).symm

/-- A node no cell drives arrives at its DAG-input offset. -/
theorem arrRel_of_not (S : Params) {v : Node n m} (h : ¬∃ i, v = .state (Y.D.cell i).out) :
    Y.arrRel S v = Y.aRel S v := by
  rw [arrRel, dite_eq_right h]

/-- A cell output expires by the THM L3.4 recursion. -/
theorem expRel_out (S : Params) (i : Fin Y.D.nc) :
    Y.expRel S (.state (Y.D.cell i).out) = Y.D.exp (Y.bRel S) i := by
  have h : ∃ i', (Node.state (Y.D.cell i).out : Node n m) = .state (Y.D.cell i').out := ⟨i, rfl⟩
  rw [expRel, dite_eq_left h]
  congr 1
  exact (Y.D.out_inj (Node.state.inj h.choose_spec)).symm

/-- A node no cell drives expires at its DAG-input offset. -/
theorem expRel_of_not (S : Params) {v : Node n m} (h : ¬∃ i, v = .state (Y.D.cell i).out) :
    Y.expRel S v = Y.bRel S v := by
  rw [expRel, dite_eq_right h]

/-- THM L2.3 under U_ENV: with C1 and C2, a trajectory on `[a, b]` that starts in the rails stays
in them. -/
theorem rails {S : Params} (hpass : ∀ i, Passive (Y.N.fet i).I)
    (hreg : ∀ i, Regular (Y.N.fet i).I) {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ}
    {tr : Fin Y.nr → ℕ → ℝ} {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)
    {e : ℝ → Fin n → ℝ} {a b : ℝ} (he : Y.N.IsTrajOn u e a b) (h0 : ∀ k, e a k ∈ Icc 0 VDD) :
    ∀ t ∈ Icc a b, ∀ k, e t k ∈ Icc 0 VDD :=
  Y.N.rail_invariance hpass hreg he (fun j _ t _ => henv.rail t j) h0

/-- U_ENV and the state in the rails on `[a, b]` give every flip-flop's run conditions there. -/
theorem ffRun {S : Params} {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ}
    {tr : Fin Y.nr → ℕ → ℝ} {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)
    {e : ℝ → Fin n → ℝ} {a b : ℝ} (hrail : ∀ t ∈ Icc a b, ∀ k, e t k ∈ Icc 0 VDD)
    (r : Fin Y.nr) : FFRun S Y.N (Y.dPin r) (Y.clk r) Y.gnd Y.vdd VDD u e a b tg (tr r) where
  vdd_mem := henv.vdd_mem
  gnd_eq t _ := henv.gnd_eq t
  vdd_eq t _ := henv.vdd_eq t
  edges := henv.edges r
  clockOK := henv.clockOK r
  d_rail t ht := by
    cases Y.dPin r with
    | state k => exact hrail t ht k
    | bdry j => exact henv.rail t j

/-- Q windows (FF1 from `s_k`): with the state in the rails on `[s_k, s_{k+1}]` and every
flip-flop in its hold tube for `σ` at `s_k`, each Q node is `validOut (σ r)` from `s_k` to
`t_{k+1}^r + t_cq^min`. -/
theorem q_window {S : Params} (hS : S.Consistent)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs) (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hrail : ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), ∀ k, e t k ∈ Icc 0 VDD)
    {σ : Fin Y.nr → Bool}
    (hhold : ∀ r, e (samp S tg k) ∈ Y.Hold r (fun t => u t (Y.clk r)) (σ r) (samp S tg k))
    (r : Fin Y.nr) :
    ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), t ≤ tr r (k + 1) + S.tcqmin →
      S.validOut (σ r) (e t (Y.qPin r)) := by
  have hA : samp S tg k = tg k + S.smax + S.tcqmax := rfl
  have hB : samp S tg (k + 1) = tg (k + 1) + S.smax + S.tcqmax := rfl
  have hK8 := hS.K8
  have hsm := hS.K14.2.2.2.1
  have hsu := (hff r).tsu_nonneg
  have hcq0 := (hff r).tcqmin_nonneg
  have hcq := (hff r).tcqmin_lt_tcqmax
  have hsp := (henv.edges r).spacing k
  have hsk := (henv.edges r).skew k
  have hsk1 := (henv.edges r).skew (k + 1)
  obtain ⟨hsk, hsk'⟩ := hsk
  obtain ⟨hsk1, hsk1'⟩ := hsk1
  intro t ht htq
  exact ((hff r).ff1 VDD u e _ _ tg (tr r) he (Y.ffRun henv hrail r) k (σ r) (samp S tg k)
    ⟨le_rfl, by linarith⟩ (by linarith) (by linarith) (hhold r)).2 t ht ht.1 htq

/-- Combinational windows (THM L3.4 in absolute time): with the state in the rails on
`[s_k, s_{k+1}]`, every flip-flop in its hold tube for `σ` at `s_k`, cells behaving, and the
window condition on the fan-in cone of `i`, cell `i`'s output is `validIn` of its value under
`(σ, x_k)` on `[t_k + a(i), t_{k+1} + b(i)]`, up to `s_{k+1}`. -/
theorem cell_valid {S : Params} (hS : S.Consistent)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs) (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hrail : ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), ∀ k, e t k ∈ Icc 0 VDD)
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
    {σ : Fin Y.nr → Bool}
    (hhold : ∀ r, e (samp S tg k) ∈ Y.Hold r (fun t => u t (Y.clk r)) (σ r) (samp S tg k))
    (i : Fin Y.D.nc)
    (hwin : ∀ i', Y.D.InCone i' i →
      tg k + Y.D.arr (Y.aRel S) i' ≤ tg (k + 1) + Y.D.inB (Y.bRel S) i') :
    ∀ t ∈ Icc (tg k + Y.D.arr (Y.aRel S) i) (tg (k + 1) + Y.D.exp (Y.bRel S) i),
      t ≤ samp S tg (k + 1) →
        S.validIn (Y.D.val (Y.srcVal σ (xs k)) i) (e t (Y.D.cell i).out) := by
  have hA : samp S tg k = tg k + S.smax + S.tcqmax := rfl
  have h := Y.D.timing hS hcells (Y.srcVal σ (xs k)) (fun v => tg k + Y.aRel S v)
    (fun v => tg (k + 1) + Y.bRel S v) ?_ i fun i' hi' => by
      rw [CombDAG.arr_const_add, CombDAG.inB_const_add]
      exact hwin i' hi'
  · rwa [CombDAG.arr_const_add, CombDAG.exp_const_add] at h
  intro i₁ j hs
  rcases Y.slot_src i₁ j hs with ⟨r, hr⟩ | ⟨p, hp⟩
  · simp only [hr, Y.aRel_qPin, Y.bRel_qPin, Y.srcVal_qPin, pot_state]
    have hsk1 := ((henv.edges r).skew (k + 1)).1
    refine ⟨le_of_eq (by rw [hA]; ring), fun t ht htB => hS.validIn_of_validOut ?_⟩
    exact Y.q_window hS hff henv k he hrail hhold r t ⟨by linarith [ht.1], htB⟩
      (by linarith [ht.2])
  · simp only [hp, Y.aRel_bdry, Y.bRel_bdry, Y.srcVal_pi, pot_bdry]
    have h1 := le_max_left S.tin (S.smax + S.tcqmax)
    have h2 := le_max_right S.tin (S.smax + S.tcqmax)
    exact ⟨by linarith, fun t ht _ => henv.pi_valid k p t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- THM L4.1's first two conclusions, given `s_k ≤ s_{k+1}`. -/
theorem refinement_of_samp_le {S : Params} (hS : S.Consistent)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
    (hpass : ∀ i, Passive (Y.N.fet i).I) (hreg : ∀ i, Regular (Y.N.fet i).I)
    (hsetup : Y.SetupOK S) (hhold : Y.HoldOK S) (hth : S.th ≤ S.tcqmax)
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)
    (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
    {σ : Fin Y.nr → Bool} (hinv : Y.InvL4 VDD u σ (samp S tg k) (e (samp S tg k)))
    (hAB : samp S tg k ≤ samp S tg (k + 1)) :
    Y.InvL4 VDD u (Y.δ σ (xs k)) (samp S tg (k + 1)) (e (samp S tg (k + 1))) ∧
      ∀ r, ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), t ≤ tg (k + 1) + S.tcqmin →
        S.validOut (σ r) (e t (Y.qPin r)) := by
  have hA : samp S tg k = tg k + S.smax + S.tcqmax := rfl
  have hB : samp S tg (k + 1) = tg (k + 1) + S.smax + S.tcqmax := rfl
  have hrail := Y.rails hpass hreg henv he hinv.2
  have hq := Y.q_window hS hff henv k he hrail hinv.1
  have hK8 := hS.K8
  have hsm := hS.K14.2.2.2.1
  have htpd : ∀ i, 0 ≤ (Y.D.cell i).tpd := fun i => (hcells i).tpd_nonneg
  have htcd : ∀ i, 0 ≤ (Y.D.cell i).tcd := fun i => (hcells i).tcd_nonneg
  refine ⟨⟨fun r => ?_, hrail _ ⟨hAB, le_rfl⟩⟩, fun r t ht htq => hq r t ht ?_⟩
  swap
  · linarith [((henv.edges r).skew (k + 1)).1]
  have hsu := (hff r).tsu_nonneg
  have hth0 := (hff r).th_nonneg
  have hcq0 := (hff r).tcqmin_nonneg
  have hcq := (hff r).tcqmin_lt_tcqmax
  have hsp := (henv.edges r).spacing k
  have hsp1 := (henv.edges r).spacing (k + 1)
  obtain ⟨hsk, hsk'⟩ := (henv.edges r).skew k
  obtain ⟨hsk1, hsk1'⟩ := (henv.edges r).skew (k + 1)
  obtain ⟨hsk2, -⟩ := (henv.edges r).skew (k + 1 + 1)
  -- The D pin is `validIn (δ σ x_k r)` on the capture window.
  have hD : ∀ t ∈ Icc (tr r (k + 1) - S.tsu) (tr r (k + 1) + S.th),
      S.validIn (Y.δ σ (xs k) r) (pot (u t) (e t) (Y.dPin r)) := by
    rintro t ⟨ht1, ht2⟩
    have htB : t ≤ samp S tg (k + 1) := by linarith
    rw [show Y.δ σ (xs k) r = Y.nodeVal σ (xs k) (Y.dPin r) from rfl]
    rcases Y.dPin_src r with ⟨i, hi⟩ | ⟨r', hr'⟩ | ⟨p, hp⟩
    · have hsu' := hsetup r
      rw [hi, arrRel_out] at hsu'
      have hho := hhold r
      rw [hi, expRel_out] at hho
      have hwin : ∀ i', Y.D.InCone i' i →
          tg k + Y.D.arr (Y.aRel S) i' ≤ tg (k + 1) + Y.D.inB (Y.bRel S) i' := by
        intro i' hi'
        have h1 := Y.D.arr_le_arr_of_inCone htpd (Y.aRel S) hi'
        have h2 : 0 ≤ Y.D.inB (Y.bRel S) i' := Y.D.le_inB_of_le htcd (fun i₁ j hs => by
          rcases Y.slot_src i₁ j hs with ⟨r₁, hr₁⟩ | ⟨p, hp⟩
          · rw [hr₁, bRel_qPin]
            exact (hff r₁).tcqmin_nonneg
          · rw [hp, bRel_bdry]
            linarith) i'
        linarith
      rw [hi, nodeVal_out, pot_state]
      exact Y.cell_valid hS hff henv k he hrail hcells hinv.1 i hwin t
        ⟨by linarith, by linarith⟩ htB
    · have hho := hhold r
      rw [hr', expRel_of_not _ _ (Y.not_exists_out_qPin r'), bRel_qPin] at hho
      rw [hr', nodeVal_qPin, pot_state]
      have hsk1r' := ((henv.edges r').skew (k + 1)).1
      exact hS.validIn_of_validOut (hq r' t ⟨by linarith, htB⟩ (by linarith))
    · have hsu' := hsetup r
      rw [hp, arrRel_of_not _ _ (Y.not_exists_out_bdry _), aRel_bdry] at hsu'
      rw [hp, nodeVal_pi, pot_bdry]
      have h1 := le_max_left S.tin (S.smax + S.tcqmax)
      exact henv.pi_valid k p t ⟨by linarith, by linarith⟩
  -- FF2 captures `δ σ x_k r` at `τ = t_{k+1}^r + t_cq^max`, and FF1 holds it until `s_{k+1}`.
  have hτ := (hff r).ff2 VDD u e _ _ tg (tr r) he (Y.ffRun henv hrail r) k (σ r)
    (Y.δ σ (xs k) r) (samp S tg k) ⟨le_rfl, hAB⟩ (by linarith) (by linarith) (hinv.1 r)
    (by linarith) hD ⟨by linarith, by linarith⟩
  exact ((hff r).ff1 VDD u e _ _ tg (tr r) he (Y.ffRun henv hrail r) (k + 1) (Y.δ σ (xs k) r)
    (tr r (k + 1) + S.tcqmax) ⟨by linarith, by linarith⟩ le_rfl (by linarith) hτ).1 _
    ⟨hAB, le_rfl⟩ (by linarith) (by linarith)

/-- **THM L4.1** (synchronous refinement), on one cycle `[s_k, s_{k+1}]`. Under the flip-flop
contracts, C1 and C2, setup and hold, `t_h ≤ t_cq^max`, U_ENV, cells behaving along the trajectory
and Inv_L4(σ) at `s_k`: Inv_L4(δ(σ, x_k)) holds at `s_{k+1}`, every Q node is `validOut (σ r)` from
`s_k` to `t_{k+1} + t_cq^min`, and every Q node is `validOut (δ(σ, x_k) r)` at `s_{k+1}` (the
spec's corollary, which THM Core reads through `dig`). -/
theorem refinement {S : Params} (hS : S.Consistent)                   -- THM (norm_num)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
                                                                    -- H_cells (MODEL in v0)
    (hpass : ∀ i, Passive (Y.N.fet i).I)                            -- MODEL (C1)
    (hreg : ∀ i, Regular (Y.N.fet i).I)                             -- MODEL (C2)
    (hsetup : Y.SetupOK S) (hhold : Y.HoldOK S)                     -- THM (finite checks)
    (hth : S.th ≤ S.tcqmax)                                         -- MODEL (FINDINGS F5)
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)   -- ENV
    (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
                                                                    -- THM (INV) / H_cells
    {σ : Fin Y.nr → Bool} (hinv : Y.InvL4 VDD u σ (samp S tg k) (e (samp S tg k))) :
    Y.InvL4 VDD u (Y.δ σ (xs k)) (samp S tg (k + 1)) (e (samp S tg (k + 1))) ∧
      (∀ r, ∀ t ∈ Icc (samp S tg k) (samp S tg (k + 1)), t ≤ tg (k + 1) + S.tcqmin →
        S.validOut (σ r) (e t (Y.qPin r))) ∧
      ∀ r, S.validOut (Y.δ σ (xs k) r) (e (samp S tg (k + 1)) (Y.qPin r)) := by
  have hK8 := hS.K8
  have hK12 := hS.K12
  obtain ⟨hslew, hlow, hhigh, hsm, -⟩ := hS.K14
  have hAB : samp S tg k ≤ samp S tg (k + 1) := by
    show tg k + S.smax + S.tcqmax ≤ tg (k + 1) + S.smax + S.tcqmax
    linarith [henv.spacing k]
  obtain ⟨hinv', hq⟩ :=
    Y.refinement_of_samp_le hS hff hpass hreg hsetup hhold hth henv k he hcells hinv hAB
  refine ⟨hinv', hq, fun r => ?_⟩
  have hrail := Y.rails hpass hreg henv he hinv.2
  have hsu := (hff r).tsu_nonneg
  have hcq0 := (hff r).tcqmin_nonneg
  have hsp1 := (henv.edges r).spacing (k + 1)
  obtain ⟨-, hsk1'⟩ := (henv.edges r).skew (k + 1)
  obtain ⟨hsk2, -⟩ := (henv.edges r).skew (k + 1 + 1)
  have hB : samp S tg (k + 1) = tg (k + 1) + S.smax + S.tcqmax := rfl
  exact ((hff r).ff1 VDD u e _ _ tg (tr r) he (Y.ffRun henv hrail r) (k + 1) (Y.δ σ (xs k) r)
    (samp S tg (k + 1)) ⟨hAB, le_rfl⟩ (by linarith) (by linarith) (hinv'.1 r)).2 _
    ⟨hAB, le_rfl⟩ le_rfl (by linarith)

/-- **THM L4.1**, primary outputs: a primary output driven by cell `i` is `validIn` of
`λ(σ, x_k)` on its THM L3.4 window `[t_k + a(i), t_{k+1} + b(i)]` (up to `s_{k+1}`), when THM L3.4's
window condition holds on `i`'s fan-in cone. C1 and C2 are needed: FF1 needs each D pin in the
rails, which for a state-node D pin only rail invariance supplies. -/
theorem refinement_out {S : Params} (hS : S.Consistent)               -- THM (norm_num)
    (hff : ∀ r, FFContract S Y.N (Y.dPin r) (Y.clk r) (Y.qPin r) Y.gnd Y.vdd (Y.Hold r))
                                                                    -- H_cells (MODEL in v0)
    (hpass : ∀ i, Passive (Y.N.fet i).I)                            -- MODEL (C1)
    (hreg : ∀ i, Regular (Y.N.fet i).I)                             -- MODEL (C2)
    {VDD : ℝ} {u : ℝ → Fin m → ℝ} {tg : ℕ → ℝ} {tr : Fin Y.nr → ℕ → ℝ}
    {xs : ℕ → Fin Y.npi → Bool} (henv : Y.UEnv S VDD u tg tr xs)   -- ENV
    (k : ℕ) {e : ℝ → Fin n → ℝ}
    (he : Y.N.IsTrajOn u e (samp S tg k) (samp S tg (k + 1)))
    (hcells : ∀ i, (Y.D.cell i).Behaves S u e (samp S tg k) (samp S tg (k + 1)))
                                                                    -- THM (INV) / H_cells
    {σ : Fin Y.nr → Bool} (hinv : Y.InvL4 VDD u σ (samp S tg k) (e (samp S tg k)))
    (o : Fin Y.npo) (i : Fin Y.D.nc) (hpo : Y.po o = .state (Y.D.cell i).out)
    (hwin : ∀ i', Y.D.InCone i' i →
      tg k + Y.D.arr (Y.aRel S) i' ≤ tg (k + 1) + Y.D.inB (Y.bRel S) i') :
    ∀ t ∈ Icc (tg k + Y.D.arr (Y.aRel S) i) (tg (k + 1) + Y.D.exp (Y.bRel S) i),
      t ≤ samp S tg (k + 1) → S.validIn (Y.out σ (xs k) o) (e t (Y.D.cell i).out) := by
  rw [show Y.out σ (xs k) o = Y.nodeVal σ (xs k) (Y.po o) from rfl, hpo, nodeVal_out]
  exact Y.cell_valid hS hff henv k he (Y.rails hpass hreg henv he hinv.2) hcells hinv.1 i hwin

end SyncNet

end AsmPhys
