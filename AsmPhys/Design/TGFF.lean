import AsmPhys.Design.Latch
import AsmPhys.Spec.Cells

/-!
# TGMS26: a transmission-gate master–slave flip-flop

Part of the design layer: definitions only, importing only Mathlib, `AsmPhys.Spec` and
`AsmPhys.Design`. See README.md for how the layers fit together.

The flip-flop of docs/SPIKE-FLIPFLOP.md: 26 transistors, 11 state nodes, boundary nodes ground,
supply, clock and data. The clock drives an internal inverter `CKB`. The master latch stores at `X`
(input gate TG1 from `A1 = ¬D`, feedback gate TG2 from `A2 = ¬Y`, forward inverter `Y = ¬X`); a
two-inverter delay `B1, B2` feeds the slave input core `B`; the slave latch stores at `Z` (input gate
TG3 from `B`, feedback gate TG4 from `A4 = ¬Q`, forward inverter `Q = ¬Z`). The master is
transparent while the clock is low, the slave while it is high. The clock and the data pin drive
gates only.

The hold tube is time-independent: the rails, `CKB` high, and the slave holding its bit. The
timing conditions N1–N7 (`TGFFTiming`) are the plan's §8 (docs/SPIKE-FLIPFLOP.md).
-/

namespace AsmPhys

open Set

namespace TGFF

/-- Ground pin. -/
def gnd : Fin 4 := 0
/-- Supply pin. -/
def vdd : Fin 4 := 1
/-- Clock pin. -/
def clk : Fin 4 := 2
/-- Data pin. -/
def d : Fin 4 := 3

/-- Inverted clock. -/
def CKB : Fin 11 := 0
/-- Master input core (`¬D`). -/
def A1 : Fin 11 := 1
/-- Master storage node. -/
def X : Fin 11 := 2
/-- Master forward inverter output. -/
def Y : Fin 11 := 3
/-- Master feedback core. -/
def A2 : Fin 11 := 4
/-- First delay stage. -/
def B1 : Fin 11 := 5
/-- Second delay stage. -/
def B2 : Fin 11 := 6
/-- Slave input core. -/
def B : Fin 11 := 7
/-- Slave storage node. -/
def Z : Fin 11 := 8
/-- Output. -/
def Q : Fin 11 := 9
/-- Slave feedback core. -/
def A4 : Fin 11 := 10

/-- Polarity of each transistor. -/
def pol : Fin 26 → Polarity :=
  ![.n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p, .n, .p,
    .n, .p]

/-- Gate of each transistor. -/
def gate : Fin 26 → Node 11 4 :=
  ![.bdry clk, .bdry clk, .bdry d, .bdry d, .state CKB, .bdry clk, .state X, .state X, .state Y,
    .state Y, .bdry clk, .state CKB, .state Y, .state Y, .state B1, .state B1, .state B2,
    .state B2, .bdry clk, .state CKB, .state Z, .state Z, .state Q, .state Q, .state CKB,
    .bdry clk]

/-- Drain of each transistor. -/
def drain : Fin 26 → Node 11 4 :=
  ![.state CKB, .state CKB, .state A1, .state A1, .state A1, .state A1, .state Y, .state Y,
    .state A2, .state A2, .state A2, .state A2, .state B1, .state B1, .state B2, .state B2,
    .state B, .state B, .state B, .state B, .state Q, .state Q, .state A4, .state A4, .state A4,
    .state A4]

/-- Source of each transistor. -/
def source : Fin 26 → Node 11 4 :=
  ![.bdry gnd, .bdry vdd, .bdry gnd, .bdry vdd, .state X, .state X, .bdry gnd, .bdry vdd,
    .bdry gnd, .bdry vdd, .state X, .state X, .bdry gnd, .bdry vdd, .bdry gnd, .bdry vdd,
    .bdry gnd, .bdry vdd, .state Z, .state Z, .bdry gnd, .bdry vdd, .bdry gnd, .bdry vdd,
    .state Z, .state Z]

end TGFF

/-- The flip-flop netlist, with device functions `dev`, capacitance laws `C`, and each transistor
carrying the sheet's parameters for its polarity. -/
noncomputable def tgff (S : Params) (dev : Fin 26 → ℝ → ℝ → ℝ → ℝ) (C : Fin 11 → ℝ → ℝ)
    (hC : ∀ k v, 0 < C k v) : Netlist 11 4 where
  nf := 26
  fet i := ⟨TGFF.pol i, S.par (TGFF.pol i), dev i, TGFF.gate i, TGFF.drain i, TGFF.source i⟩
  C := C
  C_pos := hC

/-- The flip-flop's hold tube: every node on the rail `[0, V_DD^max]`, `CKB` high, and the slave
holding `b` at `Q`. It depends neither on the clock waveform nor on time. -/
def tgffHold (S : Params) : (ℝ → ℝ) → Bool → ℝ → Set (Fin 11 → ℝ) := fun _ b _ =>
  {e | (∀ k, e k ∈ Icc 0 S.VDDmax) ∧ S.VOH ≤ e TGFF.CKB ∧ latchHold S b TGFF.Z TGFF.Q TGFF.A4 e}

namespace Params

/-- Settling time of the master latch: its (A1, X) pair, then `Y`, then `A2`. -/
noncomputable def σm (S : Params) (Cmax : Fin 11 → ℝ) : ℝ :=
  S.PhiTG (Cmax TGFF.A1) (Cmax TGFF.X) + S.tpdINV (Cmax TGFF.Y) + S.tpdINV (Cmax TGFF.A2)

/-- Settling time of the slave latch: its (B, Z) pair, then `Q`, then `A4`. -/
noncomputable def σs (S : Params) (Cmax : Fin 11 → ℝ) : ℝ :=
  S.PhiTG (Cmax TGFF.B) (Cmax TGFF.Z) + S.tpdINV (Cmax TGFF.Q) + S.tpdINV (Cmax TGFF.A4)

end Params

/-- The flip-flop's timing conditions N1–N7 (MODEL: part of H_cells' timing; N5 also constrains the
capacitance design). -/
structure TGFFTiming (S : Params) (Cmin Cmax : Fin 11 → ℝ) : Prop where
  /-- N1: the hold time covers the rise and the clock inverter. -/
  N1 : S.tslew + S.tpdINV (Cmax TGFF.CKB) ≤ S.th
  /-- N2: the setup time covers the master's settling. -/
  N2 : S.σm Cmax ≤ S.tsu
  /-- N3: the master, the chain and the slave settle before the fall. -/
  N3 : S.σm Cmax + S.tpdINV (Cmax TGFF.B1) + S.tpdINV (Cmax TGFF.B2) + S.σs Cmax ≤
    S.tsu + S.tslew + S.thigh
  /-- N4: the slave settles within the high phase. -/
  N4 : S.tpdINV (Cmax TGFF.CKB) + S.σs Cmax ≤ S.thigh
  /-- N5 (race): the chain's contamination outlasts the fall and the clock inverter. -/
  N5 : S.tslew + S.tpdINV (Cmax TGFF.CKB) ≤
    S.tcdINV (Cmin TGFF.Y) + S.tcdINV (Cmin TGFF.B1) + S.tcdINV (Cmin TGFF.B2)
  /-- N6: `t_cq^max` reaches past the fall and the clock inverter. -/
  N6 : 2 * S.tslew + S.thigh + S.tpdINV (Cmax TGFF.CKB) ≤ S.tcqmax
  /-- N7: no minimum clock-to-Q delay is claimed. -/
  N7 : S.tcqmin = 0

end AsmPhys
