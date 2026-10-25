import AsmPhys.Cells.InverterCore

/-!
# Transmission gates

A transmission gate is an n-FET and a p-FET in parallel between two state nodes `x` and `y`, in
either drain/source orientation, with gates `gn` and `gp`. `J` is the current it carries from `y`
into `x`. By passivity it flows from the higher node to the lower. It is off when its n-gate is
valid-low and its p-gate valid-high (K1, K4), and it conducts when one of its FETs is on: the n-FET
when its gate is valid-high and the lower terminal is at most `V_OL`, the p-FET when its gate is
valid-low and the upper terminal is at least `V_OH` (K10). Between two mid-band nodes nothing is
guaranteed.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- A transmission gate between state nodes `x` and `y`: n-FET `jN` gated by `gn`, p-FET `jP` gated
by `gp`, each with its channel between `x` and `y`. -/
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

namespace Netlist.IsTG

variable {N : Netlist n m} {x y : Fin n} {gn gp : Node n m} {jN jP : Fin N.nf}

section Chan

/-! ### A transistor whose channel joins `x` and `y` -/

variable {j : Fin N.nf} {u : Fin m → ℝ} {e : Fin n → ℝ}

/-- The terminals of a channel joining `x` and `y` sit at `e x` and `e y`. -/
theorem pot_chan
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    (pot u e (N.fet j).d = e y ∧ pot u e (N.fet j).s = e x) ∨
      (pot u e (N.fet j).d = e x ∧ pot u e (N.fet j).s = e y) := by
  rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> simp [hd, hs]

/-- With `x` and `y` on a rail, so are the terminals of a channel joining them. -/
theorem pot_chan_mem {V : ℝ}
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y))
    (hx : e x ∈ Icc 0 V) (hy : e y ∈ Icc 0 V) :
    pot u e (N.fet j).d ∈ Icc 0 V ∧ pot u e (N.fet j).s ∈ Icc 0 V := by
  rcases pot_chan (u := u) hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> rw [hd, hs]
  exacts [⟨hy, hx⟩, ⟨hx, hy⟩]

/-- The lower terminal of a channel joining `x` and `y` is `min (e x) (e y)`. -/
theorem min_pot_chan
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    min (pot u e (N.fet j).d) (pot u e (N.fet j).s) = min (e x) (e y) := by
  rcases pot_chan (u := u) (e := e) hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> rw [hd, hs]
  exact min_comm _ _

/-- The upper terminal of a channel joining `x` and `y` is `max (e x) (e y)`. -/
theorem max_pot_chan
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    max (pot u e (N.fet j).d) (pot u e (N.fet j).s) = max (e x) (e y) := by
  rcases pot_chan (u := u) (e := e) hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> rw [hd, hs]
  exact max_comm _ _

/-- The voltage across a channel joining `x` and `y` is `|e x − e y|`. -/
theorem abs_sub_pot_chan
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    |pot u e (N.fet j).d - pot u e (N.fet j).s| = |e x - e y| := by
  rcases pot_chan (u := u) (e := e) hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> rw [hd, hs]
  exact abs_sub_comm _ _

/-- What a channel joining distinct `x` and `y` carries into `x` it takes from `y`. -/
theorem inflow_y_of_chan (hxy : x ≠ y)
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    N.inflow u e y j = -N.inflow u e x j := by
  rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> simp [inflow, hd, hs, hxy, hxy.symm]

/-- A channel joining distinct `x` and `y` carries its whole current into `x`, with a sign. -/
theorem abs_inflow_of_chan (hxy : x ≠ y)
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) :
    |N.inflow u e x j| = |(N.fet j).current u e| := by
  rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩ <;> simp [inflow, hd, hs, hxy.symm]

/-- Passivity (C1): a channel joining distinct `x` and `y` carries current into `x` only from a
higher `y`. -/
theorem mul_inflow_nonneg_of_chan (hxy : x ≠ y)
    (hc : ((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
      ((N.fet j).d = .state x ∧ (N.fet j).s = .state y))
    (hP : Passive (N.fet j).I) : 0 ≤ (e y - e x) * N.inflow u e x j := by
  rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · simpa [inflow, FET.current, hd, hs, hxy, hxy.symm] using hP (pot u e (N.fet j).g) (e y) (e x)
  · have := hP (pot u e (N.fet j).g) (e x) (e y)
    simp only [inflow, FET.current, hd, hs, pot_state, Node.state.injEq, hxy.symm, ite_false,
      ite_true, zero_sub]
    linarith

end Chan

/-- Two currents of the sign of a nonzero `c` add up in absolute value. -/
private theorem abs_le_abs_add_of_mul_nonneg {a b c : ℝ} (hc : c ≠ 0) (ha : 0 ≤ c * a)
    (hb : 0 ≤ c * b) : |a| ≤ |a + b| := by
  rcases hc.lt_or_gt with hc | hc
  · have ha' := nonpos_of_mul_nonneg_right ha hc
    have hb' := nonpos_of_mul_nonneg_right hb hc
    rw [abs_of_nonpos ha', abs_of_nonpos (add_nonpos ha' hb')]
    linarith
  · have ha' := nonneg_of_mul_nonneg_right ha hc
    have hb' := nonneg_of_mul_nonneg_right hb hc
    rw [abs_of_nonneg ha', abs_of_nonneg (add_nonneg ha' hb')]
    linarith

/-- Current through the gate from `y` into `x`. -/
def J (_h : N.IsTG x y gn gp jN jP) (u : Fin m → ℝ) (e : Fin n → ℝ) : ℝ :=
  N.inflow u e x jN + N.inflow u e x jP

/-- What enters `x` leaves `y`. -/
theorem inflow_y (h : N.IsTG x y gn gp jN jP) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    N.inflow u e y jN + N.inflow u e y jP = -h.J u e := by
  rw [inflow_y_of_chan h.xy h.chan_n, inflow_y_of_chan h.xy h.chan_p, J, neg_add]

/-- Passivity: the gate's current flows from the higher node to the lower (C1). -/
theorem J_mul_nonneg (h : N.IsTG x y gn gp jN jP)
    (hpn : Passive (N.fet jN).I) (hpp : Passive (N.fet jP).I)        -- MODEL (C1)
    (u : Fin m → ℝ) (e : Fin n → ℝ) : 0 ≤ (e y - e x) * h.J u e := by
  rw [J, mul_add]
  exact add_nonneg (mul_inflow_nonneg_of_chan h.xy h.chan_n hpn)
    (mul_inflow_nonneg_of_chan h.xy h.chan_p hpp)

/-- An off gate (n-gate valid-low, p-gate valid-high) carries at most `I_off^n + I_off^p`
(K1, K4, C3). -/
theorem abs_J_le_Ioff {S : Params} (hS : S.Consistent) (h : N.IsTG x y gn gp jN jP)
    (hcn : FETContract .n S.pn S.VDDmax (N.fet jN).I)                -- MODEL/MEAS (C1–C6)
    (hcp : FETContract .p S.pp S.VDDmax (N.fet jP).I)                -- MODEL/MEAS (C1–C6)
    {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgn : pot u e gn ≤ S.VIL) (hgp : S.VIH ≤ pot u e gp)
    (hx : e x ∈ Icc 0 S.VDDmax) (hy : e y ∈ Icc 0 S.VDDmax) :
    |h.J u e| ≤ S.pn.Ioff + S.pp.Ioff := by
  obtain ⟨hdn, hsn⟩ := pot_chan_mem (u := u) h.chan_n hx hy
  obtain ⟨hdp, hsp⟩ := pot_chan_mem (u := u) h.chan_p hx hy
  -- n drive `g − min(d, s) ≤ V_IL − 0 ≤ V_off^n` (K1)
  have hn : |(N.fet jN).current u e| ≤ S.pn.Ioff := by
    refine hcn.off_leak _ _ _ hdn hsn ?_
    simp only [offCond, gateDrive]
    rw [h.gate_n]
    linarith [le_min hdn.1 hsn.1, hS.K1]
  -- p drive `max(d, s) − g ≤ V_DD^max − V_IH ≤ V_off^p` (K4)
  have hp : |(N.fet jP).current u e| ≤ S.pp.Ioff := by
    refine hcp.off_leak _ _ _ hdp hsp ?_
    simp only [offCond, gateDrive]
    rw [h.gate_p]
    linarith [max_le hdp.2 hsp.2, hS.K4]
  calc |h.J u e| ≤ |N.inflow u e x jN| + |N.inflow u e x jP| := abs_add_le _ _
    _ ≤ S.pn.Ioff + S.pp.Ioff := by
      rw [abs_inflow_of_chan h.xy h.chan_n, abs_inflow_of_chan h.xy h.chan_p]
      exact add_le_add hn hp

/-- With its n-gate valid-high and its lower terminal at most `V_OL`, the gate conducts at least
`min(G_on^n·|Δv|, I_sat^n)` (K10, C4). -/
theorem J_ge_of_n_on {S : Params} (hS : S.Consistent) (h : N.IsTG x y gn gp jN jP)
    (hcn : FETContract .n S.pn S.VDDmax (N.fet jN).I)                -- MODEL/MEAS (C1–C6)
    (hcp : FETContract .p S.pp S.VDDmax (N.fet jP).I)                -- MODEL/MEAS (C1–C6)
    {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgn : S.VIH ≤ pot u e gn) (hlo : min (e x) (e y) ≤ S.VOL)
    (hx : e x ∈ Icc 0 S.VDDmax) (hy : e y ∈ Icc 0 S.VDDmax) :
    min (S.pn.Gon * |e x - e y|) S.pn.Isat ≤ |h.J u e| := by
  obtain ⟨hdn, hsn⟩ := pot_chan_mem (u := u) h.chan_n hx hy
  -- n drive `g − min(d, s) ≥ V_IH − V_OL ≥ V_on^n` (K10)
  have hon := hcn.on_drive (pot u e (N.fet jN).g) _ _ hdn hsn (by
    simp only [onCond, gateDrive]
    rw [h.gate_n, min_pot_chan h.chan_n]
    linarith [hS.K10.1])
  rw [abs_sub_pot_chan h.chan_n] at hon
  rcases eq_or_ne (e y - e x) 0 with h0 | h0
  · rw [abs_sub_comm, h0, abs_zero, mul_zero]
    exact (min_le_left _ _).trans (abs_nonneg _)
  · refine hon.trans ((abs_inflow_of_chan h.xy h.chan_n).symm.trans_le ?_)
    exact abs_le_abs_add_of_mul_nonneg h0 (mul_inflow_nonneg_of_chan h.xy h.chan_n hcn.passive)
      (mul_inflow_nonneg_of_chan h.xy h.chan_p hcp.passive)

/-- With its p-gate valid-low and its upper terminal at least `V_OH`, the gate conducts at least
`min(G_on^p·|Δv|, I_sat^p)` (K10, C4). -/
theorem J_ge_of_p_on {S : Params} (hS : S.Consistent) (h : N.IsTG x y gn gp jN jP)
    (hcn : FETContract .n S.pn S.VDDmax (N.fet jN).I)                -- MODEL/MEAS (C1–C6)
    (hcp : FETContract .p S.pp S.VDDmax (N.fet jP).I)                -- MODEL/MEAS (C1–C6)
    {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgp : pot u e gp ≤ S.VIL) (hhi : S.VOH ≤ max (e x) (e y))
    (hx : e x ∈ Icc 0 S.VDDmax) (hy : e y ∈ Icc 0 S.VDDmax) :
    min (S.pp.Gon * |e x - e y|) S.pp.Isat ≤ |h.J u e| := by
  obtain ⟨hdp, hsp⟩ := pot_chan_mem (u := u) h.chan_p hx hy
  -- p drive `max(d, s) − g ≥ V_OH − V_IL ≥ V_on^p` (K10)
  have hon := hcp.on_drive (pot u e (N.fet jP).g) _ _ hdp hsp (by
    simp only [onCond, gateDrive]
    rw [h.gate_p, max_pot_chan h.chan_p]
    linarith [hS.K10.2])
  rw [abs_sub_pot_chan h.chan_p] at hon
  rcases eq_or_ne (e y - e x) 0 with h0 | h0
  · rw [abs_sub_comm, h0, abs_zero, mul_zero]
    exact (min_le_left _ _).trans (abs_nonneg _)
  · refine hon.trans ((abs_inflow_of_chan h.xy h.chan_p).symm.trans_le ?_)
    rw [J, add_comm]
    exact abs_le_abs_add_of_mul_nonneg h0 (mul_inflow_nonneg_of_chan h.xy h.chan_p hcp.passive)
      (mul_inflow_nonneg_of_chan h.xy h.chan_n hcn.passive)

/-- With gates and terminals on the rail, the gate carries at most `I_max^n + I_max^p` (C6). -/
theorem abs_J_le_Imax {S : Params} (h : N.IsTG x y gn gp jN jP)
    (hcn : FETContract .n S.pn S.VDDmax (N.fet jN).I)                -- MODEL/MEAS (C1–C6)
    (hcp : FETContract .p S.pp S.VDDmax (N.fet jP).I)                -- MODEL/MEAS (C1–C6)
    {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgn : pot u e gn ∈ Icc 0 S.VDDmax) (hgp : pot u e gp ∈ Icc 0 S.VDDmax)
    (hx : e x ∈ Icc 0 S.VDDmax) (hy : e y ∈ Icc 0 S.VDDmax) :
    |h.J u e| ≤ S.pn.Imax + S.pp.Imax := by
  obtain ⟨hdn, hsn⟩ := pot_chan_mem (u := u) h.chan_n hx hy
  obtain ⟨hdp, hsp⟩ := pot_chan_mem (u := u) h.chan_p hx hy
  have hn : |(N.fet jN).current u e| ≤ S.pn.Imax :=
    hcn.bounded _ _ _ (by rw [h.gate_n]; exact hgn) hdn hsn
  have hp : |(N.fet jP).current u e| ≤ S.pp.Imax :=
    hcp.bounded _ _ _ (by rw [h.gate_p]; exact hgp) hdp hsp
  calc |h.J u e| ≤ |N.inflow u e x jN| + |N.inflow u e x jP| := abs_add_le _ _
    _ ≤ S.pn.Imax + S.pp.Imax := by
      rw [abs_inflow_of_chan h.xy h.chan_n, abs_inflow_of_chan h.xy h.chan_p]
      exact add_le_add hn hp

end Netlist.IsTG

end AsmPhys
