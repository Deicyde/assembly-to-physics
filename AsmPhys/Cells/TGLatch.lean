import AsmPhys.Cells.TransGate
import AsmPhys.Circuit.Tube

/-!
# The transmission-gate latch

A storage node `x` with two transmission gates: an input gate `tg₁` from the input core `a₁`
(driven by `i₁`) and a feedback gate `tg₂` from the feedback core `a₂` (driven by `y`), and a
forward inverter from `x` to `y`. No other channel touches `x`. The flip-flop of
docs/SPIKE-FLIPFLOP.md contains two: the master and the slave.

`latchHold b` says the latch holds `b` at `y`: `x` and `a₂` at the latch level of `¬b` and `y` a
valid output `b`. With the input gate off and no leakage it is invariant: at the face of `x`, the
gates carry current away from it (passivity), and the faces of `a₂` and `y` are strictly inward
(K5, K6). The `x` face is only non-strict, so the proof uses the band maximum principle.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- A transmission-gate latch with storage node `x`, forward inverter `x → y`, input core
`i₁ → a₁` coupled to `x` through `tg₁`, and feedback core `y → a₂` coupled to `x` through `tg₂`. -/
structure Netlist.IsTGLatch (N : Netlist n m) (gnd vdd : Fin m) (i₁ : Node n m)
    (x y a₁ a₂ : Fin n) (g₁n g₁p g₂n g₂p : Node n m)
    (c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp : Fin N.nf) : Prop where
  core₁ : N.IsInvCore i₁ a₁ gnd vdd c₁n c₁p {t₁n, t₁p}
  core₂ : N.IsInvCore (.state y) a₂ gnd vdd c₂n c₂p {t₂n, t₂p}
  tg₁ : N.IsTG x a₁ g₁n g₁p t₁n t₁p
  tg₂ : N.IsTG x a₂ g₂n g₂p t₂n t₂p
  fwd : N.IsInverter (.state x) y gnd vdd yn yp
  only_x : ∀ i, ((N.fet i).d = .state x ∨ (N.fet i).s = .state x) →
    i ∈ ({t₁n, t₁p, t₂n, t₂p} : Finset (Fin N.nf))
  tg_disj : Disjoint ({t₁n, t₁p} : Finset (Fin N.nf)) {t₂n, t₂p}
  distinct : a₁ ≠ a₂ ∧ a₁ ≠ y ∧ a₂ ≠ y ∧ x ≠ y

/-- The latch agrees on `b` everywhere: `a₁`, `x`, `a₂` at the latch level of `¬b`, and `y` a valid
output `b`. -/
def latchAgree (S : Params) (b : Bool) {n : ℕ} (x y a₁ a₂ : Fin n) (e : Fin n → ℝ) : Prop :=
  S.Lvl (!b) (e a₁) ∧ S.Lvl (!b) (e x) ∧ S.Lvl (!b) (e a₂) ∧ S.validOut b (e y)

/-- The latch holds `b` at `y`: `x` and `a₂` at the latch level of `¬b`, and `y` a valid output
`b`. -/
def latchHold (S : Params) (b : Bool) {n : ℕ} (x y a₂ : Fin n) (e : Fin n → ℝ) : Prop :=
  S.Lvl (!b) (e x) ∧ S.Lvl (!b) (e a₂) ∧ S.validOut b (e y)

namespace Netlist.IsTGLatch

/-- A transmission gate between `x` and `y` is one between `y` and `x`. -/
private theorem tg_swap {N : Netlist n m} {x y : Fin n} {gn gp : Node n m} {jN jP : Fin N.nf}
    (h : N.IsTG x y gn gp jN jP) : N.IsTG y x gn gp jN jP where
  ne := h.ne
  xy := h.xy.symm
  pol_n := h.pol_n
  pol_p := h.pol_p
  gate_n := h.gate_n
  gate_p := h.gate_p
  chan_n := h.chan_n.symm
  chan_p := h.chan_p.symm

/-- A channel between distinct nodes `x` and `y` has its far terminal at `y` when seen from `x`. -/
private theorem tg_far {f : FET n m} {x y : Fin n} (hxy : x ≠ y)
    (hc : (f.d = .state y ∧ f.s = .state x) ∨ (f.d = .state x ∧ f.s = .state y))
    (u : Fin m → ℝ) (e : Fin n → ℝ) :
    (f.s = .state x → pot u e f.d = e y) ∧ (f.d = .state x → pot u e f.s = e y) := by
  rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact ⟨fun _ => by rw [hd, pot_state],
      fun h => absurd (Node.state.inj (hd.symm.trans h)) hxy.symm⟩
  · exact ⟨fun h => absurd (Node.state.inj (hs.symm.trans h)) hxy.symm,
      fun _ => by rw [hs, pot_state]⟩

/-- Passivity: with `e y ≤ e x`, a gate between `x` and `y` carries no net current into `x`
(C1, C2). -/
private theorem tg_inflow_nonpos {N : Netlist n m} {x y : Fin n} {gn gp : Node n m}
    {jN jP : Fin N.nf} (h : N.IsTG x y gn gp jN jP)
    (hpn : Passive (N.fet jN).I) (hrn : Regular (N.fet jN).I)
    (hpp : Passive (N.fet jP).I) (hrp : Regular (N.fet jP).I)
    {u : Fin m → ℝ} {e : Fin n → ℝ} (hle : e y ≤ e x) :
    ∑ i ∈ {jN, jP}, N.inflow u e x i ≤ 0 := by
  refine Netlist.sum_inflow_nonpos (fun i hi => ?_) (fun i hi => ?_) <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi <;> rcases hi with rfl | rfl
  · exact ⟨hpn, hrn⟩
  · exact ⟨hpp, hrp⟩
  · obtain ⟨h1, h2⟩ := tg_far h.xy h.chan_n u e
    exact ⟨fun hs => (h1 hs).trans_le hle, fun hd => (h2 hd).trans_le hle⟩
  · obtain ⟨h1, h2⟩ := tg_far h.xy h.chan_p u e
    exact ⟨fun hs => (h1 hs).trans_le hle, fun hd => (h2 hd).trans_le hle⟩

/-- Passivity: with `e x ≤ e y`, a gate between `x` and `y` carries no net current out of `x`
(C1, C2). -/
private theorem tg_inflow_nonneg {N : Netlist n m} {x y : Fin n} {gn gp : Node n m}
    {jN jP : Fin N.nf} (h : N.IsTG x y gn gp jN jP)
    (hpn : Passive (N.fet jN).I) (hrn : Regular (N.fet jN).I)
    (hpp : Passive (N.fet jP).I) (hrp : Regular (N.fet jP).I)
    {u : Fin m → ℝ} {e : Fin n → ℝ} (hle : e x ≤ e y) :
    0 ≤ ∑ i ∈ {jN, jP}, N.inflow u e x i := by
  refine Netlist.sum_inflow_nonneg (fun i hi => ?_) (fun i hi => ?_) <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi <;> rcases hi with rfl | rfl
  · exact ⟨hpn, hrn⟩
  · exact ⟨hpp, hrp⟩
  · obtain ⟨h1, h2⟩ := tg_far h.xy h.chan_n u e
    exact ⟨fun hs => hle.trans_eq (h1 hs).symm, fun hd => hle.trans_eq (h2 hd).symm⟩
  · obtain ⟨h1, h2⟩ := tg_far h.xy h.chan_p u e
    exact ⟨fun hs => hle.trans_eq (h1 hs).symm, fun hd => hle.trans_eq (h2 hd).symm⟩

/-- A contract on `T` gives each n-FET in `T` the n-FET contract. -/
private theorem contract_n {N : Netlist n m} {S : Params} {T : Finset (Fin N.nf)}
    (hc : N.ContractOn S T) {i : Fin N.nf} (hi : i ∈ T) (hpol : (N.fet i).pol = .n) :
    FETContract .n S.pn S.VDDmax (N.fet i).I := by
  have h := hc i hi
  rw [hpol] at h
  exact h

/-- A contract on `T` gives each p-FET in `T` the p-FET contract. -/
private theorem contract_p {N : Netlist n m} {S : Params} {T : Finset (Fin N.nf)}
    (hc : N.ContractOn S T) {i : Fin N.nf} (hi : i ∈ T) (hpol : (N.fet i).pol = .p) :
    FETContract .p S.pp S.VDDmax (N.fet i).I := by
  have h := hc i hi
  rw [hpol] at h
  exact h

/-- `max_principle_band` for three components. -/
private theorem band₃ {f g h f' g' h' : ℝ → ℝ} {a b V δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hh : ContinuousOn h (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hh' : ∀ t ∈ Ico a b, HasDerivWithinAt h (h' t) (Ici t) t)
    (ha : f a ≤ V ∧ g a ≤ V ∧ h a ≤ V)
    (hff : ∀ t ∈ Ico a b, f t ∈ Icc V (V + δ) → g t ≤ f t → h t ≤ f t → f' t ≤ 0)
    (hgf : ∀ t ∈ Ico a b, g t ∈ Icc V (V + δ) → f t ≤ g t → h t ≤ g t → g' t ≤ 0)
    (hhf : ∀ t ∈ Ico a b, h t ∈ Icc V (V + δ) → f t ≤ h t → g t ≤ h t → h' t ≤ 0) :
    ∀ t ∈ Icc a b, f t ≤ V ∧ g t ≤ V ∧ h t ≤ V := by
  have key := max_principle_band (ι := Fin 3) (x := fun t => ![f t, g t, h t])
    (x' := fun t => ![f' t, g' t, h' t]) (V := V) hδ
    (continuousOn_pi.2 fun k => by fin_cases k <;> simpa)
    (fun t ht => hasDerivWithinAt_pi.2 fun k => by
      fin_cases k
      exacts [hf' t ht, hg' t ht, hh' t ht])
    (fun k => by
      fin_cases k
      exacts [ha.1, ha.2.1, ha.2.2])
    (fun t ht k hk hmax => by
      have h0 := hmax 0
      have h1 := hmax 1
      have h2 := hmax 2
      fin_cases k <;> simp at hk h0 h1 h2 ⊢
      exacts [hff t ht hk h1 h2, hgf t ht hk h0 h2, hhf t ht hk h0 h1])
  exact fun t ht => ⟨key t ht 0, key t ht 1, key t ht 2⟩

variable {N : Netlist n m} {gnd vdd : Fin m} {i₁ : Node n m} {x y a₁ a₂ : Fin n}
  {g₁n g₁p g₂n g₂p : Node n m} {c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp : Fin N.nf}

/-- **Latch hold.** Without leakage, a latch whose input gate is off keeps holding its bit: its
feedback loop through `tg₂` is invariant whatever the input core and the clock levels of `tg₂` do.
-/
theorem hold_invariant {S : Params} (hS : S.Consistent)              -- THM (norm_num)
    (hL : N.IsTGLatch gnd vdd i₁ x y a₁ a₂ g₁n g₁p g₂n g₂p
      c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp)
    (hc : N.ContractOn S {c₁n, c₁p, c₂n, c₂p, t₁n, t₁p, t₂n, t₂p, yn, yp})  -- MODEL/MEAS
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (hrail : ∀ t ∈ Icc t₀ t₁, ∀ k ∈ ({x, y, a₁, a₂} : Finset (Fin n)),
      e t k ∈ Icc 0 S.VDDmax)
    (hoff : ∀ t ∈ Icc t₀ t₁, pot (u t) (e t) g₁n ≤ S.VIL ∧ S.VIH ≤ pot (u t) (e t) g₁p)
    {b : Bool} (h0 : latchHold S b x y a₂ (e t₀)) :
    ∀ t ∈ Icc t₀ t₁, latchHold S b x y a₂ (e t) := by
  obtain ⟨hδ, hVOLθ, hθVIL, hVIHθ, hθVOH⟩ := hS.band
  obtain ⟨-, hK0b, hK0c, hK0d, hK0e⟩ := hS.K0
  have hc₂n := contract_n hc (by simp) hL.core₂.pol_n
  have hc₂p := contract_p hc (by simp) hL.core₂.pol_p
  have ht₁n := contract_n hc (by simp) hL.tg₁.pol_n
  have ht₁p := contract_p hc (by simp) hL.tg₁.pol_p
  have ht₂n := contract_n hc (by simp) hL.tg₂.pol_n
  have ht₂p := contract_p hc (by simp) hL.tg₂.pol_p
  have hyn := contract_n hc (by simp) hL.fwd.pol_n
  have hyp := contract_p hc (by simp) hL.fwd.pol_p
  have hx : ∀ t ∈ Icc t₀ t₁, e t x ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht x (by simp)
  have hy : ∀ t ∈ Icc t₀ t₁, e t y ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht y (by simp)
  have ha₁ : ∀ t ∈ Icc t₀ t₁, e t a₁ ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht a₁ (by simp)
  have ha₂ : ∀ t ∈ Icc t₀ t₁, e t a₂ ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht a₂ (by simp)
  have hcont : ∀ k, ContinuousOn (fun t => e t k) (Icc t₀ t₁) :=
    fun k => continuousOn_pi.1 he.continuousOn k
  have hd : ∀ k, ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun t => e t k) (N.vf (u t) (e t) k) (Ici t) t :=
    fun k t ht => hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) k
  have hvf_nonpos : ∀ t k, N.F (u t) (e t) k ≤ 0 → N.vf (u t) (e t) k ≤ 0 :=
    fun t k hF => div_nonpos_of_nonpos_of_nonneg hF (N.C_pos k _).le
  have hvf_nonneg : ∀ t k, 0 ≤ N.F (u t) (e t) k → 0 ≤ N.vf (u t) (e t) k :=
    fun t k hF => div_nonneg hF (N.C_pos k _).le
  -- The input gate is off and leaks nothing, so only the feedback gate drives `x`.
  have hFx : ∀ t ∈ Icc t₀ t₁,
      N.F (u t) (e t) x = ∑ i ∈ {t₂n, t₂p}, N.inflow (u t) (e t) x i := by
    intro t ht
    have hJ := hL.tg₁.abs_J_le_Ioff hS ht₁n ht₁p (hoff t ht).1 (hoff t ht).2 (hx t ht) (ha₁ t ht)
    rw [hI.1, hI.2, add_zero, abs_nonpos_iff, IsTG.J] at hJ
    have hT : ({t₁n, t₁p, t₂n, t₂p} : Finset (Fin N.nf)) = {t₁n, t₁p} ∪ {t₂n, t₂p} := by
      ext i
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    rw [Netlist.F_eq_sum_inflow hL.only_x, hT, Finset.sum_union hL.tg_disj,
      Finset.sum_pair hL.tg₁.ne, hJ, zero_add]
  cases b
  · -- `b = false`: `x` and `a₂` high, `y` low; the components are `−e x`, `−e a₂` and
    -- `−θ_H + (e y − V_OL)`, all at most `−θ_H`.
    have h0x : S.θH ≤ e t₀ x := h0.1
    have h0a : S.θH ≤ e t₀ a₂ := h0.2.1
    have h0y : e t₀ y ≤ S.VOL := h0.2.2
    have key := band₃ (f := fun t => -e t x) (g := fun t => -e t a₂)
      (h := fun t => -S.θH + (e t y - S.VOL)) (f' := fun t => -N.vf (u t) (e t) x)
      (g' := fun t => -N.vf (u t) (e t) a₂) (h' := fun t => N.vf (u t) (e t) y)
      (V := -S.θH) hδ (hcont x).neg (hcont a₂).neg
      (continuousOn_const.add ((hcont y).sub continuousOn_const))
      (fun t ht => (hd x t ht).neg) (fun t ht => (hd a₂ t ht).neg)
      (fun t ht => ((hd y t ht).sub_const S.VOL).const_add (-S.θH))
      ⟨by linarith, by linarith, by linarith⟩ ?_ ?_ ?_
    · intro t ht
      have := key t ht
      beta_reduce at this
      show S.θH ≤ e t x ∧ S.θH ≤ e t a₂ ∧ e t y ≤ S.VOL
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2]⟩
    · -- Face `x`: `e x ≤ e a₂`, so the feedback gate carries no current out of `x`.
      intro t ht _ h1 _
      rw [neg_nonpos]
      refine hvf_nonneg t x ?_
      rw [hFx t (Ico_subset_Icc_self ht)]
      exact tg_inflow_nonneg hL.tg₂ ht₂n.passive ht₂n.regular ht₂p.passive ht₂p.regular
        (by linarith)
    · -- Face `a₂`: `y` is valid low and `e a₂ ≤ e x`, so `a₂` rises (K5).
      intro t ht hk h1 h2
      beta_reduce at hk h1 h2 ⊢
      have ht' := Ico_subset_Icc_self ht
      rw [neg_nonpos]
      refine hvf_nonneg t a₂ ?_
      have hcore := hL.core₂.Irise_le_core hS hc₂n hc₂p hVDD (hgnd t ht') (hvdd t ht')
        (show e t y ≤ S.VIL by linarith [hk.2]) ⟨(ha₂ t ht').1, by linarith [hk.1]⟩
      have hside := tg_inflow_nonneg (tg_swap hL.tg₂) ht₂n.passive ht₂n.regular ht₂p.passive
        ht₂p.regular (u := u t) (e := e t) (by linarith)
      rw [hL.core₂.F_out]
      have := hS.K5
      unfold Params.Irise at hcore
      linarith
    · -- Face `y`: `x` is valid high, so `y` falls (K6).
      intro t ht hk h1 _
      beta_reduce at hk h1 ⊢
      have ht' := Ico_subset_Icc_self ht
      refine hvf_nonpos t y ?_
      have hF := hL.fwd.F_out_le_neg_Ifall hS hyn hyp hVDD (hgnd t ht') (hvdd t ht')
        (show S.VIH ≤ e t x by linarith [hk.2]) ⟨by linarith [hk.1], by linarith [hk.2, hVDD.1]⟩
      have := hS.K6
      unfold Params.Ifall at hF
      linarith
  · -- `b = true`: `x` and `a₂` low, `y` high; the components are `e x`, `e a₂` and
    -- `θ_L + (V_OH − e y)`, all at most `θ_L`.
    have h0x : e t₀ x ≤ S.θL := h0.1
    have h0a : e t₀ a₂ ≤ S.θL := h0.2.1
    have h0y : S.VOH ≤ e t₀ y := h0.2.2
    have key := band₃ (f := fun t => e t x) (g := fun t => e t a₂)
      (h := fun t => S.θL + (S.VOH - e t y)) (f' := fun t => N.vf (u t) (e t) x)
      (g' := fun t => N.vf (u t) (e t) a₂) (h' := fun t => -N.vf (u t) (e t) y)
      (V := S.θL) hδ (hcont x) (hcont a₂)
      (continuousOn_const.add (continuousOn_const.sub (hcont y)))
      (hd x) (hd a₂) (fun t ht => ((hd y t ht).const_sub S.VOH).const_add S.θL)
      ⟨h0x, h0a, by linarith⟩ ?_ ?_ ?_
    · intro t ht
      have := key t ht
      beta_reduce at this
      show e t x ≤ S.θL ∧ e t a₂ ≤ S.θL ∧ S.VOH ≤ e t y
      exact ⟨this.1, this.2.1, by linarith [this.2.2]⟩
    · -- Face `x`: `e a₂ ≤ e x`, so the feedback gate carries no current into `x`.
      intro t ht _ h1 _
      refine hvf_nonpos t x ?_
      rw [hFx t (Ico_subset_Icc_self ht)]
      exact tg_inflow_nonpos hL.tg₂ ht₂n.passive ht₂n.regular ht₂p.passive ht₂p.regular h1
    · -- Face `a₂`: `y` is valid high and `e x ≤ e a₂`, so `a₂` falls (K6).
      intro t ht hk h1 h2
      beta_reduce at hk h1 h2 ⊢
      have ht' := Ico_subset_Icc_self ht
      refine hvf_nonpos t a₂ ?_
      have hcore := hL.core₂.core_le_neg_Ifall hS hc₂n hc₂p hVDD (hgnd t ht') (hvdd t ht')
        (show S.VIH ≤ e t y by linarith [hk.2]) ⟨by linarith [hk.1], (ha₂ t ht').2⟩
      have hside := tg_inflow_nonpos (tg_swap hL.tg₂) ht₂n.passive ht₂n.regular ht₂p.passive
        ht₂p.regular (u := u t) (e := e t) h1
      rw [hL.core₂.F_out]
      have := hS.K6
      unfold Params.Ifall at hcore
      linarith
    · -- Face `y`: `x` is valid low, so `y` rises (K5).
      intro t ht hk h1 _
      beta_reduce at hk h1 ⊢
      have ht' := Ico_subset_Icc_self ht
      rw [neg_nonpos]
      refine hvf_nonneg t y ?_
      have hF := hL.fwd.Irise_le_F_out hS hyn hyp hVDD (hgnd t ht') (hvdd t ht')
        (show e t x ≤ S.VIL by linarith [hk.2]) ⟨(hy t ht').1, by linarith [hk.1]⟩
      have := hS.K5
      unfold Params.Irise at hF
      linarith

end Netlist.IsTGLatch

end AsmPhys
