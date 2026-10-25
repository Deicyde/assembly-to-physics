import AsmPhys.Cells.Levels
import AsmPhys.Circuit.Rails

/-!
# THM L3.1 and THM L3.2 for the inverter

An inverter instance is an n-FET from the output to ground and a p-FET from the output to the
supply, both gated by the input node, with no other channel at the output (static CMOS: the
fanout touches the output only through gates, and its gate charge is in the output's capacitance
law). The theorems hold for every pair of devices that meets the FET contracts with the sheet's
parameters, and for every output capacitance law in the stated range.

With a valid-low input the n-FET is off (K1) and the p-FET on (K2); while `e_out ≤ V_OH`,
`C_out(e_out) · ė_out ≥ I_rise > 0` (K5). With a valid-high input the p-FET is off (K4) and the
n-FET on (K3); while `e_out ≥ V_OL`, `C_out(e_out) · ė_out ≤ −I_fall < 0` (K6).
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

namespace Netlist.IsInverter

variable {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m} {iN iP : Fin N.nf}

/-- The net channel current into an inverter's output is minus the two channel currents. -/
theorem F_out (hinv : N.IsInverter inp out gnd vdd iN iP) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    N.F u e out = -(N.fet iN).current u e - (N.fet iP).current u e := by
  unfold Netlist.F
  rw [Finset.sum_eq_add iN iP hinv.ne (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)]
  · simp [hinv.drain_n, hinv.source_n, hinv.drain_p, hinv.source_p]
    ring
  · obtain ⟨hd, hs⟩ := hinv.only i hi.1 hi.2
    simp [hd, hs]

/-- The only devices with a channel terminal at an inverter's output are `iN` and `iP`. -/
theorem eq_of_touch (hinv : N.IsInverter inp out gnd vdd iN iP) {i : Fin N.nf}
    (hi : (N.fet i).d = .state out ∨ (N.fet i).s = .state out) : i = iN ∨ i = iP := by
  by_contra h
  obtain ⟨hd, hs⟩ := hinv.only i (fun h' => h (.inl h')) (fun h' => h (.inr h'))
  exact hi.elim hd hs

/-- The n-FET's channel current at node potentials `(u, e)`. -/
theorem current_n (hinv : N.IsInverter inp out gnd vdd iN iP) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    (N.fet iN).current u e = (N.fet iN).I (pot u e inp) (e out) (u gnd) := by
  rw [FET.current, hinv.gate_n, hinv.drain_n, hinv.source_n, pot_state, pot_bdry]

/-- The p-FET's channel current at node potentials `(u, e)`. -/
theorem current_p (hinv : N.IsInverter inp out gnd vdd iN iP) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    (N.fet iP).current u e = (N.fet iP).I (pot u e inp) (e out) (u vdd) := by
  rw [FET.current, hinv.gate_p, hinv.drain_p, hinv.source_p, pot_state, pot_bdry]

/-- The inverter's output stays in `[0, V_DD]` whatever its input does: at `V_DD` both channel
currents flow out of it and at `0` both flow in (C1 and `I(v_g, v, v) = 0`). -/
theorem out_mem_rails (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hpn : Passive (N.fet iN).I) (hrn : Regular (N.fet iN).I)         -- MODEL (C1, C2)
    (hpp : Passive (N.fet iP).I) (hrp : Regular (N.fet iP).I)         -- MODEL (C1, C2)
    {VDD : ℝ} (hVDD : 0 ≤ VDD)                                       -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (h0 : e t₀ out ∈ Icc 0 VDD) :
    ∀ t ∈ Icc t₀ t₁, e t out ∈ Icc 0 VDD := by
  refine N.rail_invariance_node (k := out) (fun i hi => ?_) (fun i hi => ?_) he
    (fun t ht i => ⟨fun hd => .inr ?_, fun hs => ?_⟩) h0
  · rcases hinv.eq_of_touch hi with rfl | rfl
    exacts [hpn, hpp]
  · rcases hinv.eq_of_touch hi with rfl | rfl
    exacts [hrn, hrp]
  · rcases hinv.eq_of_touch (.inl hd) with rfl | rfl
    · rw [hinv.source_n, pot_bdry, hgnd t ht]
      exact ⟨le_rfl, hVDD⟩
    · rw [hinv.source_p, pot_bdry, hvdd t ht]
      exact ⟨hVDD, le_rfl⟩
  · rcases hinv.eq_of_touch (.inr hs) with rfl | rfl
    · nomatch hinv.source_n.symm.trans hs
    · nomatch hinv.source_p.symm.trans hs

/-- Rising output (THM, from C1, C3, C4, K0–K2, K5 and K13): with ground at `0`, the supply in
`[V_DD^min, V_DD^max]`, a valid-low input and the output in `[0, V_OH]`, the n-FET is off, the
p-FET is on, and the net current into the output is at least `I_rise`. -/
theorem Irise_le_F_out {S : Params} (hS : S.Consistent)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn false (pot u e inp))
    (hout : e out ∈ Icc 0 S.VOH) :
    S.Irise ≤ N.F u e out := by
  obtain ⟨-, -, -, -, hK0⟩ := hS.K0
  have hin : pot u e inp ≤ S.VIL := hin
  have hVDD0 : 0 ≤ VDD := by linarith [hVDD.1, hout.1, hout.2]
  have hd : e out ∈ Icc 0 S.VDDmax := ⟨hout.1, by linarith [hout.2, hVDD.1, hVDD.2]⟩
  have hoff : offCond .n S.pn (pot u e inp) (e out) 0 := by
    show pot u e inp - min (e out) 0 ≤ S.pn.Voff
    rw [min_eq_right hout.1, sub_zero]
    exact hin.trans hS.K1
  have hon : onCond .p S.pp (pot u e inp) (e out) VDD := by
    show S.pp.Von ≤ max (e out) VDD - pot u e inp
    rw [max_eq_right (by linarith [hout.2, hVDD.1])]
    linarith [hS.K2, hVDD.1]
  have hIn := abs_le.1 (hn.off_leak _ _ _ hd ⟨le_rfl, hVDD0.trans hVDD.2⟩ hoff)
  have hIp := hp.on_drive _ _ _ hd ⟨hVDD0, hVDD.2⟩ hon
  rw [abs_of_nonpos (hp.passive.nonpos_of_le hp.regular (by linarith [hout.2, hVDD.1])),
    abs_sub_comm, abs_of_nonneg (by linarith [hout.2, hVDD.1])] at hIp
  have hGp : 0 ≤ S.pp.Gon := (pos_of_mul_pos_left ((hS.K13_leak.1.trans_lt hS.K5).trans_le
    (min_le_left _ _)) (by linarith)).le
  have hmono : min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat ≤
      min (S.pp.Gon * (VDD - e out)) S.pp.Isat :=
    min_le_min (mul_le_mul_of_nonneg_left (by linarith [hout.2, hVDD.1]) hGp) le_rfl
  rw [hinv.F_out, hinv.current_n, hinv.current_p, hgnd, hvdd]
  unfold Params.Irise
  linarith

/-- Falling output (THM, from C1, C3, C4, K0, K3, K4, K6 and K13): with ground at `0`, the supply
in `[V_DD^min, V_DD^max]`, a valid-high input and the output in `[V_OL, V_DD]`, the p-FET is off,
the n-FET is on, and the net current into the output is at most `−I_fall`. -/
theorem F_out_le_neg_Ifall {S : Params} (hS : S.Consistent)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn true (pot u e inp))
    (hout : e out ∈ Icc S.VOL VDD) :
    N.F u e out ≤ -S.Ifall := by
  obtain ⟨hVOL, -, -, -, -⟩ := hS.K0
  have hin : S.VIH ≤ pot u e inp := hin
  have hVDD0 : 0 ≤ VDD := by linarith [hout.1, hout.2]
  have hd : e out ∈ Icc 0 S.VDDmax := ⟨by linarith [hout.1], hout.2.trans hVDD.2⟩
  have hoff : offCond .p S.pp (pot u e inp) (e out) VDD := by
    show max (e out) VDD - pot u e inp ≤ S.pp.Voff
    rw [max_eq_right hout.2]
    linarith [hS.K4, hVDD.2]
  have hon : onCond .n S.pn (pot u e inp) (e out) 0 := by
    show S.pn.Von ≤ pot u e inp - min (e out) 0
    rw [min_eq_right hd.1, sub_zero]
    exact hS.K3.trans hin
  have hIp := abs_le.1 (hp.off_leak _ _ _ hd ⟨hVDD0, hVDD.2⟩ hoff)
  have hIn := hn.on_drive _ _ _ hd ⟨le_rfl, hVDD0.trans hVDD.2⟩ hon
  rw [abs_of_nonneg (hn.passive.nonneg_of_le hn.regular hd.1), sub_zero,
    abs_of_nonneg hd.1] at hIn
  have hGn : 0 ≤ S.pn.Gon := (pos_of_mul_pos_left ((hS.K13_leak.2.trans_lt hS.K6).trans_le
    (min_le_left _ _)) hVOL.le).le
  have hmono : min (S.pn.Gon * S.VOL) S.pn.Isat ≤ min (S.pn.Gon * e out) S.pn.Isat :=
    min_le_min (mul_le_mul_of_nonneg_left hout.1 hGn) le_rfl
  rw [hinv.F_out, hinv.current_n, hinv.current_p, hgnd, hvdd]
  unfold Params.Ifall
  linarith

/-- **THM L3.1** (propagation) for INV: if the input is `validIn x` on `[t₀, t₁]` and the output
starts in the rails, then (a) the output is `validOut (¬x)` on `[t₀ + t_pd, t₁]`, and (b) once
it is `validOut (¬x)` at some `t₂ ∈ [t₀, t₁]` it stays so on `[t₂, t₁]`. -/
theorem propagation {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
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
        ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hVDD0 : 0 ≤ VDD := by linarith [hVDD.1]
  have hrail := hinv.out_mem_rails hn.passive hn.regular hp.passive hp.regular hVDD0 he hgnd
    hvdd h0
  have hCmax : 0 < Cmax := (N.C_pos out 0).trans_le (hcap 0).2
  have hIrise : 0 < S.Irise := sub_pos.2 hS.K5
  have hIfall : 0 < S.Ifall := sub_pos.2 hS.K6
  have htpd : 0 ≤ S.tpdINV Cmax :=
    mul_nonneg hCmax.le ((div_pos (by linarith) hIrise).le.trans (le_max_left _ _))
  have hg := continuousOn_pi.1 he.continuousOn out
  have hg' : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun t => e t out) (N.vf (u t) (e t) out) (Ici t) t :=
    fun t ht => hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) out
  -- Dividing a net current bound by the capacitance.
  have hdiv : ∀ {X F : ℝ} (v : ℝ), 0 ≤ X → X ≤ F → X / Cmax ≤ F / N.C out v := fun v hX hF =>
    (div_le_div_of_nonneg_left hX (N.C_pos out v) (hcap v).2).trans
      (div_le_div_of_nonneg_right hF (N.C_pos out v).le)
  have hsub : ∀ {t₂ s : ℝ}, t₂ ∈ Icc t₀ t₁ → s ∈ Ico t₂ t₁ → s ∈ Ico t₀ t₁ :=
    fun h2 hs => ⟨h2.1.trans hs.1, hs.2⟩
  cases x with
  | false =>
    have hface : ∀ t ∈ Ico t₀ t₁, e t out ≤ S.VOH →
        S.Irise / Cmax ≤ N.vf (u t) (e t) out := fun t ht hle =>
      have htI := Ico_subset_Icc_self ht
      hdiv _ hIrise.le (hinv.Irise_le_F_out hS hn hp hVDD (hgnd t htI) (hvdd t htI)
        (hin t htI) ⟨(hrail t htI).1, hle⟩)
    refine ⟨fun t ht => ?_, fun t₂ ht₂ h2 t ht => ?_⟩
    · show S.VOH ≤ e t out
      refine reach_of_deriv_right_ge (div_pos hIrise hCmax) hg hg' hface t
        ⟨by linarith [ht.1], ht.2⟩ ?_
      calc S.VOH - e t₀ out ≤ S.Irise / Cmax * (Cmax * (S.VOH / S.Irise)) := by
            rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hCmax.ne',
              mul_div_cancel₀ _ hIrise.ne']
            linarith [h0.1]
        _ ≤ S.Irise / Cmax * (t - t₀) :=
            mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_left _ _)
              hCmax.le).trans (show S.tpdINV Cmax ≤ t - t₀ by linarith [ht.1]))
              (div_pos hIrise hCmax).le
    · exact barrier_of_deriv_right_nonneg (hg.mono (Icc_subset_Icc_left ht₂.1))
        (fun s hs => hg' s (hsub ht₂ hs)) h2
        (fun s hs hle => (div_pos hIrise hCmax).le.trans (hface s (hsub ht₂ hs) hle)) t ht
  | true =>
    have hface : ∀ t ∈ Ico t₀ t₁, -e t out ≤ -S.VOL →
        S.Ifall / Cmax ≤ -N.vf (u t) (e t) out := fun t ht hle => by
      have htI := Ico_subset_Icc_self ht
      have hF := hinv.F_out_le_neg_Ifall hS hn hp hVDD (hgnd t htI) (hvdd t htI) (hin t htI)
        ⟨neg_le_neg_iff.1 hle, (hrail t htI).2⟩
      rw [Netlist.vf, ← neg_div]
      exact hdiv _ hIfall.le (by linarith)
    refine ⟨fun t ht => ?_, fun t₂ ht₂ h2 t ht => ?_⟩
    · show e t out ≤ S.VOL
      refine neg_le_neg_iff.1 (reach_of_deriv_right_ge (div_pos hIfall hCmax) hg.neg
        (fun t ht => (hg' t ht).neg) hface t ⟨by linarith [ht.1], ht.2⟩ ?_)
      calc -S.VOL - -e t₀ out ≤ S.Ifall / Cmax * (Cmax * ((S.VDDmax - S.VOL) / S.Ifall)) := by
            rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hCmax.ne',
              mul_div_cancel₀ _ hIfall.ne']
            linarith [h0.2, hVDD.2]
        _ ≤ S.Ifall / Cmax * (t - t₀) :=
            mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_right _ _)
              hCmax.le).trans (show S.tpdINV Cmax ≤ t - t₀ by linarith [ht.1]))
              (div_pos hIfall hCmax).le
    · have h2 : e t₂ out ≤ S.VOL := h2
      show e t out ≤ S.VOL
      exact neg_le_neg_iff.1 (barrier_of_deriv_right_nonneg
        (hg.neg.mono (Icc_subset_Icc_left ht₂.1)) (fun s hs => (hg' s (hsub ht₂ hs)).neg)
        (neg_le_neg h2)
        (fun s hs hle => (div_pos hIfall hCmax).le.trans (hface s (hsub ht₂ hs) hle)) t ht)

/-- **THM L3.2** (contamination) for INV: if the output is `validOut b` at `t₁` (and in the rails),
then it is `validIn b` on `[t₁, t₁ + t_cd]`, whatever the input does within the rails. -/
theorem contamination {S : Params} (hS : S.Consistent)               -- THM (norm_num)
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
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV Cmin)), S.validIn b (e t out) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hVDD0 : 0 ≤ VDD := by linarith [hVDD.1]
  have hrail' := hinv.out_mem_rails hn.passive hn.regular hp.passive hp.regular hVDD0 he hgnd
    hvdd hrail
  -- `I_max > 0`: the n-FET's on-drive floor at full swing is positive (K6, K13).
  have hK6 := lt_min_iff.1 (hS.K13_leak.2.trans_lt hS.K6)
  have hGn : 0 < S.pn.Gon := pos_of_mul_pos_left hK6.1 hVOL.le
  have hImax : 0 < max S.pn.Imax S.pp.Imax :=
    (lt_min (mul_pos hGn (by linarith [hS.K13_supply])) hK6.2).trans_le
      (hS.K13_drive.1.trans (le_max_left _ _))
  have hslew : ∀ t ∈ Ico t₁ t₂,
      ‖N.vf (u t) (e t) out‖ ≤ 2 * max S.pn.Imax S.pp.Imax / Cmin := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have hd : e t out ∈ Icc 0 S.VDDmax := ⟨(hrail' t htI).1, (hrail' t htI).2.trans hVDD.2⟩
    have hIn : |(N.fet iN).current (u t) (e t)| ≤ S.pn.Imax := by
      rw [hinv.current_n, hgnd t htI]
      exact hn.bounded _ _ _ (hin t htI) hd ⟨le_rfl, hVDD0.trans hVDD.2⟩
    have hIp : |(N.fet iP).current (u t) (e t)| ≤ S.pp.Imax := by
      rw [hinv.current_p, hvdd t htI]
      exact hp.bounded _ _ _ (hin t htI) hd ⟨hVDD0, hVDD.2⟩
    have hF : |N.F (u t) (e t) out| ≤ 2 * max S.pn.Imax S.pp.Imax := by
      rw [hinv.F_out, abs_le]
      have := abs_le.1 hIn
      have := abs_le.1 hIp
      constructor <;> linarith [le_max_left S.pn.Imax S.pp.Imax, le_max_right S.pn.Imax S.pp.Imax]
    rw [Real.norm_eq_abs, Netlist.vf, abs_div, abs_of_pos (N.C_pos out _)]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hCmin (hcap _).1).trans
      (div_le_div_of_nonneg_right hF hCmin.le)
  intro t ht
  have htt : t - t₁ ≤ S.tcdINV Cmin := by linarith [ht.2.trans (min_le_right _ _)]
  have hdist := norm_image_sub_le_of_norm_deriv_right_le_segment
    (continuousOn_pi.1 he.continuousOn out)
    (fun t ht => hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) out) hslew t
    ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hmove : |e t out - e t₁ out| ≤ min S.NML S.NMH := by
    rw [← Real.norm_eq_abs]
    refine hdist.trans ((mul_le_mul_of_nonneg_left htt (by positivity)).trans_eq ?_)
    unfold Params.tcdINV
    field_simp
  have hmove := abs_le.1 hmove
  cases b with
  | false =>
    have h1 : e t₁ out ≤ S.VOL := h1
    show e t out ≤ S.VIL
    linarith [min_le_left S.NML S.NMH, show S.NML = S.VIL - S.VOL from rfl]
  | true =>
    have h1 : S.VOH ≤ e t₁ out := h1
    show S.VIH ≤ e t out
    linarith [min_le_right S.NML S.NMH, show S.NMH = S.VOH - S.VIH from rfl]

end Netlist.IsInverter

end AsmPhys
