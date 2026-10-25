import AsmPhys.Cells.Inverter
import AsmPhys.Circuit.Inflow

/-!
# Inverter cores with side channels

An inverter core is an inverter whose output may carry extra channels (`side`), for instance a
transmission gate into a storage node. Its two transistors obey the inverter bounds; the side
transistors add their inflow. The pure inverter is the core with no side channels.

The output may sit anywhere in `[0, V_DD^max]`: hold tubes take no `V_DD` argument, so cells inside
them are only known to be on the rail `[0, V_DD^max]`. Above `V_DD` the p-FET is off (K4) and
conducts out of the output (C1), so the pull-down bounds hold up to `V_DD^max`.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- An inverter core: an n-FET `iN` from `out` to `gnd` and a p-FET `iP` from `out` to `vdd`, both
gated by `inp`, and no channel terminal at `out` other than these two and the `side` transistors. -/
structure Netlist.IsInvCore (N : Netlist n m) (inp : Node n m) (out : Fin n) (gnd vdd : Fin m)
    (iN iP : Fin N.nf) (side : Finset (Fin N.nf)) : Prop where
  ne : iN ≠ iP
  pol_n : (N.fet iN).pol = .n
  pol_p : (N.fet iP).pol = .p
  gate_n : (N.fet iN).g = inp
  gate_p : (N.fet iP).g = inp
  drain_n : (N.fet iN).d = .state out
  source_n : (N.fet iN).s = .bdry gnd
  drain_p : (N.fet iP).d = .state out
  source_p : (N.fet iP).s = .bdry vdd
  n_nmem : iN ∉ side
  p_nmem : iP ∉ side
  only : ∀ i, i ≠ iN → i ≠ iP → i ∉ side →
    (N.fet i).d ≠ .state out ∧ (N.fet i).s ≠ .state out

namespace Netlist

variable {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m} {iN iP : Fin N.nf}
  {side : Finset (Fin N.nf)}

/-- A pure inverter is a core with no side channels. -/
theorem IsInverter.toCore (h : N.IsInverter inp out gnd vdd iN iP) :
    N.IsInvCore inp out gnd vdd iN iP ∅ :=
  ⟨h.ne, h.pol_n, h.pol_p, h.gate_n, h.gate_p, h.drain_n, h.source_n, h.drain_p, h.source_p,
    Finset.notMem_empty _, Finset.notMem_empty _, fun i hn hp _ => h.only i hn hp⟩

namespace IsInvCore

/-- The n-FET's channel current at node potentials `(u, e)`. -/
theorem current_n (h : N.IsInvCore inp out gnd vdd iN iP side) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    (N.fet iN).current u e = (N.fet iN).I (pot u e inp) (e out) (u gnd) := by
  rw [FET.current, h.gate_n, h.drain_n, h.source_n, pot_state, pot_bdry]

/-- The p-FET's channel current at node potentials `(u, e)`. -/
theorem current_p (h : N.IsInvCore inp out gnd vdd iN iP side) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    (N.fet iP).current u e = (N.fet iP).I (pot u e inp) (e out) (u vdd) := by
  rw [FET.current, h.gate_p, h.drain_p, h.source_p, pot_state, pot_bdry]

/-- The net current into a core's output: the core's own current plus the side inflow. -/
theorem F_out (h : N.IsInvCore inp out gnd vdd iN iP side) (u : Fin m → ℝ) (e : Fin n → ℝ) :
    N.F u e out =
      -(N.fet iN).current u e - (N.fet iP).current u e + ∑ i ∈ side, N.inflow u e out i := by
  change ∑ i, N.inflow u e out i = _
  rw [← Finset.sum_subset (Finset.subset_univ (insert iN (insert iP side))) fun i _ hi => ?_,
    Finset.sum_insert (by simp [h.ne, h.n_nmem]), Finset.sum_insert h.p_nmem]
  · simp [inflow, h.drain_n, h.source_n, h.drain_p, h.source_p]
    ring
  · simp only [Finset.mem_insert, not_or] at hi
    obtain ⟨hd, hs⟩ := h.only i hi.1 hi.2.1 hi.2.2
    simp [inflow, hd, hs]

/-- With a valid-high input and the output in `[V_OL, V_DD^max]`, the core pulls down by at least
`I_fall` (K3, K4, K6, K13). -/
theorem core_le_neg_Ifall {S : Params} (hS : S.Consistent)
    (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn true (pot u e inp))
    (hout : e out ∈ Icc S.VOL S.VDDmax) :
    -(N.fet iN).current u e - (N.fet iP).current u e ≤ -S.Ifall := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hin : S.VIH ≤ pot u e inp := hin
  have hd : e out ∈ Icc 0 S.VDDmax := ⟨hVOL.le.trans hout.1, hout.2⟩
  have hs : VDD ∈ Icc 0 S.VDDmax := ⟨by linarith [hVDD.1], hVDD.2⟩
  -- Both terminals at most `V_DD^max` (K4): the p-FET is off.
  have hoff : offCond .p S.pp (pot u e inp) (e out) VDD := by
    show max (e out) VDD - pot u e inp ≤ S.pp.Voff
    linarith [max_le hout.2 hVDD.2, hS.K4]
  have hon : onCond .n S.pn (pot u e inp) (e out) 0 := by
    show S.pn.Von ≤ pot u e inp - min (e out) 0
    rw [min_eq_right hd.1, sub_zero]
    exact hS.K3.trans hin
  have hIp := abs_le.1 (hp.off_leak _ _ _ hd hs hoff)
  have hIn := hn.on_drive _ _ _ hd ⟨le_rfl, hs.1.trans hs.2⟩ hon
  rw [abs_of_nonneg (hn.passive.nonneg_of_le hn.regular hd.1), sub_zero,
    abs_of_nonneg hd.1] at hIn
  have hGn : 0 ≤ S.pn.Gon := (pos_of_mul_pos_left ((hS.K13_leak.2.trans_lt hS.K6).trans_le
    (min_le_left _ _)) hVOL.le).le
  have hmono : min (S.pn.Gon * S.VOL) S.pn.Isat ≤ min (S.pn.Gon * e out) S.pn.Isat :=
    min_le_min (mul_le_mul_of_nonneg_left hout.1 hGn) le_rfl
  rw [h.current_n, h.current_p, hgnd, hvdd]
  unfold Params.Ifall
  linarith

/-- With a valid-low input and the output in `[0, V_OH]`, the core pulls up by at least `I_rise`
(K1, K2, K5, K13). -/
theorem Irise_le_core {S : Params} (hS : S.Consistent)
    (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn false (pot u e inp))
    (hout : e out ∈ Icc 0 S.VOH) :
    S.Irise ≤ -(N.fet iN).current u e - (N.fet iP).current u e := by
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
  rw [h.current_n, h.current_p, hgnd, hvdd]
  unfold Params.Irise
  linarith

/-- With a valid-high input and the output on the rail, the core pushes in at most `I_off^p`. -/
theorem core_le_Ioff {S : Params} (hS : S.Consistent)
    (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn true (pot u e inp))
    (hout : e out ∈ Icc 0 S.VDDmax) :
    -(N.fet iN).current u e - (N.fet iP).current u e ≤ S.pp.Ioff := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hin : S.VIH ≤ pot u e inp := hin
  have hs : VDD ∈ Icc 0 S.VDDmax := ⟨by linarith [hVDD.1], hVDD.2⟩
  -- Both terminals at most `V_DD^max` (K4): the p-FET is off.
  have hoff : offCond .p S.pp (pot u e inp) (e out) VDD := by
    show max (e out) VDD - pot u e inp ≤ S.pp.Voff
    linarith [max_le hout.2 hVDD.2, hS.K4]
  have hIp := abs_le.1 (hp.off_leak _ _ _ hout hs hoff)
  -- The source is at `0 ≤ e_out`: the n-FET conducts out of the output.
  have hIn := hn.passive.nonneg_of_le hn.regular (g := pot u e inp) hout.1
  rw [h.current_n, h.current_p, hgnd, hvdd]
  linarith

/-- With a valid-low input and the output in `[0, V_DD]`, the core pulls out at most `I_off^n`. -/
theorem neg_Ioff_le_core {S : Params} (hS : S.Consistent)
    (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax) {u : Fin m → ℝ} {e : Fin n → ℝ}
    (hgnd : u gnd = 0) (hvdd : u vdd = VDD) (hin : S.validIn false (pot u e inp))
    (hout : e out ∈ Icc 0 VDD) :
    -S.pn.Ioff ≤ -(N.fet iN).current u e - (N.fet iP).current u e := by
  have hin : pot u e inp ≤ S.VIL := hin
  have hVDD0 : 0 ≤ VDD := hout.1.trans hout.2
  have hd : e out ∈ Icc 0 S.VDDmax := ⟨hout.1, hout.2.trans hVDD.2⟩
  have hoff : offCond .n S.pn (pot u e inp) (e out) 0 := by
    show pot u e inp - min (e out) 0 ≤ S.pn.Voff
    rw [min_eq_right hout.1, sub_zero]
    exact hin.trans hS.K1
  have hIn := abs_le.1 (hn.off_leak _ _ _ hd ⟨le_rfl, hVDD0.trans hVDD.2⟩ hoff)
  -- The source is at `V_DD ≥ e_out`: the p-FET conducts into the output.
  have hIp := hp.passive.nonpos_of_le hp.regular (g := pot u e inp) hout.2
  rw [h.current_n, h.current_p, hgnd, hvdd]
  linarith

end IsInvCore

end Netlist

namespace Params

/-- Propagation delay of an inverter core whose side inflow is at most `ε` in magnitude:
`C_out^max · max(V_OH / (I_rise − ε), (V_DD^max − V_OL) / (I_fall − ε))`. With `ε = 0` it is
`tpdINV`. -/
noncomputable def tpdSide (S : Params) (ε Cmax : ℝ) : ℝ :=
  Cmax * max (S.VOH / (S.Irise - ε)) ((S.VDDmax - S.VOL) / (S.Ifall - ε))

end Params

namespace Netlist

variable {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m} {iN iP : Fin N.nf}
  {side : Finset (Fin N.nf)}

/-- **THM L3.1** for an inverter core with side inflow at most `ε < min(I_rise, I_fall)`, output on
the rail `[0, V_DD^max]`: (a) valid inputs give a valid output after `tpdSide ε C_out^max`, and
(b) once valid, the output stays valid. -/
theorem IsInvCore.propagation_side {S : Params} (hS : S.Consistent)    -- THM (norm_num)
    (h : N.IsInvCore inp out gnd vdd iN iP side)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (hrail : ∀ t ∈ Icc t₀ t₁, e t out ∈ Icc 0 S.VDDmax)
    {x : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn x (pot (u t) (e t) inp))
    {ε : ℝ} (hεr : ε < min S.Irise S.Ifall)
    (hside : ∀ t ∈ Icc t₀ t₁, |∑ i ∈ side, N.inflow (u t) (e t) out i| ≤ ε) :
    (∀ t ∈ Icc (t₀ + S.tpdSide ε Cmax) t₁, S.validOut (!x) (e t out)) ∧
      ∀ t₂ ∈ Icc t₀ t₁, S.validOut (!x) (e t₂ out) →
        ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hCmax : 0 < Cmax := (N.C_pos out 0).trans_le (hcap 0).2
  have hr : 0 < S.Irise - ε := sub_pos.2 (hεr.trans_le (min_le_left _ _))
  have hf : 0 < S.Ifall - ε := sub_pos.2 (hεr.trans_le (min_le_right _ _))
  have htpd : 0 ≤ S.tpdSide ε Cmax :=
    mul_nonneg hCmax.le ((div_pos (by linarith) hr).le.trans (le_max_left _ _))
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
        (S.Irise - ε) / Cmax ≤ N.vf (u t) (e t) out := fun t ht hle => by
      have htI := Ico_subset_Icc_self ht
      have hcore := h.Irise_le_core hS hn hp hVDD (hgnd t htI) (hvdd t htI) (hin t htI)
        ⟨(hrail t htI).1, hle⟩
      have hs := abs_le.1 (hside t htI)
      exact hdiv _ hr.le (by rw [h.F_out]; linarith)
    refine ⟨fun t ht => ?_, fun t₂ ht₂ h2 t ht => ?_⟩
    · show S.VOH ≤ e t out
      refine reach_of_deriv_right_ge (div_pos hr hCmax) hg hg' hface t
        ⟨by linarith [ht.1], ht.2⟩ ?_
      calc S.VOH - e t₀ out ≤ (S.Irise - ε) / Cmax * (Cmax * (S.VOH / (S.Irise - ε))) := by
            rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hCmax.ne',
              mul_div_cancel₀ _ hr.ne']
            linarith [(hrail t₀ ⟨le_rfl, by linarith [ht.1, ht.2]⟩).1]
        _ ≤ (S.Irise - ε) / Cmax * (t - t₀) :=
            mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_left _ _)
              hCmax.le).trans (show S.tpdSide ε Cmax ≤ t - t₀ by linarith [ht.1]))
              (div_pos hr hCmax).le
    · exact barrier_of_deriv_right_nonneg (hg.mono (Icc_subset_Icc_left ht₂.1))
        (fun s hs => hg' s (hsub ht₂ hs)) h2
        (fun s hs hle => (div_pos hr hCmax).le.trans (hface s (hsub ht₂ hs) hle)) t ht
  | true =>
    have hface : ∀ t ∈ Ico t₀ t₁, -e t out ≤ -S.VOL →
        (S.Ifall - ε) / Cmax ≤ -N.vf (u t) (e t) out := fun t ht hle => by
      have htI := Ico_subset_Icc_self ht
      have hcore := h.core_le_neg_Ifall hS hn hp hVDD (hgnd t htI) (hvdd t htI) (hin t htI)
        ⟨neg_le_neg_iff.1 hle, (hrail t htI).2⟩
      have hs := abs_le.1 (hside t htI)
      rw [Netlist.vf, ← neg_div]
      exact hdiv _ hf.le (by rw [h.F_out]; linarith)
    refine ⟨fun t ht => ?_, fun t₂ ht₂ h2 t ht => ?_⟩
    · show e t out ≤ S.VOL
      refine neg_le_neg_iff.1 (reach_of_deriv_right_ge (div_pos hf hCmax) hg.neg
        (fun t ht => (hg' t ht).neg) hface t ⟨by linarith [ht.1], ht.2⟩ ?_)
      calc -S.VOL - -e t₀ out
          ≤ (S.Ifall - ε) / Cmax * (Cmax * ((S.VDDmax - S.VOL) / (S.Ifall - ε))) := by
            rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hCmax.ne',
              mul_div_cancel₀ _ hf.ne']
            linarith [(hrail t₀ ⟨le_rfl, by linarith [ht.1, ht.2]⟩).2]
        _ ≤ (S.Ifall - ε) / Cmax * (t - t₀) :=
            mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_right _ _)
              hCmax.le).trans (show S.tpdSide ε Cmax ≤ t - t₀ by linarith [ht.1]))
              (div_pos hf hCmax).le
    · have h2 : e t₂ out ≤ S.VOL := h2
      show e t out ≤ S.VOL
      exact neg_le_neg_iff.1 (barrier_of_deriv_right_nonneg
        (hg.neg.mono (Icc_subset_Icc_left ht₂.1)) (fun s hs => (hg' s (hsub ht₂ hs)).neg)
        (neg_le_neg h2)
        (fun s hs hle => (div_pos hf hCmax).le.trans (hface s (hsub ht₂ hs) hle)) t ht)

/-- **THM L3.1** for a pure inverter whose output is on the rail `[0, V_DD^max]` (rather than
starting in `[0, V_DD]`). -/
theorem IsInverter.propagation_rail {S : Params} (hS : S.Consistent)  -- THM (norm_num)
    (h : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (hrail : ∀ t ∈ Icc t₀ t₁, e t out ∈ Icc 0 S.VDDmax)
    {x : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn x (pot (u t) (e t) inp)) :
    (∀ t ∈ Icc (t₀ + S.tpdINV Cmax) t₁, S.validOut (!x) (e t out)) ∧
      ∀ t₂ ∈ Icc t₀ t₁, S.validOut (!x) (e t₂ out) →
        ∀ t ∈ Icc t₂ t₁, S.validOut (!x) (e t out) := by
  have hεr : (0 : ℝ) < min S.Irise S.Ifall := lt_min (sub_pos.2 hS.K5) (sub_pos.2 hS.K6)
  have htpd : S.tpdSide 0 Cmax = S.tpdINV Cmax := by
    simp only [Params.tpdSide, Params.tpdINV, sub_zero]
  have := h.toCore.propagation_side hS hn hp hcap hVDD he hgnd hvdd hrail hin hεr
    fun t _ => by rw [Finset.sum_empty, abs_zero]
  rwa [htpd] at this

/-- **THM L3.2** for a pure inverter whose output is on the rail `[0, V_DD^max]`. -/
theorem IsInverter.contamination_rail {S : Params} (hS : S.Consistent) -- THM (norm_num)
    (h : N.IsInverter inp out gnd vdd iN iP)
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
    (hrail : ∀ t ∈ Icc t₁ t₂, e t out ∈ Icc 0 S.VDDmax)
    {b : Bool} (h1 : S.validOut b (e t₁ out)) :
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV Cmin)), S.validIn b (e t out) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  have hVDD0 : 0 ≤ VDD := by linarith [hVDD.1]
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
    have hIn : |(N.fet iN).current (u t) (e t)| ≤ S.pn.Imax := by
      rw [h.current_n, hgnd t htI]
      exact hn.bounded _ _ _ (hin t htI) (hrail t htI) ⟨le_rfl, hVDD0.trans hVDD.2⟩
    have hIp : |(N.fet iP).current (u t) (e t)| ≤ S.pp.Imax := by
      rw [h.current_p, hvdd t htI]
      exact hp.bounded _ _ _ (hin t htI) (hrail t htI) ⟨hVDD0, hVDD.2⟩
    have hF : |N.F (u t) (e t) out| ≤ 2 * max S.pn.Imax S.pp.Imax := by
      rw [h.F_out, abs_le]
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

end Netlist

end AsmPhys
