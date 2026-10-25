import AsmPhys.Cells.TGLatchAgree
import AsmPhys.Cells.TGLatchPair
import AsmPhys.Cells.InverterCell

/-!
# Transmission-gate latch: the whole latch settles

Once the input pair has settled (`pair_settle`), the forward inverter and then the feedback core
follow within their delays, so the whole latch agrees on the input's bit.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- `PhiTG ≥ 0` for nonnegative capacitances (K0, K6, K13). -/
theorem Params.Consistent.PhiTG_nonneg {S : Params} (hS : S.Consistent) {CA CX : ℝ}
    (hCA : 0 ≤ CA) (hCX : 0 ≤ CX) : 0 ≤ S.PhiTG CA CX := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  -- The n-FET's drive floor at `V_OL` beats a nonnegative leak (K6, K13).
  have hK6 := lt_min_iff.1 (hS.K13_leak.2.trans_lt hS.K6)
  have hGn : 0 < S.pn.Gon := pos_of_mul_pos_left hK6.1 hVOL.le
  have hVDD : 0 ≤ S.VDDmax := by linarith [hS.K13_supply]
  have hr₁ : 0 ≤ min (S.pn.Gon * S.VOL) S.pn.Isat := (hS.K13_leak.2.trans_lt hS.K6).le
  have hr₂ : 0 ≤ min (S.pn.Gon * (S.NML / 2)) S.pn.Isat :=
    le_min (mul_nonneg hGn.le (by unfold Params.NML; linarith)) hK6.2.le
  exact le_max_of_le_left (add_nonneg
    (div_nonneg (mul_nonneg (add_nonneg hCA hCX) hVDD) hr₁)
    (div_nonneg (mul_nonneg hCX hVDD) hr₂))

namespace Netlist.IsTGLatch

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

/-- A latch level is a valid input level (K0). -/
private theorem validIn_of_Lvl {S : Params} (hS : S.Consistent) {c : Bool} {v : ℝ}
    (h : S.Lvl c v) : S.validIn c v := by
  obtain ⟨hδ, -, hθVIL, hVIHθ, -⟩ := hS.band
  cases c
  · exact show v ≤ S.VIL by have : v ≤ S.θL := h; linarith
  · exact show S.VIH ≤ v by have : S.θH ≤ v := h; linarith

/-- A valid output level is at the latch level (K0). -/
private theorem Lvl_of_validOut {S : Params} (hS : S.Consistent) {c : Bool} {v : ℝ}
    (h : S.validOut c v) : S.Lvl c v := by
  obtain ⟨hδ, hVOLθ, -, -, hθVOH⟩ := hS.band
  cases c
  · exact show v ≤ S.θL by have : v ≤ S.VOL := h; linarith
  · exact show S.θH ≤ v by have : S.VOH ≤ v := h; linarith

variable {N : Netlist n m} {gnd vdd : Fin m} {i₁ : Node n m} {x y a₁ a₂ : Fin n}
  {g₁n g₁p g₂n g₂p : Node n m} {c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp : Fin N.nf}

/-- **Latch settle.** Under `pair_settle`'s hypotheses, the whole latch agrees on `b` after the pair
settles and the forward inverter and the feedback core follow. -/
theorem settle {S : Params} (hS : S.Consistent)                      -- THM (norm_num)
    (hL : N.IsTGLatch gnd vdd i₁ x y a₁ a₂ g₁n g₁p g₂n g₂p
      c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp)
    (hc : N.ContractOn S {c₁n, c₁p, c₂n, c₂p, t₁n, t₁p, t₂n, t₂p, yn, yp})  -- MODEL/MEAS
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {CminA CmaxA CminX CmaxX CminY CmaxY CminA₂ CmaxA₂ : ℝ}
    (hcA : NodeCap CminA CmaxA (N.C a₁)) (hcX : NodeCap CminX CmaxX (N.C x))  -- MEAS/MODEL
    (hcY : NodeCap CminY CmaxY (N.C y)) (hcA₂ : NodeCap CminA₂ CmaxA₂ (N.C a₂))  -- MEAS/MODEL
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}
    (he : N.IsTrajOn u e t₀ t₁)
    (hgnd : ∀ t ∈ Icc t₀ t₁, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₀ t₁, u t vdd = VDD)                          -- ENV
    (hrail : ∀ t ∈ Icc t₀ t₁, ∀ k ∈ ({x, y, a₁, a₂} : Finset (Fin n)),
      e t k ∈ Icc 0 S.VDDmax)
    {b : Bool} (hin : ∀ t ∈ Icc t₀ t₁, S.validIn b (pot (u t) (e t) i₁))
    (hon : ∀ t ∈ Icc t₀ t₁, S.VIH ≤ pot (u t) (e t) g₁n ∧ pot (u t) (e t) g₁p ≤ S.VIL)
    (hoff₂ : ∀ t ∈ Icc t₀ t₁, pot (u t) (e t) g₂n ≤ S.VIL ∧ S.VIH ≤ pot (u t) (e t) g₂p) :
    ∀ t ∈ Icc (t₀ + S.PhiTG CmaxA CmaxX + S.tpdINV CmaxY + S.tpdINV CmaxA₂) t₁,
      latchAgree S b x y a₁ a₂ (e t) := by
  have hyn := contract_n hc (by simp) hL.fwd.pol_n
  have hyp := contract_p hc (by simp) hL.fwd.pol_p
  have hc₂n := contract_n hc (by simp) hL.core₂.pol_n
  have hc₂p := contract_p hc (by simp) hL.core₂.pol_p
  have ht₂n := contract_n hc (by simp) hL.tg₂.pol_n
  have ht₂p := contract_p hc (by simp) hL.tg₂.pol_p
  have hpair := hL.pair_settle hS hc hI hcA hcX hVDD he hgnd hvdd hrail hin hon hoff₂
  have hCmax : ∀ {Cmin Cmax : ℝ} {C : ℝ → ℝ}, NodeCap Cmin Cmax C → 0 ≤ Cmax :=
    fun h => (h.pos.le.trans (h.range 0).1).trans (h.range 0).2
  have hΦ := hS.PhiTG_nonneg (hCmax hcA) (hCmax hcX)
  have hY := hS.tpdINV_nonneg (hCmax hcY)
  have hA₂ := hS.tpdINV_nonneg (hCmax hcA₂)
  set T₁ := t₀ + S.PhiTG CmaxA CmaxX with hT₁
  set T₂ := T₁ + S.tpdINV CmaxY with hT₂
  intro t ht
  have hsub : ∀ {a : ℝ}, t₀ ≤ a → ∀ s ∈ Icc a t₁, s ∈ Icc t₀ t₁ :=
    fun ha s hs => ⟨ha.trans hs.1, hs.2⟩
  have h₀₁ : t₀ ≤ T₁ := by linarith
  have h₀₂ : t₀ ≤ T₂ := by linarith
  -- From `T₁` the storage node is at the latch level of `¬b` (`pair_settle`), so the forward
  -- inverter makes `y` a valid output `b` from `T₂` on (THM L3.1).
  have hfwd := (hL.fwd.propagation_rail hS hyn hyp hcY.range hVDD (he.mono h₀₁ le_rfl)
    (fun s hs => hgnd s (hsub h₀₁ s hs)) (fun s hs => hvdd s (hsub h₀₁ s hs))
    (fun s hs => hrail s (hsub h₀₁ s hs) y (by simp)) (x := !b)
    (fun s hs => validIn_of_Lvl hS (hpair s hs).2)).1
  rw [Bool.not_not] at hfwd
  -- The feedback gate is off and leaks nothing, so the feedback core has no side current, and
  -- from `T₂` its input `y` is valid: `a₂` is a valid output `¬b` after `tpdSide 0 = tpdINV`.
  have hεr : (0 : ℝ) < min S.Irise S.Ifall := lt_min (sub_pos.2 hS.K5) (sub_pos.2 hS.K6)
  have hcore := (hL.core₂.propagation_side hS hc₂n hc₂p hcA₂.range hVDD (he.mono h₀₂ le_rfl)
    (fun s hs => hgnd s (hsub h₀₂ s hs)) (fun s hs => hvdd s (hsub h₀₂ s hs))
    (fun s hs => hrail s (hsub h₀₂ s hs) a₂ (by simp)) (x := b)
    (fun s hs => hS.validIn_of_validOut (hfwd s hs)) hεr (fun s hs => by
      have hs' := hsub h₀₂ s hs
      have hJ := hL.tg₂.abs_J_le_Ioff hS ht₂n ht₂p (hoff₂ s hs').1 (hoff₂ s hs').2
        (hrail s hs' x (by simp)) (hrail s hs' a₂ (by simp))
      rw [hI.1, hI.2, add_zero] at hJ
      rw [Finset.sum_pair hL.tg₂.ne, hL.tg₂.inflow_y, abs_neg]
      exact hJ)).1
  have htpd : S.tpdSide 0 CmaxA₂ = S.tpdINV CmaxA₂ := by
    simp only [Params.tpdSide, Params.tpdINV, sub_zero]
  rw [htpd] at hcore
  have htT₁ : t ∈ Icc T₁ t₁ := ⟨by linarith [ht.1], ht.2⟩
  exact ⟨(hpair t htT₁).1, (hpair t htT₁).2, Lvl_of_validOut hS (hcore t ht),
    hfwd t ⟨by linarith [ht.1], ht.2⟩⟩

end Netlist.IsTGLatch

end AsmPhys
