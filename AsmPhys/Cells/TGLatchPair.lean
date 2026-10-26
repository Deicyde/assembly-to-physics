import AsmPhys.Cells.TGLatch
import AsmPhys.Circuit.Lyapunov

/-!
# Transmission-gate latch: the input pair settles

With the input gate on, the feedback gate off and the input valid, the pair (input core, storage node)
reaches the input's latch level from any state on the rails within `PhiTG` and stays there
(docs/SPIKE-FLIPFLOP.md §10, L12). The Lyapunov function is the pair's charge (clipped at `V_OH` in
the high case) over the core's drive floor, plus the distance of the pair's extreme from the latch
level over the gate's drive floor: the gate's current is internal to the pair's charge, the core
drains it at rate at least `min(G_on·V_OL, I_sat)` while the core is above `V_OL`, and otherwise the
gate drains the storage node at rate at least `min(G_on·NM/2, I_sat)`.
-/

namespace AsmPhys

open Set

/-- A clipped right derivative of a minimum is at least `min d 0`. -/
private theorem min_le_clip {f g d : ℝ} :
    min d 0 ≤ if f < g then d else if g < f then 0 else min d 0 := by
  split_ifs
  exacts [min_le_left _ _, min_le_right _ _, le_rfl]

/-- **Clipped pair settle**, for real functions. `A` is driven by a core current `K` and gives the
current `J` to `X`, with capacitance laws `cA`, `cX`. Passivity fixes the sign of `J`, the core
pushes in at least `r₁` up to `V_OH`, and the gate carries at least `r₂` into `X` while `A ≥ V_OH`
and `X < θ_H`. Then `A` and `X` reach `θ_H` within `(C_A^max + C_X^max)·V/r₁ + C_X^max·V/r₂` and
stay there. The Lyapunov function is the pair's charge deficit below `V_OH` over `r₁` plus
`(θ_H − min(A, X))·C_X^max/r₂`. -/
private theorem settle_hi {A X K J cA cX : ℝ → ℝ}
    {t₀ t₁ V VOH θH r₁ r₂ CminA CmaxA CminX CmaxX : ℝ}
    (hcA : Continuous cA) (hcX : Continuous cX) (hCA : 0 < CminA) (hCX : 0 < CminX)
    (hcAr : ∀ v, cA v ∈ Icc CminA CmaxA) (hcXr : ∀ v, cX v ∈ Icc CminX CmaxX)
    (hA : ContinuousOn A (Icc t₀ t₁)) (hX : ContinuousOn X (Icc t₀ t₁))
    (dA : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt A ((K t - J t) / cA (A t)) (Ici t) t)
    (dX : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt X (J t / cX (X t)) (Ici t) t)
    (hAr : ∀ t ∈ Icc t₀ t₁, A t ∈ Icc 0 V) (hXr : ∀ t ∈ Icc t₀ t₁, X t ∈ Icc 0 V)
    (hθ : θH ≤ VOH) (hVOH : VOH ∈ Icc 0 V) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hJp : ∀ t ∈ Ico t₀ t₁, X t ≤ A t → 0 ≤ J t)
    (hJn : ∀ t ∈ Ico t₀ t₁, A t ≤ X t → J t ≤ 0)
    (hK : ∀ t ∈ Ico t₀ t₁, A t ≤ VOH → r₁ ≤ K t)
    (hJon : ∀ t ∈ Ico t₀ t₁, VOH ≤ A t → X t < θH → r₂ ≤ J t) :
    ∀ t ∈ Icc (t₀ + ((CmaxA + CmaxX) * V / r₁ + CmaxX * V / r₂)) t₁,
      θH ≤ A t ∧ θH ≤ X t := by
  intro t ht
  have hcAp : ∀ v, 0 < cA v := fun v => hCA.trans_le (hcAr v).1
  have hcXp : ∀ v, 0 < cX v := fun v => hCX.trans_le (hcXr v).1
  have hCmaxA : 0 ≤ CmaxA := (hcAp 0).le.trans (hcAr 0).2
  have hCmaxX : 0 < CmaxX := (hcXp 0).trans_le (hcXr 0).2
  have hV : 0 ≤ V := hVOH.1.trans hVOH.2
  have hB : 0 ≤ (CmaxA + CmaxX) * V / r₁ + CmaxX * V / r₂ := by positivity
  have ht₀₁ : t₀ ≤ t₁ := by linarith [ht.1, ht.2]
  have hqA := strictMono_charge hcA hcAp
  have hqX := strictMono_charge hcX hcXp
  have hqAc : Continuous (charge cA) :=
    continuous_iff_continuousAt.2 fun v => (hasDerivAt_charge hcA v).continuousAt
  have hqXc : Continuous (charge cX) :=
    continuous_iff_continuousAt.2 fun v => (hasDerivAt_charge hcX v).continuousAt
  have hmin : ∀ {f g : ℝ → ℝ} {s : Set ℝ}, ContinuousOn f s → ContinuousOn g s →
      ContinuousOn (fun x => min (f x) (g x)) s := fun hf hg =>
    continuous_min.comp_continuousOn (hf.prodMk hg)
  have hq0A : ∀ v, 0 ≤ v → 0 ≤ charge cA v := fun v hv =>
    (mul_nonneg hCA.le hv).trans (charge_mem_Icc hcA hcAr hv).1
  have hq0X : ∀ v, 0 ≤ v → 0 ≤ charge cX v := fun v hv =>
    (mul_nonneg hCX.le hv).trans (charge_mem_Icc hcX hcXr hv).1
  -- The charges' right derivatives are the net currents.
  have dqA : ∀ s ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun s => charge cA (A s)) (K s - J s) (Ici s) s := by
    intro s hs
    have h := (hasDerivAt_charge hcA (A s)).comp_hasDerivWithinAt s (dA s hs)
    rwa [mul_div_cancel₀ _ (hcAp _).ne'] at h
  have dqX : ∀ s ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun s => charge cX (X s)) (J s) (Ici s) s := by
    intro s hs
    have h := (hasDerivAt_charge hcX (X s)).comp_hasDerivWithinAt s (dX s hs)
    rwa [mul_div_cancel₀ _ (hcXp _).ne'] at h
  -- Right derivatives of the clipped charges and of `min A X`.
  obtain ⟨cA', hcA'⟩ : ∃ f : ℝ → ℝ, ∀ s, f s =
      if charge cA (A s) < charge cA VOH then K s - J s
      else if charge cA VOH < charge cA (A s) then 0 else min (K s - J s) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨cX', hcX'⟩ : ∃ f : ℝ → ℝ, ∀ s, f s =
      if charge cX (X s) < charge cX VOH then J s
      else if charge cX VOH < charge cX (X s) then 0 else min (J s) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨m', hm'⟩ : ∃ f : ℝ → ℝ, ∀ s, f s =
      if A s < X s then (K s - J s) / cA (A s) else if X s < A s then J s / cX (X s)
      else min ((K s - J s) / cA (A s)) (J s / cX (X s)) := ⟨_, fun _ => rfl⟩
  have dDA : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => charge cA VOH - min (charge cA (A s)) (charge cA VOH)) (-cA' s) (Ici s) s := by
    intro s hs
    rw [hcA']
    exact (HasDerivWithinAt.min_Ici (dqA s hs)
      (hasDerivWithinAt_const s (Ici s) (charge cA VOH))).const_sub _
  have dDX : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => charge cX VOH - min (charge cX (X s)) (charge cX VOH)) (-cX' s) (Ici s) s := by
    intro s hs
    rw [hcX']
    exact (HasDerivWithinAt.min_Ici (dqX s hs)
      (hasDerivWithinAt_const s (Ici s) (charge cX VOH))).const_sub _
  have dm : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun s => min (A s) (X s)) (m' s) (Ici s) s := by
    intro s hs
    rw [hm']
    exact HasDerivWithinAt.min_Ici (dA s hs) (dX s hs)
  have hcA_lt : ∀ s, A s < VOH → cA' s = K s - J s := fun s h => by
    rw [hcA']
    exact ite_eq_left (hqA.lt_iff_lt.2 h)
  have hcA_gt : ∀ s, VOH < A s → cA' s = 0 := fun s h => by
    rw [hcA', ite_eq_right (not_lt.2 (hqA.lt_iff_lt.2 h).le), ite_eq_left (hqA.lt_iff_lt.2 h)]
  have hcX_lt : ∀ s, X s < VOH → cX' s = J s := fun s h => by
    rw [hcX']
    exact ite_eq_left (hqX.lt_iff_lt.2 h)
  have hcA_ge : ∀ s, min (K s - J s) 0 ≤ cA' s := fun s => by
    rw [hcA']
    exact min_le_clip
  have hcX_ge : ∀ s, min (J s) 0 ≤ cX' s := fun s => by
    rw [hcX']
    exact min_le_clip
  -- Below `V_OH`, the smaller of `A` and `X` does not fall.
  have hm : ∀ s ∈ Ico t₀ t₁, min (A s) (X s) ≤ VOH → 0 ≤ m' s := by
    intro s hs hmin
    rw [hm']
    split_ifs with h₁ h₂
    · rw [min_eq_left h₁.le] at hmin
      exact div_nonneg (by linarith [hK s hs hmin, hJn s hs h₁.le]) (hcAp _).le
    · exact div_nonneg (hJp s hs h₂.le) (hcXp _).le
    · have he : A s = X s := le_antisymm (not_lt.1 h₂) (not_lt.1 h₁)
      rw [he, min_self] at hmin
      have hJ0 : J s = 0 := le_antisymm (hJn s hs he.le) (hJp s hs he.ge)
      rw [hJ0, sub_zero, zero_div]
      exact le_min (div_nonneg (by linarith [hK s hs (he.le.trans hmin)]) (hcAp _).le) le_rfl
  -- The Lyapunov function and its right derivative.
  have hΦc : ContinuousOn (fun s => (charge cA VOH - min (charge cA (A s)) (charge cA VOH) +
      (charge cX VOH - min (charge cX (X s)) (charge cX VOH))) / r₁ +
      (θH - min (A s) (X s)) * CmaxX / r₂) (Icc t₀ t₁) :=
    ((continuousOn_const.sub (hmin (hqAc.comp_continuousOn hA) continuousOn_const)).add
      (continuousOn_const.sub (hmin (hqXc.comp_continuousOn hX) continuousOn_const))).div_const _
      |>.add (((continuousOn_const.sub (hmin hA hX)).mul continuousOn_const).div_const _)
  have dΦ : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => (charge cA VOH - min (charge cA (A s)) (charge cA VOH) +
        (charge cX VOH - min (charge cX (X s)) (charge cX VOH))) / r₁ +
        (θH - min (A s) (X s)) * CmaxX / r₂)
      ((-cA' s + -cX' s) / r₁ + -m' s * CmaxX / r₂) (Ici s) s := fun s hs =>
    (((dDA s hs).add (dDX s hs)).div_const r₁).add
      ((((dm s hs).const_sub θH).mul_const CmaxX).div_const r₂)
  have hmθ : ∀ s, ¬(θH ≤ A s ∧ θH ≤ X s) → min (A s) (X s) < θH := fun s hP =>
    lt_of_not_ge fun h => hP ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩
  -- Off the target the Lyapunov function falls at rate at least `1`.
  have hdec : ∀ s ∈ Ico t₀ t₁, ¬(θH ≤ A s ∧ θH ≤ X s) →
      (-cA' s + -cX' s) / r₁ + -m' s * CmaxX / r₂ ≤ -1 := by
    intro s hs hP
    have hms := hmθ s hP
    rcases lt_or_ge (A s) VOH with hAV | hAV
    · -- `A < V_OH`: the core drives the pair's charge deficit down at rate `r₁`; `min A X` does
      -- not fall.
      have hKs := hK s hs hAV.le
      have hcX : J s ≤ cX' s := by
        rcases lt_or_ge (X s) VOH with hXV | hXV
        · exact (hcX_lt s hXV).ge
        · have := hcX_ge s
          rwa [min_eq_left (hJn s hs (by linarith))] at this
      have h₁ : (-cA' s + -cX' s) / r₁ ≤ -1 := by
        rw [div_le_iff₀ hr₁, hcA_lt s hAV]
        linarith
      have h₂ : 0 ≤ m' s * CmaxX / r₂ :=
        div_nonneg (mul_nonneg (hm s hs ((min_le_left _ _).trans hAV.le)) hCmaxX.le) hr₂.le
      have h₃ : -m' s * CmaxX / r₂ = -(m' s * CmaxX / r₂) := by ring
      linarith
    · -- `A ≥ V_OH`: then `X < θ_H`, the gate drives `X` up at rate `r₂/C_X^max`, and the pair's
      -- charge deficit does not grow.
      have hXθ : X s < θH := by
        rcases min_lt_iff.1 hms with h | h
        · linarith
        · exact h
      have hXA : X s < A s := by linarith
      have hJ := hJon s hs hAV hXθ
      have hm_eq : m' s = J s / cX (X s) := by
        rw [hm', ite_eq_right (not_lt.2 hXA.le), ite_eq_left hXA]
      have hcX : cX' s = J s := hcX_lt s (by linarith)
      have hcA : -J s ≤ cA' s := by
        rcases hAV.lt_or_eq with hAV' | hAV'
        · rw [hcA_gt s hAV']
          linarith
        · have := hcA_ge s
          have hKs := hK s hs hAV'.ge
          exact le_trans (le_min (by linarith) (by linarith)) this
      have h₁ : (-cA' s + -cX' s) / r₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr₁.le
      have hcx := hcXr (X s)
      have hcxp := hcXp (X s)
      have h₂ : r₂ ≤ m' s * CmaxX := by
        rw [hm_eq, div_mul_eq_mul_div, le_div_iff₀ hcxp]
        nlinarith [hcx.2]
      have h₃ : -m' s * CmaxX / r₂ ≤ -1 := by
        rw [div_le_iff₀ hr₂]
        linarith
      linarith
  -- Off the target the Lyapunov function is positive.
  have hpos : ∀ s ∈ Icc t₀ t₁, ¬(θH ≤ A s ∧ θH ≤ X s) →
      0 < (charge cA VOH - min (charge cA (A s)) (charge cA VOH) +
        (charge cX VOH - min (charge cX (X s)) (charge cX VOH))) / r₁ +
        (θH - min (A s) (X s)) * CmaxX / r₂ := by
    intro s _ hP
    refine add_pos_of_nonneg_of_pos (div_nonneg (add_nonneg (sub_nonneg.2 (min_le_right _ _))
      (sub_nonneg.2 (min_le_right _ _))) hr₁.le) (div_pos (mul_pos ?_ hCmaxX) hr₂)
    linarith [hmθ s hP]
  -- At `t₀` the Lyapunov function is at most the settling bound.
  have hΦ₀ : (charge cA VOH - min (charge cA (A t₀)) (charge cA VOH) +
      (charge cX VOH - min (charge cX (X t₀)) (charge cX VOH))) / r₁ +
      (θH - min (A t₀) (X t₀)) * CmaxX / r₂ ≤
      (CmaxA + CmaxX) * V / r₁ + CmaxX * V / r₂ := by
    have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht₀₁⟩
    obtain ⟨hA0, -⟩ := hAr t₀ ht₀
    obtain ⟨hX0, -⟩ := hXr t₀ ht₀
    have hqAV := (charge_mem_Icc hcA hcAr hVOH.1).2
    have hqXV := (charge_mem_Icc hcX hcXr hVOH.1).2
    have hminA : 0 ≤ min (charge cA (A t₀)) (charge cA VOH) := le_min (hq0A _ hA0) (hq0A _ hVOH.1)
    have hminX : 0 ≤ min (charge cX (X t₀)) (charge cX VOH) := le_min (hq0X _ hX0) (hq0X _ hVOH.1)
    have h₁ := mul_le_mul_of_nonneg_left hVOH.2 hCmaxA
    have h₂ := mul_le_mul_of_nonneg_left hVOH.2 hCmaxX.le
    have h₃ : θH - min (A t₀) (X t₀) ≤ V := by linarith [le_min hA0 hX0, hVOH.2]
    refine add_le_add (div_le_div_of_nonneg_right (by linarith) hr₁.le)
      (div_le_div_of_nonneg_right ?_ hr₂.le)
    nlinarith
  have hmax := max_le hB hΦ₀
  obtain ⟨τ, hτ, hPτ⟩ := reach_of_lyapunov (P := fun s => θH ≤ A s ∧ θH ≤ X s) hΦc dΦ hdec hpos
    (by linarith [ht.1, ht.2])
  -- After `τ`, `min A X` stays at least `θ_H`.
  have hτt : τ ≤ t := hτ.2.trans (by linarith [ht.1])
  have hstay := barrier_of_deriv_right_nonneg (g := fun s => min (A s) (X s)) (g' := m')
    ((hmin hA hX).mono (Icc_subset_Icc_left hτ.1)) (fun s hs => dm s ⟨hτ.1.trans hs.1, hs.2⟩)
    (le_min hPτ.1 hPτ.2) (fun s hs h => hm s ⟨hτ.1.trans hs.1, hs.2⟩ (h.trans hθ)) t ⟨hτt, ht.2⟩
  exact le_min_iff.1 hstay

variable {n m : ℕ}

namespace Netlist.IsTGLatch

/-- Passivity: with `e x ≤ e y`, a gate between `x` and `y` carries current into `x` (C1, C2). -/
private theorem J_nonneg_of_le {N : Netlist n m} {x y : Fin n} {gn gp : Node n m}
    {jN jP : Fin N.nf} (h : N.IsTG x y gn gp jN jP)
    (hpn : Passive (N.fet jN).I) (hrn : Regular (N.fet jN).I)
    (hpp : Passive (N.fet jP).I) (hrp : Regular (N.fet jP).I)
    {u : Fin m → ℝ} {e : Fin n → ℝ} (hle : e x ≤ e y) : 0 ≤ h.J u e := by
  have key : ∀ j : Fin N.nf, Passive (N.fet j).I → Regular (N.fet j).I →
      (((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
        ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) → 0 ≤ N.inflow u e x j := by
    intro j hp hr hc
    rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · simp only [inflow, FET.current, hd, hs, Node.state.injEq, h.xy.symm, ite_true, ite_false,
        sub_zero, pot_state]
      exact hp.nonneg_of_le hr hle
    · simp only [inflow, FET.current, hd, hs, Node.state.injEq, h.xy.symm, ite_true, ite_false,
        zero_sub, pot_state, neg_nonneg]
      exact hp.nonpos_of_le hr hle
  exact add_nonneg (key jN hpn hrn h.chan_n) (key jP hpp hrp h.chan_p)

/-- Passivity: with `e y ≤ e x`, a gate between `x` and `y` carries current out of `x` (C1, C2). -/
private theorem J_nonpos_of_le {N : Netlist n m} {x y : Fin n} {gn gp : Node n m}
    {jN jP : Fin N.nf} (h : N.IsTG x y gn gp jN jP)
    (hpn : Passive (N.fet jN).I) (hrn : Regular (N.fet jN).I)
    (hpp : Passive (N.fet jP).I) (hrp : Regular (N.fet jP).I)
    {u : Fin m → ℝ} {e : Fin n → ℝ} (hle : e y ≤ e x) : h.J u e ≤ 0 := by
  have key : ∀ j : Fin N.nf, Passive (N.fet j).I → Regular (N.fet j).I →
      (((N.fet j).d = .state y ∧ (N.fet j).s = .state x) ∨
        ((N.fet j).d = .state x ∧ (N.fet j).s = .state y)) → N.inflow u e x j ≤ 0 := by
    intro j hp hr hc
    rcases hc with ⟨hd, hs⟩ | ⟨hd, hs⟩
    · simp only [inflow, FET.current, hd, hs, Node.state.injEq, h.xy.symm, ite_true, ite_false,
        sub_zero, pot_state]
      exact hp.nonpos_of_le hr hle
    · simp only [inflow, FET.current, hd, hs, Node.state.injEq, h.xy.symm, ite_true, ite_false,
        zero_sub, pot_state, neg_nonpos]
      exact hp.nonneg_of_le hr hle
  exact add_nonpos (key jN hpn hrn h.chan_n) (key jP hpp hrp h.chan_p)

/-- A contract on `T` gives each n-FET in `T` the n-FET contract. -/
private theorem contractOn_n {N : Netlist n m} {S : Params} {T : Finset (Fin N.nf)}
    (hc : N.ContractOn S T) {i : Fin N.nf} (hi : i ∈ T) (hpol : (N.fet i).pol = .n) :
    FETContract .n S.pn S.VDDmax (N.fet i).I := by
  have h := hc i hi
  rw [hpol] at h
  exact h

/-- A contract on `T` gives each p-FET in `T` the p-FET contract. -/
private theorem contractOn_p {N : Netlist n m} {S : Params} {T : Finset (Fin N.nf)}
    (hc : N.ContractOn S T) {i : Fin N.nf} (hi : i ∈ T) (hpol : (N.fet i).pol = .p) :
    FETContract .p S.pp S.VDDmax (N.fet i).I := by
  have h := hc i hi
  rw [hpol] at h
  exact h

variable {N : Netlist n m} {gnd vdd : Fin m} {i₁ : Node n m} {x y a₁ a₂ : Fin n}
  {g₁n g₁p g₂n g₂p : Node n m} {c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp : Fin N.nf}

/-- **Pair settle.** Without leakage, with the input gate on, the feedback gate off and the input
`validIn b`, the input core and the storage node reach the latch level of `¬b` from any state on
the rails within `PhiTG`, and stay there. -/
theorem pair_settle {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
    (hL : N.IsTGLatch gnd vdd i₁ x y a₁ a₂ g₁n g₁p g₂n g₂p
      c₁n c₁p c₂n c₂p t₁n t₁p t₂n t₂p yn yp)
    (hc : N.ContractOn S {c₁n, c₁p, c₂n, c₂p, t₁n, t₁p, t₂n, t₂p, yn, yp})  -- MODEL/MEAS
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {CminA CmaxA CminX CmaxX : ℝ}
    (hcA : NodeCap CminA CmaxA (N.C a₁)) (hcX : NodeCap CminX CmaxX (N.C x))  -- MEAS/MODEL
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
    ∀ t ∈ Icc (t₀ + S.PhiTG CmaxA CmaxX) t₁,
      S.Lvl (!b) (e t a₁) ∧ S.Lvl (!b) (e t x) := by
  obtain ⟨hδ, hVOLθ, hθVIL, hVIHθ, hθVOH⟩ := hS.band
  obtain ⟨hVOL, hK0b, hK0c, hK0d, hK0e⟩ := hS.K0
  have hsup := hS.K13_supply
  have hc₁n := contractOn_n hc (by simp) hL.core₁.pol_n
  have hc₁p := contractOn_p hc (by simp) hL.core₁.pol_p
  have ht₁n := contractOn_n hc (by simp) hL.tg₁.pol_n
  have ht₁p := contractOn_p hc (by simp) hL.tg₁.pol_p
  have ht₂n := contractOn_n hc (by simp) hL.tg₂.pol_n
  have ht₂p := contractOn_p hc (by simp) hL.tg₂.pol_p
  have hx : ∀ t ∈ Icc t₀ t₁, e t x ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht x (by simp)
  have ha₁ : ∀ t ∈ Icc t₀ t₁, e t a₁ ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht a₁ (by simp)
  have ha₂ : ∀ t ∈ Icc t₀ t₁, e t a₂ ∈ Icc 0 S.VDDmax := fun t ht => hrail t ht a₂ (by simp)
  have hcont : ∀ k, ContinuousOn (fun t => e t k) (Icc t₀ t₁) :=
    fun k => continuousOn_pi.1 he.continuousOn k
  have hd : ∀ k, ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun t => e t k) (N.vf (u t) (e t) k) (Ici t) t :=
    fun k t ht => hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) k
  have hCAc : Continuous (N.C a₁) := hcA.lipschitz.choose_spec.continuous
  have hCXc : Continuous (N.C x) := hcX.lipschitz.choose_spec.continuous
  -- `J` is the input gate's current into `x`, `K` the input core's current into `a₁`.
  obtain ⟨J, hJd⟩ : ∃ J : ℝ → ℝ, ∀ t, J t = hL.tg₁.J (u t) (e t) := ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℝ → ℝ, ∀ t,
      K t = -(N.fet c₁n).current (u t) (e t) - (N.fet c₁p).current (u t) (e t) :=
    ⟨_, fun _ => rfl⟩
  -- The feedback gate is off and leaks nothing, so only the input gate drives `x`.
  have hFx : ∀ t ∈ Icc t₀ t₁, N.F (u t) (e t) x = J t := by
    intro t ht
    have hJ2 := hL.tg₂.abs_J_le_Ioff hS ht₂n ht₂p (hoff₂ t ht).1 (hoff₂ t ht).2 (hx t ht)
      (ha₂ t ht)
    rw [hI.1, hI.2, add_zero, abs_nonpos_iff, IsTG.J] at hJ2
    have hT : ({t₁n, t₁p, t₂n, t₂p} : Finset (Fin N.nf)) = {t₁n, t₁p} ∪ {t₂n, t₂p} := by
      ext i
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    rw [Netlist.F_eq_sum_inflow hL.only_x, hT, Finset.sum_union hL.tg_disj,
      Finset.sum_pair hL.tg₁.ne, Finset.sum_pair hL.tg₂.ne, hJ2, add_zero, hJd]
    rfl
  -- What the input gate gives `x` it takes from `a₁`.
  have hFa : ∀ t, N.F (u t) (e t) a₁ = K t - J t := by
    intro t
    rw [hL.core₁.F_out, Finset.sum_pair hL.tg₁.ne, hL.tg₁.inflow_y, hKd, hJd]
    ring
  have dA : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun t => e t a₁) ((K t - J t) / N.C a₁ (e t a₁)) (Ici t) t :=
    fun t ht => (hd a₁ t ht).congr_deriv (by
      show N.F (u t) (e t) a₁ / N.C a₁ (e t a₁) = _
      rw [hFa])
  have dX : ∀ t ∈ Ico t₀ t₁,
      HasDerivWithinAt (fun t => e t x) (J t / N.C x (e t x)) (Ici t) t :=
    fun t ht => (hd x t ht).congr_deriv (by
      show N.F (u t) (e t) x / N.C x (e t x) = _
      rw [hFx t (Ico_subset_Icc_self ht)])
  -- Passivity: the input gate's current flows from the higher node of the pair to the lower.
  have hJp : ∀ t, e t x ≤ e t a₁ → 0 ≤ J t := fun t h => by
    rw [hJd]
    exact J_nonneg_of_le hL.tg₁ ht₁n.passive ht₁n.regular ht₁p.passive ht₁p.regular h
  have hJn : ∀ t, e t a₁ ≤ e t x → J t ≤ 0 := fun t h => by
    rw [hJd]
    exact J_nonpos_of_le hL.tg₁ ht₁n.passive ht₁n.regular ht₁p.passive ht₁p.regular h
  cases b
  · -- `b = false`: the input is low, the core pulls the pair up.
    have hr₁ : 0 < min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat :=
      hS.K13_leak.1.trans_lt hS.K5
    have hGp : 0 < S.pp.Gon :=
      pos_of_mul_pos_left (hr₁.trans_le (min_le_left _ _)) (by linarith)
    have hr₂ : 0 < min (S.pp.Gon * (S.NMH / 2)) S.pp.Isat :=
      lt_min (mul_pos hGp (by unfold Params.NMH; linarith)) (hr₁.trans_le (min_le_right _ _))
    have key := settle_hi (A := fun t => e t a₁) (X := fun t => e t x) (K := K) (J := J)
      (cA := N.C a₁) (cX := N.C x) (V := S.VDDmax) (VOH := S.VOH) (θH := S.θH)
      hCAc hCXc hcA.pos hcX.pos hcA.range hcX.range (hcont a₁) (hcont x) dA dX ha₁ hx
      (by linarith) ⟨by linarith, by linarith⟩ hr₁ hr₂ (fun t _ h => hJp t h)
      (fun t _ h => hJn t h) ?_ ?_
    · have hPhi : (CmaxA + CmaxX) * S.VDDmax / min (S.pp.Gon * (S.VDDmin - S.VOH)) S.pp.Isat
          + CmaxX * S.VDDmax / min (S.pp.Gon * (S.NMH / 2)) S.pp.Isat ≤
          S.PhiTG CmaxA CmaxX := le_max_right _ _
      intro t ht
      exact key t ⟨by linarith [ht.1], ht.2⟩
    · -- Below `V_OH` the core pushes in at least `I_rise` (K5).
      intro t ht hAV
      have ht' := Ico_subset_Icc_self ht
      have h := hL.core₁.Irise_le_core hS hc₁n hc₁p hVDD (hgnd t ht') (hvdd t ht') (hin t ht')
        ⟨(ha₁ t ht').1, hAV⟩
      unfold Params.Irise at h
      rw [hI.1, sub_zero] at h
      rw [hKd]
      exact h
    · -- With `a₁ ≥ V_OH` and `x < θ_H`, the gate's p-FET is on (K10).
      intro t ht hAV hXθ
      have ht' := Ico_subset_Icc_self ht
      have hXA : e t x ≤ e t a₁ := by linarith
      have h := hL.tg₁.J_ge_of_p_on hS ht₁n ht₁p (hon t ht').2 (le_max_of_le_right hAV)
        (hx t ht') (ha₁ t ht')
      rw [← hJd, abs_of_nonneg (hJp t hXA), abs_sub_comm,
        abs_of_pos (by linarith : 0 < e t a₁ - e t x)] at h
      refine le_trans (min_le_min (mul_le_mul_of_nonneg_left ?_ hGp.le) le_rfl) h
      unfold Params.NMH
      unfold Params.θH at hXθ
      linarith
  · -- `b = true`: the input is high, the core pulls the pair down. Reflect `v ↦ V_DD^max − v`.
    have hr₁ : 0 < min (S.pn.Gon * S.VOL) S.pn.Isat := hS.K13_leak.2.trans_lt hS.K6
    have hGn : 0 < S.pn.Gon := pos_of_mul_pos_left (hr₁.trans_le (min_le_left _ _)) hVOL.le
    have hr₂ : 0 < min (S.pn.Gon * (S.NML / 2)) S.pn.Isat :=
      lt_min (mul_pos hGn (by unfold Params.NML; linarith)) (hr₁.trans_le (min_le_right _ _))
    have dA' : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => S.VDDmax - e t a₁)
        ((-K t - -J t) / N.C a₁ (S.VDDmax - (S.VDDmax - e t a₁))) (Ici t) t :=
      fun t ht => ((dA t ht).const_sub S.VDDmax).congr_deriv (by rw [sub_sub_cancel]; ring)
    have dX' : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => S.VDDmax - e t x)
        (-J t / N.C x (S.VDDmax - (S.VDDmax - e t x))) (Ici t) t :=
      fun t ht => ((dX t ht).const_sub S.VDDmax).congr_deriv (by rw [sub_sub_cancel]; ring)
    have key := settle_hi (A := fun t => S.VDDmax - e t a₁) (X := fun t => S.VDDmax - e t x)
      (K := fun t => -K t) (J := fun t => -J t)
      (cA := fun v => N.C a₁ (S.VDDmax - v)) (cX := fun v => N.C x (S.VDDmax - v))
      (V := S.VDDmax) (VOH := S.VDDmax - S.VOL) (θH := S.VDDmax - S.θL)
      (hCAc.comp (continuous_const.sub continuous_id))
      (hCXc.comp (continuous_const.sub continuous_id)) hcA.pos hcX.pos
      (fun v => hcA.range _) (fun v => hcX.range _)
      (continuousOn_const.sub (hcont a₁)) (continuousOn_const.sub (hcont x)) dA' dX'
      (fun t ht => ⟨by linarith [(ha₁ t ht).2], by linarith [(ha₁ t ht).1]⟩)
      (fun t ht => ⟨by linarith [(hx t ht).2], by linarith [(hx t ht).1]⟩)
      (by linarith) ⟨by linarith, by linarith⟩ hr₁ hr₂
      (fun t _ h => neg_nonneg.2 (hJn t (by linarith)))
      (fun t _ h => neg_nonpos.2 (hJp t (by linarith))) ?_ ?_
    · have hPhi : (CmaxA + CmaxX) * S.VDDmax / min (S.pn.Gon * S.VOL) S.pn.Isat
          + CmaxX * S.VDDmax / min (S.pn.Gon * (S.NML / 2)) S.pn.Isat ≤
          S.PhiTG CmaxA CmaxX := le_max_left _ _
      intro t ht
      obtain ⟨h₁, h₂⟩ := key t ⟨by linarith [ht.1], ht.2⟩
      exact ⟨show e t a₁ ≤ S.θL by linarith, show e t x ≤ S.θL by linarith⟩
    · -- Above `V_OL` the core pulls out at least `I_fall` (K6).
      intro t ht hAV
      have ht' := Ico_subset_Icc_self ht
      have h := hL.core₁.core_le_neg_Ifall hS hc₁n hc₁p hVDD (hgnd t ht') (hvdd t ht')
        (hin t ht') ⟨by linarith, (ha₁ t ht').2⟩
      unfold Params.Ifall at h
      rw [hI.2, sub_zero] at h
      show _ ≤ -K t
      rw [hKd]
      linarith
    · -- With `a₁ ≤ V_OL` and `x > θ_L`, the gate's n-FET is on (K10).
      intro t ht hAV hXθ
      have ht' := Ico_subset_Icc_self ht
      have hAX : e t a₁ ≤ e t x := by linarith
      have h := hL.tg₁.J_ge_of_n_on hS ht₁n ht₁p (hon t ht').1
        (min_le_of_right_le (by linarith)) (hx t ht') (ha₁ t ht')
      rw [← hJd, abs_of_nonpos (hJn t hAX), abs_of_pos (by linarith : 0 < e t x - e t a₁)] at h
      refine le_trans (min_le_min (mul_le_mul_of_nonneg_left ?_ hGn.le) le_rfl) h
      unfold Params.NML
      unfold Params.θL at hXθ
      linarith

end Netlist.IsTGLatch

end AsmPhys
