import AsmPhys.Cells.FlipFlop
import AsmPhys.Circuit.Rails
import AsmPhys.Circuit.WellPosed

/-!
# THM L3.3 — Buridan: setup and hold cannot be removed

Take any well-posed netlist meeting the flip-flop contract FF1–FF2, with `D` and a ClockOK clock
as boundary inputs, started at `s₀ = t_k^r + t_cq^max` in a hold state. Let `D_τ(t) = ρ(t − τ)`,
where `ρ` rises continuously from `0` (at `x ≤ 0`) to `V_DD` (at `x ≥ t_r`). Starting the rise at
`τ = s₀` makes `D` a valid `1` through the capture window, so `Q(t_obs) ≥ V_OH` by FF2 and FF1;
starting it at `τ = t_{k+1}^r + t_h` keeps `D` a valid `0`, so `Q(t_obs) ≤ V_OL`. The map
`τ ↦ Q(t_obs)` is continuous by THM L2.4, and the intermediate value theorem gives a `τ*` with
`Q(t_obs) = (V_IL + V_IH)/2`, which is not even a valid input level.

FF2 needs a trajectory that covers the hold window, so each trajectory is built on
`[s₀, max t_obs (t_{k+1}^r + t_h)]` and the chosen one is restricted to `[s₀, t_obs]` at the end.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- For `x₀ ≤ x₁`, a continuous `ρ : ℝ → ℝ` that is constant on `(-∞, x₀]` and on `[x₁, ∞)`
factors through the projection onto the compact `[x₀, x₁]`, so it is uniformly continuous. -/
lemma uniformContinuous_of_const_off_Icc {ρ : ℝ → ℝ} {x₀ x₁ : ℝ} (h : x₀ ≤ x₁)
    (hρ : Continuous ρ) (h₀ : ∀ x ≤ x₀, ρ x = ρ x₀) (h₁ : ∀ x, x₁ ≤ x → ρ x = ρ x₁) :
    UniformContinuous ρ := by
  have heq : ρ = (ρ ∘ Subtype.val) ∘ projIcc x₀ x₁ h := by
    funext x
    rcases le_total x x₀ with hx | hx
    · simp [projIcc_of_le_left h hx, h₀ x hx]
    rcases le_total x₁ x with hx' | hx'
    · simp [projIcc_of_right_le h hx', h₁ x hx']
    · simp [projIcc_of_mem h ⟨hx, hx'⟩]
  rw [heq]
  exact (CompactSpace.uniformContinuous_of_continuous (hρ.comp continuous_subtype_val)).comp
    (LipschitzWith.projIcc h).uniformContinuous

/-- If `|x − y| ≤ δ`, then updating coordinate `j` of `v` to `x` or to `y` gives points within `δ`
in the sup norm. -/
lemma norm_update_sub_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (j : ι)
    {x y δ : ℝ} (h : |x - y| ≤ δ) :
    ‖Function.update v j x - Function.update v j y‖ ≤ δ := by
  refine (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans h)).2 fun i => ?_
  rcases eq_or_ne i j with rfl | hi
  · simpa using h
  · simpa [Function.update_of_ne hi] using (abs_nonneg _).trans h

/-- FF2 then FF1. Take a trajectory on `[a, b]` with `t_{k+1}^r + t_h ≤ b` and a hold state at
`s ∈ [t_k^r + t_cq^max, t_{k+1}^r − t_su]`, with `D` `validIn d'` on the capture window
`[t_{k+1}^r − t_su, t_{k+1}^r + t_h]`. Then `Q` is `validOut d'` at every `t ∈ [a, b]` with
`t_{k+1}^r + t_cq^max ≤ t ≤ t_{k+2}^r + t_cq^min`. -/
theorem FFContract.validOut_of_capture {S : Params} (hS : S.Consistent) {N : Netlist n m}
    {dPin : Node n m} {clk gnd vdd : Fin m} {q : Fin n}
    {Hold : (ℝ → ℝ) → Bool → ℝ → Set (Fin n → ℝ)}
    (hff : FFContract S N dPin clk q gnd vdd Hold) {VDD : ℝ} {u : ℝ → Fin m → ℝ}
    {e : ℝ → Fin n → ℝ} {a b : ℝ} {tg tr : ℕ → ℝ} (he : N.IsTrajOn u e a b)
    (hrun : FFRun S N dPin clk gnd vdd VDD u e a b tg tr) {k : ℕ} {d d' : Bool} {s : ℝ}
    (hb : tr (k + 1) + S.th ≤ b) (hs : s ∈ Icc a b) (hks : tr k + S.tcqmax ≤ s)
    (hsk : s ≤ tr (k + 1) - S.tsu)
    (hes : e s ∈ Hold (fun t => u t clk) d s)
    (hD : ∀ t ∈ Icc (tr (k + 1) - S.tsu) (tr (k + 1) + S.th),
      S.validIn d' (pot (u t) (e t) dPin))
    {t : ℝ} (ht : t ∈ Icc a b) (ht₁ : tr (k + 1) + S.tcqmax ≤ t)
    (ht₂ : t ≤ tr (k + 2) + S.tcqmin) :
    S.validOut d' (e t q) := by
  have htsu := hff.tsu_nonneg
  have htcq : 0 ≤ S.tcqmax := hff.tcqmin_nonneg.trans hff.tcqmin_lt_tcqmax.le
  have hcq : tr (k + 1) + S.tcqmax ∈ Icc a b := ⟨by linarith [hs.1], ht₁.trans ht.2⟩
  have hlt : tr (k + 1) + S.tcqmax < tr (k + 1 + 1) := by
    have h1 := hrun.edges.spacing (k + 1)
    have h2 := (hrun.edges.skew (k + 1)).2
    have h3 := (hrun.edges.skew (k + 1 + 1)).1
    linarith [hS.K8]
  exact (hff.ff1 VDD u e a b tg tr he hrun (k + 1) d' _ hcq le_rfl hlt
    (hff.ff2 VDD u e a b tg tr he hrun k d d' s hs hks hsk hes hb hD hcq)).2 t ht ht₁ ht₂

/-- **THM L3.3** (Buridan). -/
theorem buridan {S : Params} (hS : S.Consistent)                      -- THM (norm_num)
    {N : Netlist n m} {jD clk gnd vdd : Fin m} {q : Fin n}
    {Hold : (ℝ → ℝ) → Bool → ℝ → Set (Fin n → ℝ)}
    (hff : FFContract S N (.bdry jD) clk q gnd vdd Hold)              -- H_cells (MODEL in v0)
    {Cmin Cmax : Fin n → ℝ}
    (hreg : ∀ i, Regular (N.fet i).I)                   -- MODEL (C2)
    (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (N.C k))                   -- MEAS range, MODEL law
    (hD : jD ≠ clk ∧ jD ≠ gnd ∧ jD ≠ vdd)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                    -- ENV
    {u₀ : ℝ → Fin m → ℝ} (hu₀ : Continuous u₀)                       -- ENV
    (hgnd : ∀ t, u₀ t gnd = 0) (hvdd : ∀ t, u₀ t vdd = VDD)           -- ENV
    {tg tr : ℕ → ℝ} (hedges : EdgesOK S tg tr)                        -- ENV
    (hclk : ClockOK S VDD (fun t => u₀ t clk) tr)                     -- ENV
    {ρ : ℝ → ℝ} {tρ : ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x ≤ 0, ρ x = 0)
    (hρ1 : ∀ x, tρ ≤ x → ρ x = VDD) (hρr : ∀ x, ρ x ∈ Icc 0 VDD)
    {k : ℕ} (hfit : tr k + S.tcqmax + tρ ≤ tr (k + 1) - S.tsu)
    {d₀ : Bool} {e₀ : Fin n → ℝ}
    (h0 : e₀ ∈ Hold (fun t => u₀ t clk) d₀ (tr k + S.tcqmax))
    {tobs : ℝ} (hobs : tobs ∈ Icc (tr (k + 1) + S.tcqmax) (tr (k + 2) + S.tcqmin)) :
    ∃ τ ∈ Icc (tr k + S.tcqmax) (tr (k + 1) + S.th), ∃ e : ℝ → Fin n → ℝ,
      N.IsTrajOn (fun t => Function.update (u₀ t) jD (ρ (t - τ))) e (tr k + S.tcqmax) tobs ∧
        e (tr k + S.tcqmax) = e₀ ∧ e tobs q = (S.VIL + S.VIH) / 2 := by
  obtain ⟨hOL, hOLIL, hILIH, hIHOH, hOHDD⟩ := hS.K0
  have htsu := hff.tsu_nonneg
  have hth := hff.th_nonneg
  have htcq : 0 ≤ S.tcqmax := hff.tcqmin_nonneg.trans hff.tcqmin_lt_tcqmax.le
  -- `ρ 0 = 0` and `ρ 0 = V_DD > 0` rule out `t_r ≤ 0`.
  have htρ : 0 < tρ := not_le.1 fun h => by
    have := (hρ0 0 le_rfl).symm.trans (hρ1 0 h)
    linarith [hVDD.1]
  set a := tr k + S.tcqmax with ha
  have hab : a ≤ tobs := by linarith [hobs.1]
  have hlohi : a ≤ tr (k + 1) + S.th := by linarith
  -- FF2 needs the trajectory to cover the hold window as well as `t_obs`.
  set b := max tobs (tr (k + 1) + S.th)
  have hobsb : tobs ≤ b := le_max_left _ _
  have hthb : tr (k + 1) + S.th ≤ b := le_max_right _ _
  have hab' : a ≤ b := hab.trans hobsb
  -- One trajectory `E τ` on `[a, b]` for each start `τ` of the rise.
  have hex : ∀ τ : ℝ, ∃ e, N.IsTrajOn (fun t => Function.update (u₀ t) jD (ρ (t - τ))) e a b ∧
      e a = e₀ := fun τ =>
    N.exists_isTrajOn hreg hcap
      (by fun_prop : Continuous fun t => Function.update (u₀ t) jD (ρ (t - τ))).continuousOn hab' e₀
  choose E hE hE0 using hex
  -- The rise on `D` leaves the clock, ground and supply pins alone.
  have hclkfun : ∀ τ, (fun t => Function.update (u₀ t) jD (ρ (t - τ)) clk) = fun t => u₀ t clk :=
    fun τ => funext fun t => Function.update_of_ne hD.1.symm _ _
  have hrun : ∀ τ, FFRun S N (.bdry jD) clk gnd vdd VDD
      (fun t => Function.update (u₀ t) jD (ρ (t - τ))) (E τ) a b tg tr := fun τ =>
    { vdd_mem := hVDD
      gnd_eq := fun t _ => (Function.update_of_ne hD.2.1.symm _ _).trans (hgnd t)
      vdd_eq := fun t _ => (Function.update_of_ne hD.2.2.symm _ _).trans (hvdd t)
      edges := hedges
      clockOK := by rw [hclkfun]; exact hclk
      d_rail := fun t _ => by simpa only [pot_bdry, Function.update_self] using hρr (t - τ) }
  -- FF2 then FF1: a `D` that is `validIn d'` through the capture window gives `validOut d'`.
  have hQ : ∀ τ (d' : Bool), (∀ t ∈ Icc (tr (k + 1) - S.tsu) (tr (k + 1) + S.th),
      S.validIn d' (ρ (t - τ))) → S.validOut d' (E τ tobs q) := by
    intro τ d' hd'
    refine hff.validOut_of_capture hS (hE τ) (hrun τ) (s := a) (d := d₀) hthb ⟨le_rfl, hab'⟩
      le_rfl (by linarith) ?_ (fun t ht => ?_) ⟨hab, hobsb⟩ hobs.1 hobs.2
    · rw [hclkfun, hE0]
      exact h0
    · simpa only [pot_bdry, Function.update_self] using hd' t ht
  have hlo : S.VOH ≤ E a tobs q := hQ a true fun t ht => by
    show S.VIH ≤ ρ (t - a)
    rw [hρ1 _ (by linarith [ht.1])]
    linarith [hVDD.1]
  have hhi : E (tr (k + 1) + S.th) tobs q ≤ S.VOL := hQ _ false fun t ht => by
    show ρ (t - (tr (k + 1) + S.th)) ≤ S.VIL
    rw [hρ0 _ (by linarith [ht.2])]
    linarith
  -- THM L2.4 with equal initial states: `Q(t_obs)` moves by at most `C·δ` when the rise moves by
  -- at most `δ` in the sup norm.
  have hkey : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ τ' δ, (∀ x, |ρ (x - τ') - ρ (x - τ)| ≤ δ) →
      |E τ' tobs q - E τ tobs q| ≤ C * δ := by
    obtain ⟨K, Lu, hdep⟩ := N.exists_lipschitz_dependence hreg hcap
    refine ⟨Lu * (tobs - a) * Real.exp (K * (tobs - a)),
      mul_nonneg (mul_nonneg Lu.coe_nonneg (sub_nonneg.2 hab)) (Real.exp_pos _).le,
      fun τ τ' δ hδ => ?_⟩
    have h := hdep (hE τ') (hE τ) (fun t _ => norm_update_sub_update_le _ _ (hδ t)) tobs
      ⟨hab, hobsb⟩
    rw [hE0, hE0, sub_self, norm_zero, mul_zero, zero_add] at h
    calc |E τ' tobs q - E τ tobs q| = ‖(E τ' tobs - E τ tobs) q‖ := by
          rw [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖E τ' tobs - E τ tobs‖ := norm_le_pi_norm _ q
      _ ≤ _ := h
  -- `ρ` is uniformly continuous, so `τ ↦ Q(t_obs)` is continuous.
  have hcont : Continuous fun τ => E τ tobs q := by
    obtain ⟨C, hC0, hC⟩ := hkey
    have hρu : UniformContinuous ρ := uniformContinuous_of_const_off_Icc htρ.le hρ
      (fun x hx => (hρ0 x hx).trans (hρ0 0 le_rfl).symm)
      (fun x hx => (hρ1 x hx).trans (hρ1 tρ le_rfl).symm)
    have hC1 : 0 < C + 1 := by linarith
    refine Metric.continuous_iff.2 fun τ ε hε => ?_
    obtain ⟨η, hη, hηρ⟩ := Metric.uniformContinuous_iff.1 hρu (ε / (C + 1)) (div_pos hε hC1)
    refine ⟨η, hη, fun τ' hτ' => ?_⟩
    rw [Real.dist_eq]
    refine (hC τ τ' (ε / (C + 1)) fun x => ?_).trans_lt ?_
    · rw [← Real.dist_eq]
      refine (hηρ ?_).le
      rw [Real.dist_eq] at hτ' ⊢
      rwa [show x - τ' - (x - τ) = -(τ' - τ) by ring, abs_neg]
    · rw [mul_div_assoc', div_lt_iff₀ hC1]
      nlinarith
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc' hlohi hcont.continuousOn
    (show (S.VIL + S.VIH) / 2 ∈ Icc (E (tr (k + 1) + S.th) tobs q) (E a tobs q) from
      ⟨by linarith, by linarith⟩)
  exact ⟨τ, hτ, E τ, (hE τ).mono le_rfl hobsb, hE0 τ, hfτ⟩

end AsmPhys
