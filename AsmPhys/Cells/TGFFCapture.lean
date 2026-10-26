import AsmPhys.Cells.TGFF
import AsmPhys.Cells.TGLatchSettle
import AsmPhys.Cells.Chain

/-!
# TGMS26: capture (FF2) and the flip-flop contract

Capture at edge `T' = t_{k+1}^r` (docs/SPIKE-FLIPFLOP.md §6), for bit `b` held on `D` through
`[T' − t_su, T' + t_h]`. In the low phase before `T'` the master settles to `b` (`settle`); through the
rising transition its latch agrees (`agree_invariant`); in the high phase it holds (`hold_invariant`)
while the delay chain carries `b` to `B2` and the slave settles to it; through the falling transition
the chain's contamination delay keeps `B2` valid and the slave agreeing; in the next low phase the
slave holds, so the state is in the hold tube at `τ = T' + t_cq^max`.

The timing conditions N1–N7 (`TGFFTiming`) are the plan's §8: the hold time covers the rise and the
clock inverter (N1), setup covers the master (N2) and the chain plus slave before the fall (N3), the
slave settles within the high phase (N4), the chain's contamination outlasts the fall (N5, the race),
`t_cq^max` reaches past the fall (N6), and `t_cq^min = 0` (N7).
-/

namespace AsmPhys

open Set

/-- `t_pd(INV) ≥ 0` (K0, K5). -/
private theorem tpdINV_nonneg_aux {S : Params} (hS : S.Consistent) {Cmax : ℝ} (hC : 0 ≤ Cmax) :
    0 ≤ S.tpdINV Cmax := by
  obtain ⟨hVOL, hK01, hK02, hK03, -⟩ := hS.K0
  exact mul_nonneg hC ((div_pos (by linarith) (sub_pos.2 hS.K5)).le.trans (le_max_left _ _))

/-- The pair settling time is positive: its pull-down bound is (K0, K6, K13). -/
private theorem phiTG_pos {S : Params} (hS : S.Consistent) {CA CX : ℝ} (hA : 0 < CA)
    (hX : 0 < CX) : 0 < S.PhiTG CA CX := by
  obtain ⟨hVOL, hK01, -, -, -⟩ := hS.K0
  have h1 : 0 < min (S.pn.Gon * S.VOL) S.pn.Isat := hS.K13_leak.2.trans_lt hS.K6
  have hK6 := lt_min_iff.1 h1
  have hGn : 0 < S.pn.Gon := pos_of_mul_pos_left hK6.1 hVOL.le
  have hV : 0 < S.VDDmax := by linarith [hS.K13_supply, hS.K0.2.2.2.2, hS.K0.2.2.2.1, hS.K0.2.2.1]
  have h2 : 0 < min (S.pn.Gon * (S.NML / 2)) S.pn.Isat :=
    lt_min (mul_pos hGn (half_pos (sub_pos.2 hK01))) hK6.2
  exact (add_pos (div_pos (mul_pos (add_pos hA hX) hV) h1) (div_pos (mul_pos hX hV) h2)).trans_le
    (le_max_left _ _)

/-- **Capture (FF2's core).** Without leakage, for every device family meeting the contracts and
every capacitance law in range: a trajectory that is on the rails with `CKB` high at `T' − t_su`, in
the low phase, with `D` valid `b` on `[T' − t_su, T' + t_h]`, is in the hold tube of `b` at
`T' + t_cq^max`. Nothing else about the state at `T' − t_su` is used. -/
theorem tgff_capture {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {dev : Fin 26 → ℝ → ℝ → ℝ → ℝ} {C : Fin 11 → ℝ → ℝ} {hC : ∀ k v, 0 < C k v}
    (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))  -- MODEL/MEAS
    {Cmin Cmax : Fin 11 → ℝ} (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (C k))       -- MEAS
    (ht : TGFFTiming S Cmin Cmax)                                                -- MODEL
    {VDD : ℝ} {u : ℝ → Fin 4 → ℝ} {e : ℝ → Fin 11 → ℝ} {a b : ℝ} {tg tr : ℕ → ℝ}
    (he : (tgff S dev C hC).IsTrajOn u e a b)
    (hrun : FFRun S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.gnd TGFF.vdd VDD u e a b tg tr)
    {k : ℕ} {d' : Bool} (hs : tr (k + 1) - S.tsu ∈ Icc a b)
    (hlow : tr k + 2 * S.tslew + S.thigh ≤ tr (k + 1) - S.tsu)
    (hrail : ∀ j, e (tr (k + 1) - S.tsu) j ∈ Icc 0 S.VDDmax)
    (hckb : S.VOH ≤ e (tr (k + 1) - S.tsu) TGFF.CKB)
    (hD : ∀ t ∈ Icc (tr (k + 1) - S.tsu) (tr (k + 1) + S.th), S.validIn d' (u t TGFF.d))
    (hτ : tr (k + 1) + S.tcqmax ∈ Icc a b) :
    e (tr (k + 1) + S.tcqmax) ∈ tgffHold S (fun t => u t TGFF.clk) d' (tr (k + 1) + S.tcqmax) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hK04⟩ := hS.K0
  obtain ⟨hslew, -, hhigh, -, -⟩ := hS.K14
  obtain ⟨N1, N2, N3, N4, N5, N6, -⟩ := ht
  have hVDD := hrun.vdd_mem
  have hcl := hrun.clockOK
  have hc := tgff_contractOn (S := S) (C := C) (hC := hC) hdev
  -- Delays are nonnegative and the pair settling times positive.
  have hCmax : ∀ j, 0 < Cmax j := fun j =>
    (hcap j).pos.trans_le (((hcap j).range 0).1.trans ((hcap j).range 0).2)
  have hpd : ∀ j, 0 ≤ S.tpdINV (Cmax j) := fun j => tpdINV_nonneg_aux hS (hCmax j).le
  have hΦm := (phiTG_pos hS (hCmax TGFF.A1) (hCmax TGFF.X)).le
  have hΦs := (phiTG_pos hS (hCmax TGFF.B) (hCmax TGFF.Z)).le
  have hσm : S.σm Cmax = S.PhiTG (Cmax TGFF.A1) (Cmax TGFF.X) + S.tpdINV (Cmax TGFF.Y) +
      S.tpdINV (Cmax TGFF.A2) := rfl
  have hσs : S.σs Cmax = S.PhiTG (Cmax TGFF.B) (Cmax TGFF.Z) + S.tpdINV (Cmax TGFF.Q) +
      S.tpdINV (Cmax TGFF.A4) := rfl
  have hpc := hpd TGFF.CKB
  have hpY := hpd TGFF.Y
  have hpA2 := hpd TGFF.A2
  have hpB1 := hpd TGFF.B1
  have hpB2 := hpd TGFF.B2
  have hpQ := hpd TGFF.Q
  have hpA4 := hpd TGFF.A4
  -- `EdgesOK` and K8 put `τ` before the next edge.
  have hτlt : tr (k + 1) + S.tcqmax < tr (k + 1 + 1) := by
    have h1 := hrun.edges.spacing (k + 1)
    have h2 := (hrun.edges.skew (k + 1)).2
    have h3 := (hrun.edges.skew (k + 1 + 1)).1
    linarith [hS.K8]
  -- Phase boundaries: `t₀ = T' − t_su`, `t₁ = t₀ + σ_m`, `r = R' + p_c`, `f = F'`, `l = L' + p_c`,
  -- `c = t₁ + δ_ch`, `s₀ = max r c`.
  obtain ⟨t₀, ht₀⟩ : ∃ t, t = tr (k + 1) - S.tsu := ⟨_, rfl⟩
  rw [← ht₀] at hs hlow hrail hckb hD
  obtain ⟨t₁, ht₁⟩ : ∃ t, t = t₀ + S.PhiTG (Cmax TGFF.A1) (Cmax TGFF.X) +
      S.tpdINV (Cmax TGFF.Y) + S.tpdINV (Cmax TGFF.A2) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ t, t = tr (k + 1) + S.tslew + S.tpdINV (Cmax TGFF.CKB) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ t, t = tr (k + 1) + S.tslew + S.thigh := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ t, t = tr (k + 1) + 2 * S.tslew + S.thigh + S.tpdINV (Cmax TGFF.CKB) :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτd⟩ : ∃ t, t = tr (k + 1) + S.tcqmax := ⟨_, rfl⟩
  rw [← hτd] at hτ hτlt ⊢
  obtain ⟨c, hcd⟩ : ∃ t, t = t₁ + S.tpdINV (Cmax TGFF.B1) + S.tpdINV (Cmax TGFF.B2) := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ t, t = max r c := ⟨_, rfl⟩
  have hrs₀ : r ≤ s₀ := by rw [hs₀]; exact le_max_left _ _
  have hcs₀ : c ≤ s₀ := by rw [hs₀]; exact le_max_right _ _
  -- N2–N4 and N6 order the boundaries.
  have h01 : t₀ ≤ t₁ := by linarith
  have h0r : t₀ ≤ r := by linarith
  have h1r : t₁ ≤ r := by linarith
  have hs₀f : s₀ + S.PhiTG (Cmax TGFF.B) (Cmax TGFF.Z) + S.tpdINV (Cmax TGFF.Q) +
      S.tpdINV (Cmax TGFF.A4) ≤ f := by
    have : s₀ ≤ f - (S.PhiTG (Cmax TGFF.B) (Cmax TGFF.Z) + S.tpdINV (Cmax TGFF.Q) +
        S.tpdINV (Cmax TGFF.A4)) := by
      rw [hs₀]
      exact max_le (by linarith) (by linarith)
    linarith
  have h0s₀ : t₀ ≤ s₀ := h0r.trans hrs₀
  have hrf : r ≤ f := by linarith
  have h0f : t₀ ≤ f := by linarith
  have hfl : f ≤ l := by linarith
  have hlτ : l ≤ τ := by linarith
  have h0l : t₀ ≤ l := by linarith
  have hτb : τ ≤ b := hτ.2
  have hlb : l ≤ b := hlτ.trans hτb
  have hfb : f ≤ b := hfl.trans hlb
  have hTb : tr (k + 1) ≤ b := by linarith
  have hrb : r ≤ b := hrf.trans hfb
  have h1b : t₁ ≤ b := h1r.trans hrb
  -- (0) Rails on `[t₀, b]`: only ground and supply touch channels.
  have hR : ∀ t ∈ Icc t₀ b, ∀ j, e t j ∈ Icc 0 S.VDDmax := by
    refine (tgff S dev C hC).rail_invariance (fun i => (hdev i).passive)
      (fun i => (hdev i).regular) (he.mono hs.1 le_rfl) (fun j hj t ht => ?_) hrail
    have hta : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    rcases (tgff_touchesChannel j).1 hj with rfl | rfl
    · rw [hrun.gnd_eq t hta]
      exact ⟨le_rfl, by linarith [hS.K13_supply]⟩
    · rw [hrun.vdd_eq t hta]
      exact ⟨by linarith [hVDD.1], hVDD.2⟩
  -- Run facts on any `[p, q] ⊆ [t₀, b]`.
  have hE : ∀ p q, t₀ ≤ p → q ≤ b → (tgff S dev C hC).IsTrajOn u e p q :=
    fun p q hp hq => he.mono (hs.1.trans hp) hq
  have hG : ∀ p q, t₀ ≤ p → q ≤ b → ∀ t ∈ Icc p q, u t TGFF.gnd = 0 :=
    fun p q hp hq t ht => hrun.gnd_eq t ⟨hs.1.trans (hp.trans ht.1), ht.2.trans hq⟩
  have hV : ∀ p q, t₀ ≤ p → q ≤ b → ∀ t ∈ Icc p q, u t TGFF.vdd = VDD :=
    fun p q hp hq t ht => hrun.vdd_eq t ⟨hs.1.trans (hp.trans ht.1), ht.2.trans hq⟩
  have hRr : ∀ p q, t₀ ≤ p → q ≤ b → ∀ t ∈ Icc p q, ∀ j, e t j ∈ Icc 0 S.VDDmax :=
    fun p q hp hq t ht => hR t ⟨hp.trans ht.1, ht.2.trans hq⟩
  -- (1) Clock: low on `[t₀, T']` and `[L', τ]`, high on `[R', F']`.
  have hclk₁ : ∀ t ∈ Icc t₀ (tr (k + 1)), u t TGFF.clk ≤ S.VIL :=
    fun t ht => hcl.low_between k t ⟨hlow.trans ht.1, ht.2⟩
  have hclkH : ∀ t ∈ Icc r f, S.VIH ≤ u t TGFF.clk :=
    fun t ht => hcl.high (k + 1) t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hclk₂ : ∀ t ∈ Icc l τ, u t TGFF.clk ≤ S.VIL :=
    fun t ht => hcl.low_between (k + 1) t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `CKB` is high on `[t₀, T']`, low on `[R' + p_c, F']`, high on `[L' + p_c, τ]` (THM L3.1).
  have hinv := tgff_inv_CKB (S := S) (dev := dev) (C := C) (hC := hC)
  have hckb₁ : ∀ t ∈ Icc t₀ (tr (k + 1)), S.VOH ≤ e t TGFF.CKB :=
    (hinv.propagation_rail hS (hdev 0) (hdev 1) (hcap TGFF.CKB).range hVDD
      (hE t₀ (tr (k + 1)) le_rfl hTb) (hG _ _ le_rfl hTb) (hV _ _ le_rfl hTb)
      (fun t ht => hRr _ _ le_rfl hTb t ht _) (x := false) hclk₁).2 t₀
      ⟨le_rfl, by linarith⟩ hckb
  have hckb₂ : ∀ t ∈ Icc r f, e t TGFF.CKB ≤ S.VOL := fun t ht =>
    (hinv.propagation_rail hS (hdev 0) (hdev 1) (hcap TGFF.CKB).range hVDD
      (hE (tr (k + 1) + S.tslew) f (by linarith) hfb) (hG _ _ (by linarith) hfb)
      (hV _ _ (by linarith) hfb) (fun t' ht' => hRr _ _ (by linarith) hfb t' ht' _) (x := true)
      (fun t' ht' => hcl.high (k + 1) t' ⟨ht'.1, by linarith [ht'.2]⟩)).1 t
      ⟨by linarith [ht.1], ht.2⟩
  have hckb₃ : ∀ t ∈ Icc l τ, S.VOH ≤ e t TGFF.CKB := fun t ht =>
    (hinv.propagation_rail hS (hdev 0) (hdev 1) (hcap TGFF.CKB).range hVDD
      (hE (tr (k + 1) + 2 * S.tslew + S.thigh) τ (by linarith) hτb) (hG _ _ (by linarith) hτb)
      (hV _ _ (by linarith) hτb) (fun t' ht' => hRr _ _ (by linarith) hτb t' ht' _)
      (x := false)
      (fun t' ht' => hcl.low_between (k + 1) t' ⟨ht'.1, by linarith [ht'.2]⟩)).1 t
      ⟨by linarith [ht.1], ht.2⟩
  -- (2) The master settles on `[t₀, t₁]`: TG1 on, TG2 off, `D` valid.
  have hM := tgff_master (S := S) (dev := dev) (C := C) (hC := hC)
  have hm₁ : latchAgree S d' TGFF.X TGFF.Y TGFF.A1 TGFF.A2 (e t₁) :=
    hM.settle hS (hc _) hI (hcap TGFF.A1) (hcap TGFF.X) (hcap TGFF.Y) (hcap TGFF.A2) hVDD
      (hE t₀ t₁ le_rfl h1b) (hG _ _ le_rfl h1b) (hV _ _ le_rfl h1b)
      (fun t ht j _ => hRr _ _ le_rfl h1b t ht j) (b := d')
      (fun t ht => hD t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => ⟨hK03.le.trans (hckb₁ t ⟨ht.1, by linarith [ht.2]⟩),
        hclk₁ t ⟨ht.1, by linarith [ht.2]⟩⟩)
      (fun t ht => ⟨hclk₁ t ⟨ht.1, by linarith [ht.2]⟩,
        hK03.le.trans (hckb₁ t ⟨ht.1, by linarith [ht.2]⟩)⟩)
      t₁ ⟨ht₁.ge, le_rfl⟩
  -- (3) Through the rise it agrees while `D` is valid (N1).
  have hm₂ : ∀ t ∈ Icc t₁ r, latchAgree S d' TGFF.X TGFF.Y TGFF.A1 TGFF.A2 (e t) :=
    hM.agree_invariant hS (hc _) hVDD (hE t₁ r h01 hrb) (hG _ _ h01 hrb) (hV _ _ h01 hrb)
      (fun t ht j _ => hRr _ _ h01 hrb t ht j)
      (fun t ht => hD t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hm₁
  -- (4) In the high phase TG1 is off and the master holds.
  have hm₃ : ∀ t ∈ Icc r f, latchHold S d' TGFF.X TGFF.Y TGFF.A2 (e t) :=
    hM.hold_invariant hS (hc _) hI hVDD (hE r f h0r hfb) (hG _ _ h0r hfb) (hV _ _ h0r hfb)
      (fun t ht j _ => hRr _ _ h0r hfb t ht j)
      (fun t ht => ⟨(hckb₂ t ht).trans hK01.le, hclkH t ht⟩) (hm₂ r ⟨h1r, le_rfl⟩).2
  have hY : ∀ t ∈ Icc t₁ f, S.validOut d' (e t TGFF.Y) := fun t ht =>
    (le_total t r).elim (fun h => (hm₂ t ⟨ht.1, h⟩).2.2.2) (fun h => (hm₃ t ⟨h, ht.2⟩).2.2)
  -- (5) The chain carries `b` to `B2` by `c = t₁ + δ_ch`.
  have hB1 : ∀ t ∈ Icc (t₁ + S.tpdINV (Cmax TGFF.B1)) f, S.validOut (!d') (e t TGFF.B1) :=
    ((tgff_inv_B1 (S := S) (dev := dev) (C := C) (hC := hC)).propagation_rail hS (hdev 12)
      (hdev 13) (hcap TGFF.B1).range hVDD (hE t₁ f h01 hfb) (hG _ _ h01 hfb) (hV _ _ h01 hfb)
      (fun t ht => hRr _ _ h01 hfb t ht _) (x := d')
      (fun t ht => hS.validIn_of_validOut (hY t ht))).1
  have hB2 : ∀ t ∈ Icc c f, S.validOut d' (e t TGFF.B2) := by
    have := ((tgff_inv_B2 (S := S) (dev := dev) (C := C) (hC := hC)).propagation_rail hS
      (hdev 14) (hdev 15) (hcap TGFF.B2).range hVDD
      (hE (t₁ + S.tpdINV (Cmax TGFF.B1)) f (by linarith) hfb) (hG _ _ (by linarith) hfb)
      (hV _ _ (by linarith) hfb) (fun t ht => hRr _ _ (by linarith) hfb t ht _) (x := !d')
      (fun t ht => hS.validIn_of_validOut (hB1 t ht))).1
    simp only [Bool.not_not] at this
    exact fun t ht => this t ⟨by linarith [ht.1], ht.2⟩
  -- (6) The slave settles on `[s₀, F']`: TG3 on, TG4 off, `B2` valid (N3, N4).
  have hSl := tgff_slave (S := S) (dev := dev) (C := C) (hC := hC)
  have hs₅ : latchAgree S d' TGFF.Z TGFF.Q TGFF.B TGFF.A4 (e f) :=
    hSl.settle hS (hc _) hI (hcap TGFF.B) (hcap TGFF.Z) (hcap TGFF.Q) (hcap TGFF.A4) hVDD
      (hE s₀ f h0s₀ hfb) (hG _ _ h0s₀ hfb) (hV _ _ h0s₀ hfb)
      (fun t ht j _ => hRr _ _ h0s₀ hfb t ht j) (b := d')
      (fun t ht => hS.validIn_of_validOut (hB2 t ⟨hcs₀.trans ht.1, ht.2⟩))
      (fun t ht => ⟨hclkH t ⟨hrs₀.trans ht.1, ht.2⟩,
        (hckb₂ t ⟨hrs₀.trans ht.1, ht.2⟩).trans hK01.le⟩)
      (fun t ht => ⟨(hckb₂ t ⟨hrs₀.trans ht.1, ht.2⟩).trans hK01.le,
        hclkH t ⟨hrs₀.trans ht.1, ht.2⟩⟩)
      f ⟨hs₀f, le_rfl⟩
  -- (7) Fall race: the chain's contamination keeps `B2` valid on `[F', L' + p_c]` (N5), so the
  -- slave keeps agreeing.
  have hB2c : ∀ t ∈ Icc f l, S.validIn d' (e t TGFF.B2) := fun t ht =>
    contamination_chain3 hS (tgff_inv_Y (S := S) (dev := dev) (C := C) (hC := hC)) tgff_inv_B1
      tgff_inv_B2 (hc _) (hcap TGFF.Y).pos (hcap TGFF.B1).pos (hcap TGFF.B2).pos
      (hcap TGFF.Y).range (hcap TGFF.B1).range (hcap TGFF.B2).range hVDD (hE f l h0f hlb)
      (hG _ _ h0f hlb) (hV _ _ h0f hlb) (fun t' ht' => hRr _ _ h0f hlb t' ht' TGFF.X)
      (fun t' ht' => ⟨hRr _ _ h0f hlb t' ht' _, hRr _ _ h0f hlb t' ht' _,
        hRr _ _ h0f hlb t' ht' _⟩)
      ⟨hY f ⟨by linarith, le_rfl⟩, hB1 f ⟨by linarith, le_rfl⟩, hB2 f ⟨by linarith, le_rfl⟩⟩ t
      ⟨ht.1, le_min ht.2 (by linarith [ht.2])⟩
  have hs₆ : ∀ t ∈ Icc f l, latchAgree S d' TGFF.Z TGFF.Q TGFF.B TGFF.A4 (e t) :=
    hSl.agree_invariant hS (hc _) hVDD (hE f l h0f hlb) (hG _ _ h0f hlb) (hV _ _ h0f hlb)
      (fun t ht j _ => hRr _ _ h0f hlb t ht j) hB2c hs₅
  -- (8) In the next low phase TG3 is off and the slave holds until `τ` (N6).
  have hs₇ : ∀ t ∈ Icc l τ, latchHold S d' TGFF.Z TGFF.Q TGFF.A4 (e t) :=
    hSl.hold_invariant hS (hc _) hI hVDD (hE l τ h0l hτb) (hG _ _ h0l hτb) (hV _ _ h0l hτb)
      (fun t ht j _ => hRr _ _ h0l hτb t ht j)
      (fun t ht => ⟨hclk₂ t ht, hK03.le.trans (hckb₃ t ht)⟩) (hs₆ l ⟨hfl, le_rfl⟩).2
  exact ⟨hR τ ⟨h0l.trans hlτ, hτb⟩, hckb₃ τ ⟨hlτ, le_rfl⟩, hs₇ τ ⟨hlτ, le_rfl⟩⟩

/-- **TGMS26 meets the flip-flop contract.** Without leakage, for every device family meeting the
per-polarity contracts, every capacitance law in range and every sheet satisfying N1–N7, the
transistor-level flip-flop satisfies FF1–FF2 with the time-independent hold tube `tgffHold`. -/
theorem tgff_contract {S : Params} (hS : S.Consistent)                -- THM (norm_num)
    (hI : S.pn.Ioff = 0 ∧ S.pp.Ioff = 0)                             -- MEAS (scope: no leakage)
    {dev : Fin 26 → ℝ → ℝ → ℝ → ℝ} {C : Fin 11 → ℝ → ℝ} {hC : ∀ k v, 0 < C k v}
    (hdev : ∀ i, FETContract (TGFF.pol i) (S.par (TGFF.pol i)) S.VDDmax (dev i))  -- MODEL/MEAS
    {Cmin Cmax : Fin 11 → ℝ} (hcap : ∀ k, NodeCap (Cmin k) (Cmax k) (C k))       -- MEAS
    (ht : TGFFTiming S Cmin Cmax) :                                              -- MODEL
    FFContract S (tgff S dev C hC) (.bdry TGFF.d) TGFF.clk TGFF.Q TGFF.gnd TGFF.vdd
      (tgffHold S) := by
  obtain ⟨hVOL, hK01, hK02, hK03, hK04⟩ := hS.K0
  obtain ⟨hslew, -, hhigh, -, -⟩ := hS.K14
  have hCmax : ∀ j, 0 < Cmax j := fun j =>
    (hcap j).pos.trans_le (((hcap j).range 0).1.trans ((hcap j).range 0).2)
  have hpd : ∀ j, 0 ≤ S.tpdINV (Cmax j) := fun j => tpdINV_nonneg_aux hS (hCmax j).le
  -- `t_su ≥ σ_m > 0` (N2), `t_h ≥ t_slew + p_c > 0` (N1), `t_cq^max > t_cq^min = 0` (N6, N7).
  have hσm : 0 < S.σm Cmax :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
      (phiTG_pos hS (hCmax TGFF.A1) (hCmax TGFF.X)) (hpd _)) (hpd _)
  have htsu : 0 < S.tsu := hσm.trans_le ht.N2
  have hpc := hpd TGFF.CKB
  have hN1 := ht.N1
  have hN6 := ht.N6
  have hN7 := ht.N7
  refine ⟨htsu.le, by linarith, hN7.ge, by rw [hN7]; linarith,
    tgff_ff1 hS hI hdev hcap ht.N6 ht.N7, ?_⟩
  intro VDD u e a b tg tr he hrun k d d' s hs hks hsk hes hb hD hτ
  -- FF1 from the hold state at `s` gives the rails and `CKB ≥ V_OH` at `T' − t_su`.
  have hs' : tr (k + 1) - S.tsu ∈ Icc a b := ⟨hs.1.trans hsk, by linarith⟩
  obtain ⟨h0r, h0c, -⟩ := (tgff_ff1 hS hI hdev hcap ht.N6 ht.N7 VDD u e a b tg tr he hrun k d s
    hs hks (by linarith) hes).1 _ hs' hsk (by linarith)
  exact tgff_capture hS hI hdev hcap ht he hrun hs' (by linarith) h0r h0c hD hτ

end AsmPhys
