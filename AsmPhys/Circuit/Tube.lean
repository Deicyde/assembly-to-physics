import AsmPhys.Circuit.Rails

/-!
# Invariant tubes with strictly inward faces

Hold tubes of storage circuits are boxes cut out by finitely many one-sided constraints
`g_i(t) ≤ 0`, typically `g_i(t) = ±(e_k(t) − θ)`. If at every time where all constraints hold and
constraint `i` is tight, `g_i` has a strictly negative right derivative, then no constraint can be
the first to fail, so a family that starts inside stays inside. No Lipschitz bound is needed,
because the faces are strictly inward.
-/

namespace AsmPhys

open Set Filter Topology

/-- Strict invariance of finitely many one-sided constraints `g i ≤ 0`. -/
theorem invariant_of_strict {ι : Type*} [Finite ι] {g g' : ι → ℝ → ℝ} {a b : ℝ}
    (hg : ∀ i, ContinuousOn (g i) (Icc a b))
    (hg' : ∀ i, ∀ t ∈ Ico a b, HasDerivWithinAt (g i) (g' i t) (Ici t) t)
    (ha : ∀ i, g i a ≤ 0)
    (hface : ∀ t ∈ Ico a b, (∀ j, g j t ≤ 0) → ∀ i, g i t = 0 → g' i t < 0) :
    ∀ t ∈ Icc a b, ∀ i, g i t ≤ 0 := by
  set s := {t | ∀ i, g i t ≤ 0}
  have hs : IsClosed (s ∩ Icc a b) := by
    have : s ∩ Icc a b = Icc a b ∩ ⋂ i, (Icc a b ∩ g i ⁻¹' Iic 0) := by
      ext t
      simp only [s, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
      exact ⟨fun h => ⟨h.2, fun i => ⟨h.2, h.1 i⟩⟩, fun h => ⟨fun i => (h.2 i).2, h.1⟩⟩
    rw [this]
    exact isClosed_Icc.inter
      (isClosed_iInter fun i => (hg i).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  refine fun t ht => hs.Icc_subset_of_forall_exists_gt (s := s) ha ?_ ht
  rintro t ⟨hts, htI⟩ y hy
  have hev : ∀ᶠ z in 𝓝[>] t, ∀ i, g i z ≤ 0 := by
    refine eventually_all.2 fun i => ?_
    rcases (hts i).lt_or_eq with hlt | heq
    · exact nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem htI)
        (((hg i t (Ico_subset_Icc_self htI)).eventually (Iio_mem_nhds hlt)).mono
          fun z hz => le_of_lt hz)
    · have hi := hface t htI hts i heq
      filter_upwards [(hg' i t htI).Ioi_of_Ici.limsup_slope_le' (lt_irrefl t) hi,
        self_mem_nhdsWithin] with z hz htz
      rw [slope_def_field, div_lt_iff₀ (sub_pos.2 htz), zero_mul, heq] at hz
      linarith
  obtain ⟨z, hz, hzI⟩ := (hev.and (Ioc_mem_nhdsGT hy)).exists
  exact ⟨z, hz, hzI⟩

/-- Band maximum principle: as `max_principle`, but the face condition is needed only while the
largest component is within `δ` above `V`. Storage nodes of latches have faces that are only
non-strict (`F ≤ 0`), and their tubes are cut out by comparing a component with the largest one. -/
theorem max_principle_band {ι : Type*} [Fintype ι] {x x' : ℝ → ι → ℝ} {a b V δ : ℝ}
    (hδ : 0 < δ) (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t) (ha : ∀ k, x a k ≤ V)
    (hface : ∀ t ∈ Ico a b, ∀ k, x t k ∈ Icc V (V + δ) → (∀ j, x t j ≤ x t k) → x' t k ≤ 0) :
    ∀ t ∈ Icc a b, ∀ k, x t k ≤ V := by
  have key : ∀ ε > 0, ε * (b - a) ≤ δ → ∀ t ∈ Icc a b, ∀ k, x t k ≤ V + ε * (t - a) := by
    intro ε hε hεδ
    have hB : Continuous fun t : ℝ => V + ε * (t - a) := by fun_prop
    set s := {t | ∀ k, x t k ≤ V + ε * (t - a)}
    have hs : IsClosed (s ∩ Icc a b) := by
      rw [inter_comm]
      exact (hx.prodMk (continuous_pi fun _ => hB).continuousOn).preimage_isClosed_of_isClosed
        isClosed_Icc (isClosed_le continuous_fst continuous_snd)
    refine fun t ht => hs.Icc_subset_of_forall_exists_gt (fun k => by simpa using ha k) ?_ ht
    rintro t ⟨hts, htI⟩ y hy
    have hev : ∀ᶠ z in 𝓝[>] t, ∀ k, x z k ≤ V + ε * (z - a) := by
      refine eventually_all.2 fun k => ?_
      rcases (hts k).lt_or_eq with hlt | heq
      · have hxk : ContinuousWithinAt (fun z => x z k) (Icc a b) t :=
          continuousOn_pi.1 hx k t (Ico_subset_Icc_self htI)
        exact nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem htI)
          ((Filter.Tendsto.eventually_lt hxk hB.continuousWithinAt hlt).mono fun z hz => hz.le)
      · -- `t < b` and `ε (b − a) ≤ δ` keep the barrier below `V + δ`.
        have hεt : ε * (t - a) ≤ δ :=
          (mul_le_mul_of_nonneg_left (by linarith [htI.2]) hε.le).trans hεδ
        have hk := hface t htI k
          ⟨by rw [heq]; exact le_add_of_nonneg_right (mul_nonneg hε.le (sub_nonneg.2 htI.1)),
            by rw [heq]; linarith⟩
          fun j => (hts j).trans heq.ge
        have hBd : HasDerivAt (fun z => V + ε * (z - a)) ε t :=
          (((hasDerivAt_id t).sub_const a).const_mul ε |>.const_add V).congr_deriv (mul_one ε)
        have hd : HasDerivWithinAt (fun z => x z k - (V + ε * (z - a))) (x' t k - ε) (Ici t) t :=
          (hasDerivWithinAt_pi.1 (hx' t htI) k).sub hBd.hasDerivWithinAt
        filter_upwards [hd.Ioi_of_Ici.limsup_slope_le' (lt_irrefl t)
          (by linarith : x' t k - ε < 0), self_mem_nhdsWithin] with z hz htz
        rw [slope_def_field, div_lt_iff₀ (sub_pos.2 htz)] at hz
        simp only [zero_mul] at hz
        linarith
    obtain ⟨z, hz, hzI⟩ := (hev.and (Ioc_mem_nhdsGT hy)).exists
    exact ⟨z, hz, hzI⟩
  intro t ht k
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hm : 0 < min η δ := lt_min hη hδ
  have hb : 0 < b - a + 1 := by linarith [ht.1, ht.2]
  -- `ε = min(η, δ)/(b − a + 1)` satisfies `ε (b − a) ≤ min(η, δ)`.
  have hεb : min η δ / (b - a + 1) * (b - a) ≤ min η δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    nlinarith
  have hε : 0 < min η δ / (b - a + 1) := div_pos hm hb
  have h1 := key _ hε (hεb.trans (min_le_right _ _)) t ht k
  have h2 : min η δ / (b - a + 1) * (t - a) ≤ η :=
    (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hε.le).trans (hεb.trans (min_le_left _ _))
  linarith

end AsmPhys
