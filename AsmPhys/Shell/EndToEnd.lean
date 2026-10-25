import Mathlib.MeasureTheory.Measure.Basic

/-!
# THM End-to-end — the probabilistic shell

The shell is pure measure theory. All physics, timing and refinement live in `hcore`, which
THM Core proves from H_cells, K0–K13, THM L4.1, THM L5.1 and the program spec: every run that
loads correctly (`G_init`), whose devices meet their contracts (`G_mfg`) and whose cycles all track
the model (`MF k`) has no bad cycle. The failure set then lies inside
`G_initᶜ ∪ G_mfgᶜ ∪ ⋃_k (MF_kᶜ ∩ G_mfg)`, and the union bound gives
`ε_init + ε_mfg + N·ε_cycle` with no independence assumption.

`μ` is applied as an outer measure, so no event needs to be measurable; "succeeds with probability
at least `1 − ε`" is the inner-measure reading.
-/

namespace AsmPhys

open MeasureTheory

/-- **THM End-to-end**: `μ{ω | ∃ k ≤ N, ω ∈ bad k} ≤ ε_init + ε_mfg + N·ε_cycle`. -/
theorem end_to_end {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ginit Gmfg : Set Ω) (MF bad : ℕ → Set Ω) (N : ℕ) (εinit εmfg εcycle : ENNReal)
    (hinit : μ Ginitᶜ ≤ εinit)                                        -- MEAS
    (hmfg : μ Gmfgᶜ ≤ εmfg)                                           -- MEAS
    (hcyc : ∀ k ∈ Finset.Icc 1 N, μ ((MF k)ᶜ ∩ Gmfg) ≤ εcycle)        -- MODEL
    (hcore : ∀ ω ∈ Ginit ∩ Gmfg, (∀ k ∈ Finset.Icc 1 N, ω ∈ MF k) →   -- THM (THM Core)
      ∀ k ≤ N, ω ∉ bad k) :
    μ {ω | ∃ k ≤ N, ω ∈ bad k} ≤ εinit + εmfg + N * εcycle := by
  have hsub : {ω | ∃ k ≤ N, ω ∈ bad k} ⊆
      Ginitᶜ ∪ Gmfgᶜ ∪ ⋃ k ∈ Finset.Icc 1 N, (MF k)ᶜ ∩ Gmfg := by
    rintro ω ⟨k, hk, hb⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff, not_or,
      not_not, not_exists, not_and] at h
    obtain ⟨⟨hi, hm⟩, hmf⟩ := h
    exact hcore ω ⟨hi, hm⟩ (fun j hj => by_contra fun h' => hmf j hj h' hm) k hk hb
  calc μ {ω | ∃ k ≤ N, ω ∈ bad k}
      ≤ μ (Ginitᶜ ∪ Gmfgᶜ ∪ ⋃ k ∈ Finset.Icc 1 N, (MF k)ᶜ ∩ Gmfg) := measure_mono hsub
    _ ≤ μ Ginitᶜ + μ Gmfgᶜ + ∑ k ∈ Finset.Icc 1 N, μ ((MF k)ᶜ ∩ Gmfg) :=
        (measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _))
    _ ≤ εinit + εmfg + ∑ _k ∈ Finset.Icc 1 N, εcycle :=
        add_le_add (add_le_add hinit hmfg) (Finset.sum_le_sum hcyc)
    _ = εinit + εmfg + N * εcycle := by simp [Finset.sum_const, nsmul_eq_mul]

end AsmPhys
