import AsmPhys.Circuit.Netlist
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# THM L2.3 and THM L2.5 — Rail invariance and the slew bound

Rail invariance is a discrete maximum principle. At a time when a state node holds the largest
state potential and that potential is at least `V`, every channel terminal at the node sees a
potential no higher than its own, so passivity (C1) and `I(v_g, v, v) = 0` make every channel
current flow out of it and its potential cannot rise. Symmetrically for the smallest potential
and `0`. This needs only C1, continuity of the devices (from C2) and positive capacitance; no
Lipschitz bound on the field is used.

The slew bound follows from C6 once rail invariance keeps every terminal on the rails.
-/

namespace AsmPhys

open Set Filter Topology

/-- C2 makes a device function jointly continuous. -/
theorem Regular.continuous {I : ℝ → ℝ → ℝ → ℝ} (h : Regular I) :
    Continuous fun x : ℝ × ℝ × ℝ => I x.1 x.2.1 x.2.2 :=
  h.lipschitz.choose_spec.continuous

/-- Derived clause (THM, from C1 and the continuity in C2): `I(v_g, v, v) = 0`. -/
theorem Passive.apply_self {I : ℝ → ℝ → ℝ → ℝ} (hP : Passive I)
    (hR : Regular I) (g v : ℝ) : I g v v = 0 := by
  have hc : Continuous fun d => I g d v :=
    hR.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  refine le_antisymm ?_ ?_
  · refine le_of_tendsto ((hc.tendsto v).mono_left nhdsWithin_le_nhds : Tendsto _ (𝓝[<] v) _) ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact nonpos_of_mul_nonneg_right (hP g d v) (sub_neg.2 hd)
  · refine ge_of_tendsto ((hc.tendsto v).mono_left nhdsWithin_le_nhds : Tendsto _ (𝓝[>] v) _) ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact nonneg_of_mul_nonneg_right (hP g d v) (sub_pos.2 hd)

/-- With the drain not above the source, a passive regular device conducts from source to
drain: `I ≤ 0`. -/
theorem Passive.nonpos_of_le {I : ℝ → ℝ → ℝ → ℝ} (hP : Passive I)
    (hR : Regular I) {g d s : ℝ} (h : d ≤ s) : I g d s ≤ 0 := by
  rcases h.lt_or_eq with h | rfl
  · exact nonpos_of_mul_nonneg_right (hP g d s) (sub_neg.2 h)
  · exact (hP.apply_self hR g _).le

/-- With the source not above the drain, a passive regular device conducts from drain to
source: `0 ≤ I`. -/
theorem Passive.nonneg_of_le {I : ℝ → ℝ → ℝ → ℝ} (hP : Passive I)
    (hR : Regular I) {g d s : ℝ} (h : s ≤ d) : 0 ≤ I g d s := by
  rcases h.lt_or_eq with h | rfl
  · exact nonneg_of_mul_nonneg_right (hP g d s) (sub_pos.2 h)
  · exact (hP.apply_self hR g _).ge

/-- Discrete maximum principle for a finite family of right-differentiable functions: if the
family starts at most `V`, and whenever a component is the largest and at least `V` its right
derivative is nonpositive, then every component stays at most `V` on `[a, b]`. -/
theorem max_principle {ι : Type*} [Fintype ι] {x x' : ℝ → ι → ℝ} {a b V : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t)
    (ha : ∀ k, x a k ≤ V)
    (hface : ∀ t ∈ Ico a b, ∀ k, V ≤ x t k → (∀ j, x t j ≤ x t k) → x' t k ≤ 0) :
    ∀ t ∈ Icc a b, ∀ k, x t k ≤ V := by
  have key : ∀ ε > 0, ∀ t ∈ Icc a b, ∀ k, x t k ≤ V + ε * (t - a) := by
    intro ε hε
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
      · have hk := hface t htI k
          (by rw [heq]; exact le_add_of_nonneg_right (mul_nonneg hε.le (sub_nonneg.2 htI.1)))
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
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hta : 0 ≤ t - a := sub_nonneg.2 ht.1
  have h1 := key (δ / (t - a + 1)) (div_pos hδ (by linarith)) t ht k
  have h2 : δ / (t - a + 1) * (t - a) ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

namespace Netlist

variable {n m : ℕ} (N : Netlist n m)

/-- Bounds on the state potentials and on the channel-touching boundary potentials bound every
drain and source potential. -/
theorem pot_terminal_mem {u : Fin m → ℝ} {e : Fin n → ℝ} {S : Set ℝ} (he : ∀ k, e k ∈ S)
    (hu : ∀ j, N.TouchesChannel j → u j ∈ S) (i : Fin N.nf) :
    pot u e (N.fet i).d ∈ S ∧ pot u e (N.fet i).s ∈ S := by
  constructor
  · cases hd : (N.fet i).d with
    | state k => exact he k
    | bdry j => exact hu j ⟨i, .inl hd⟩
  · cases hs : (N.fet i).s with
    | state k => exact he k
    | bdry j => exact hu j ⟨i, .inr hs⟩

/-- If no drain or source potential exceeds `e k`, the net channel current into `k` is
nonpositive. -/
theorem F_nonpos_of_terminals_le (hpass : ∀ i, Passive (N.fet i).I)
    (hreg : ∀ i, Regular (N.fet i).I) {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n}
    (hd : ∀ i, pot u e (N.fet i).d ≤ e k) (hs : ∀ i, pot u e (N.fet i).s ≤ e k) :
    N.F u e k ≤ 0 := by
  unfold F FET.current
  refine Finset.sum_nonpos fun i _ => ?_
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact (hpass i).nonpos_of_le (hreg i) (hd i)
  · rw [h2, pot_state, zero_sub, neg_nonpos]
    exact (hpass i).nonneg_of_le (hreg i) (hs i)
  · simp

/-- If no drain or source potential is below `e k`, the net channel current into `k` is
nonnegative. -/
theorem F_nonneg_of_le_terminals (hpass : ∀ i, Passive (N.fet i).I)
    (hreg : ∀ i, Regular (N.fet i).I) {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n}
    (hd : ∀ i, e k ≤ pot u e (N.fet i).d) (hs : ∀ i, e k ≤ pot u e (N.fet i).s) :
    0 ≤ N.F u e k := by
  unfold F FET.current
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact (hpass i).nonneg_of_le (hreg i) (hd i)
  · rw [h2, pot_state, zero_sub, neg_nonneg]
    exact (hpass i).nonpos_of_le (hreg i) (hs i)
  · simp

/-- If every channel current is at most `Imax` in size, then `|F_k| ≤ n_k · Imax`. -/
theorem abs_F_le {u : Fin m → ℝ} {e : Fin n → ℝ} {Imax : ℝ}
    (h : ∀ i, |(N.fet i).current u e| ≤ Imax) (k : Fin n) :
    |N.F u e k| ≤ N.nChan k * Imax := by
  unfold F
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
          (if (N.fet i).d = .state k then (N.fet i).current u e else 0)|
      ≤ ∑ i, ((if (N.fet i).s = .state k then Imax else 0) +
          (if (N.fet i).d = .state k then Imax else 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := h i
        have h0 := abs_nonneg ((N.fet i).current u e)
        split_ifs <;>
          simp only [sub_self, sub_zero, zero_sub, abs_neg, abs_zero, add_zero, zero_add] <;>
          linarith
    _ = N.nChan k * Imax := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
          Finset.sum_const]
        simp only [nChan, nsmul_eq_mul, Nat.cast_add]
        ring

/-- **THM L2.3** (rail invariance): if every device satisfies C1 and C2, every boundary node that
touches a channel stays in `[0, V]`, and the initial state lies in `[0, V]ⁿ`, then the trajectory
stays in `[0, V]ⁿ` on `[a, b]`. Gate-only boundary nodes are unconstrained. -/
theorem rail_invariance
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, N.TouchesChannel j → ∀ t ∈ Icc a b, u t j ∈ Icc 0 V)   -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, ∀ k, e t k ∈ Icc 0 V := by
  have hut : ∀ t ∈ Ico a b, ∀ j, N.TouchesChannel j → u t j ∈ Icc 0 V :=
    fun t ht j hj => hu j hj t (Ico_subset_Icc_self ht)
  intro t ht k
  refine ⟨?_, ?_⟩
  · have := max_principle (x := fun t => -e t) (x' := fun t => -N.vf (u t) (e t)) (V := 0)
      he.continuousOn.neg (fun t ht => (he.hasDerivWithinAt t ht).neg)
      (fun k => neg_nonpos.2 (h0 k).1) ?_ t ht k
    · simpa using this
    intro t ht k hk hmin
    simp only [Pi.neg_apply, neg_nonneg, neg_le_neg_iff, neg_nonpos] at hk hmin ⊢
    have hS := N.pot_terminal_mem (u := u t) (S := Ici (e t k)) hmin
      (fun j hj => hk.trans (hut t ht j hj).1)
    exact div_nonneg (N.F_nonneg_of_le_terminals hpass hreg (fun i => (hS i).1)
      (fun i => (hS i).2)) (N.C_pos k _).le
  · refine max_principle he.continuousOn he.hasDerivWithinAt (fun k => (h0 k).2) ?_ t ht k
    intro t ht k hk hmax
    have hS := N.pot_terminal_mem (u := u t) (S := Iic (e t k)) hmax
      (fun j hj => (hut t ht j hj).2.trans hk)
    exact div_nonpos_of_nonpos_of_nonneg (N.F_nonpos_of_terminals_le hpass hreg
      (fun i => (hS i).1) (fun i => (hS i).2)) (N.C_pos k _).le

/-- **THM L2.5** (slew bound): if all boundary potentials lie in `Rail = [0, Vmax]` and the initial
state does too, then `|ė_k(t)| ≤ n_k · I_max / C_k^min` on `[a, b]`, where `n_k` is the number of
channel terminals at node `k`. Uses C6 and THM L2.3. -/
theorem slew_bound {Cmin : Fin n → ℝ} {Imax Vmax : ℝ}
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hbd : ∀ i, BoundedOnRail Imax Vmax (N.fet i).I)       -- MEAS (C6)
    (hCmin : ∀ k, 0 < Cmin k)                              -- MEAS
    (hC : ∀ k v, Cmin k ≤ N.C k v)                         -- MEAS
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, ∀ t ∈ Icc a b, u t j ∈ Icc 0 Vmax)          -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 Vmax) :
    ∀ t ∈ Icc a b, ∀ k, |N.vf (u t) (e t) k| ≤ N.nChan k * Imax / Cmin k := by
  intro t ht k
  have hrail := N.rail_invariance hpass hreg he (fun j _ t ht => hu j t ht) h0
  have hpot : ∀ nd, pot (u t) (e t) nd ∈ Icc 0 Vmax := fun nd => by
    cases nd with
    | state k => exact hrail t ht k
    | bdry j => exact hu j t ht
  have hF := N.abs_F_le (u := u t) (e := e t) (fun i => hbd i _ _ _ (hpot _) (hpot _) (hpot _)) k
  show |N.F (u t) (e t) k / N.C k (e t k)| ≤ N.nChan k * Imax / Cmin k
  rw [abs_div, abs_of_pos (N.C_pos k _)]
  calc |N.F (u t) (e t) k| / N.C k (e t k) ≤ |N.F (u t) (e t) k| / Cmin k :=
        div_le_div_of_nonneg_left (abs_nonneg _) (hCmin k) (hC k _)
    _ ≤ N.nChan k * Imax / Cmin k := div_le_div_of_nonneg_right hF (hCmin k).le

/-- **THM L2.5**, integrated form: each state potential is Lipschitz in time on `[a, b]` with
constant `n_k · I_max / C_k^min`. -/
theorem slew_lipschitz {Cmin : Fin n → ℝ} {Imax Vmax : ℝ}
    (hpass : ∀ i, Passive (N.fet i).I)                     -- MODEL (C1)
    (hreg : ∀ i, Regular (N.fet i).I)        -- MODEL (C2)
    (hbd : ∀ i, BoundedOnRail Imax Vmax (N.fet i).I)       -- MEAS (C6)
    (hCmin : ∀ k, 0 < Cmin k)                              -- MEAS
    (hC : ∀ k v, Cmin k ≤ N.C k v)                         -- MEAS
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hu : ∀ j, ∀ t ∈ Icc a b, u t j ∈ Icc 0 Vmax)          -- ENV
    (h0 : ∀ k, e a k ∈ Icc 0 Vmax) :
    ∀ k, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |e t k - e s k| ≤ N.nChan k * Imax / Cmin k * |t - s| := by
  intro k
  have hb := N.slew_bound hpass hreg hbd hCmin hC he hu h0
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      |e t k - e s k| ≤ N.nChan k * Imax / Cmin k * (t - s) := by
    intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun z => e z k)
      (f' := fun z => N.vf (u z) (e z) k) (C := N.nChan k * Imax / Cmin k)
      ((continuousOn_pi.1 he.continuousOn k).mono hsub)
      (fun z hz => hasDerivWithinAt_pi.1
        (he.hasDerivWithinAt z ⟨hs.1.trans hz.1, hz.2.trans_le ht.2⟩) k)
      (fun z hz => (Real.norm_eq_abs _).trans_le (hb z (hsub (Ico_subset_Icc_self hz)) k))
      t ⟨hst, le_rfl⟩
    rwa [Real.norm_eq_abs] at this
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.2 hst)]
    exact key s hs t ht hst
  · rw [abs_sub_comm, abs_sub_comm t s, abs_of_nonneg (sub_nonneg.2 hts)]
    exact key t ht s hs hts

/-! ### Local versions

A cell theorem constrains only the cell's own nodes and its neighbours, so it needs rail
invariance and the slew bound for a set of nodes, with hypotheses on the devices at those nodes
alone. -/

/-- If every drain or source across a channel from `k` is at most `e k`, the net channel current
into `k` is nonpositive. Only the devices with a channel terminal at `k` need C1 and C2. -/
theorem F_nonpos_of_neighbours_le {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n}
    (hpass : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → Passive (N.fet i).I)
    (hreg : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → Regular (N.fet i).I)
    (hd : ∀ i, (N.fet i).s = .state k → pot u e (N.fet i).d ≤ e k)
    (hs : ∀ i, (N.fet i).d = .state k → pot u e (N.fet i).s ≤ e k) :
    N.F u e k ≤ 0 := by
  unfold F FET.current
  refine Finset.sum_nonpos fun i _ => ?_
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact (hpass i (.inr h1)).nonpos_of_le (hreg i (.inr h1)) (hd i h1)
  · rw [h2, pot_state, zero_sub, neg_nonpos]
    exact (hpass i (.inl h2)).nonneg_of_le (hreg i (.inl h2)) (hs i h2)
  · simp

/-- If every drain or source across a channel from `k` is at least `e k`, the net channel current
into `k` is nonnegative. Only the devices with a channel terminal at `k` need C1 and C2. -/
theorem F_nonneg_of_le_neighbours {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n}
    (hpass : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → Passive (N.fet i).I)
    (hreg : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) → Regular (N.fet i).I)
    (hd : ∀ i, (N.fet i).s = .state k → e k ≤ pot u e (N.fet i).d)
    (hs : ∀ i, (N.fet i).d = .state k → e k ≤ pot u e (N.fet i).s) :
    0 ≤ N.F u e k := by
  unfold F FET.current
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with h1 h2 h2
  · simp
  · rw [h1, pot_state, sub_zero]
    exact (hpass i (.inr h1)).nonneg_of_le (hreg i (.inr h1)) (hd i h1)
  · rw [h2, pot_state, zero_sub, neg_nonneg]
    exact (hpass i (.inl h2)).nonpos_of_le (hreg i (.inl h2)) (hs i h2)
  · simp

/-- If every device with a channel terminal at `k` carries at most `Imax` in size, then
`|F_k| ≤ n_k · Imax`. -/
theorem abs_F_le_of_channel {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n} {Imax : ℝ}
    (h : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      |(N.fet i).current u e| ≤ Imax) :
    |N.F u e k| ≤ N.nChan k * Imax := by
  unfold F
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(if (N.fet i).s = .state k then (N.fet i).current u e else 0) -
          (if (N.fet i).d = .state k then (N.fet i).current u e else 0)|
      ≤ ∑ i, ((if (N.fet i).s = .state k then Imax else 0) +
          (if (N.fet i).d = .state k then Imax else 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2 h2
        · have hi := h i (.inr h1)
          simp only [sub_self, abs_zero]
          linarith [abs_nonneg ((N.fet i).current u e)]
        · simpa only [sub_zero, add_zero] using h i (.inr h1)
        · simpa only [zero_sub, abs_neg, zero_add] using h i (.inl h2)
        · simp
    _ = N.nChan k * Imax := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
          Finset.sum_const]
        simp only [nChan, nsmul_eq_mul, Nat.cast_add]
        ring

/-- Pointwise slew bound (THM, from C6): if every terminal of every device with a channel
terminal at `k` lies in `[0, Vmax]`, those devices satisfy C6, and `0 < Cmin ≤ C_k(e_k)`, then
`|ė_k| ≤ n_k · I_max / C_min`. -/
theorem abs_vf_le {u : Fin m → ℝ} {e : Fin n → ℝ} {k : Fin n} {Cmin Imax Vmax : ℝ}
    (hbd : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      BoundedOnRail Imax Vmax (N.fet i).I)                           -- MEAS (C6)
    (hpot : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      pot u e (N.fet i).g ∈ Icc 0 Vmax ∧ pot u e (N.fet i).d ∈ Icc 0 Vmax ∧
        pot u e (N.fet i).s ∈ Icc 0 Vmax)
    (hCmin : 0 < Cmin) (hC : Cmin ≤ N.C k (e k)) :                   -- MEAS
    |N.vf u e k| ≤ N.nChan k * Imax / Cmin := by
  have hF := N.abs_F_le_of_channel (u := u) (e := e) (k := k) fun i hi =>
    hbd i hi _ _ _ (hpot i hi).1 (hpot i hi).2.1 (hpot i hi).2.2
  show |N.F u e k / N.C k (e k)| ≤ N.nChan k * Imax / Cmin
  rw [abs_div, abs_of_pos (N.C_pos k _)]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) hCmin hC).trans
    (div_le_div_of_nonneg_right hF hCmin.le)

/-- Local rail invariance (THM, from C1 and C2, as THM L2.3): let `K` be a set of state nodes
whose devices satisfy C1 and C2. Suppose that on `[a, b]` the other channel terminal of every
device with a drain or source in `K` is in `K` or has potential in `[0, V]`. If `K` starts in
`[0, V]`, it stays in `[0, V]` on `[a, b]`. -/
theorem rail_invariance_set {K : Set (Fin n)}
    (hpass : ∀ i, ∀ k ∈ K, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Passive (N.fet i).I)                                           -- MODEL (C1)
    (hreg : ∀ i, ∀ k ∈ K, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Regular (N.fet i).I)                                           -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hnb : ∀ t ∈ Icc a b, ∀ i, ∀ k ∈ K,
      ((N.fet i).d = .state k →
        (∃ j ∈ K, (N.fet i).s = .state j) ∨ pot (u t) (e t) (N.fet i).s ∈ Icc 0 V) ∧
      ((N.fet i).s = .state k →
        (∃ j ∈ K, (N.fet i).d = .state j) ∨ pot (u t) (e t) (N.fet i).d ∈ Icc 0 V))  -- ENV
    (h0 : ∀ k ∈ K, e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, ∀ k ∈ K, e t k ∈ Icc 0 V := by
  have : Fintype K := Fintype.ofFinite K
  have hc : ∀ j : K, ContinuousOn (fun t => e t j) (Icc a b) :=
    fun j => continuousOn_pi.1 he.continuousOn j
  have hd : ∀ t ∈ Ico a b, ∀ j : K,
      HasDerivWithinAt (fun t => e t j) (N.vf (u t) (e t) j) (Ici t) t :=
    fun t ht j => hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) j
  intro t ht k hk
  refine ⟨?_, ?_⟩
  · have := max_principle (ι := K) (x := fun t j => -e t j)
      (x' := fun t j => -N.vf (u t) (e t) j) (V := 0)
      (continuousOn_pi.2 fun j => (hc j).neg)
      (fun t ht => hasDerivWithinAt_pi.2 fun j => (hd t ht j).neg)
      (fun j => neg_nonpos.2 (h0 j j.2).1) ?_ t ht ⟨k, hk⟩
    · simpa using this
    rintro t ht ⟨k, hk⟩ hk0 hmin
    simp only [neg_nonneg, neg_le_neg_iff, neg_nonpos] at hk0 hmin ⊢
    have hnb' := hnb t (Ico_subset_Icc_self ht)
    refine div_nonneg (N.F_nonneg_of_le_neighbours (fun i hi => hpass i k hk hi)
      (fun i hi => hreg i k hk hi) (fun i hi => ?_) (fun i hi => ?_)) (N.C_pos k _).le
    · rcases (hnb' i k hk).2 hi with ⟨j, hj, hdj⟩ | hmem
      · rw [hdj, pot_state]
        exact hmin ⟨j, hj⟩
      · exact hk0.trans hmem.1
    · rcases (hnb' i k hk).1 hi with ⟨j, hj, hsj⟩ | hmem
      · rw [hsj, pot_state]
        exact hmin ⟨j, hj⟩
      · exact hk0.trans hmem.1
  · have := max_principle (ι := K) (x := fun t j => e t j)
      (x' := fun t j => N.vf (u t) (e t) j) (V := V)
      (continuousOn_pi.2 hc) (fun t ht => hasDerivWithinAt_pi.2 (hd t ht))
      (fun j => (h0 j j.2).2) ?_ t ht ⟨k, hk⟩
    · exact this
    rintro t ht ⟨k, hk⟩ hk0 hmax
    have hnb' := hnb t (Ico_subset_Icc_self ht)
    refine div_nonpos_of_nonpos_of_nonneg (N.F_nonpos_of_neighbours_le
      (fun i hi => hpass i k hk hi) (fun i hi => hreg i k hk hi) (fun i hi => ?_)
      (fun i hi => ?_)) (N.C_pos k _).le
    · rcases (hnb' i k hk).2 hi with ⟨j, hj, hdj⟩ | hmem
      · rw [hdj, pot_state]
        exact hmax ⟨j, hj⟩
      · exact hmem.2.trans hk0
    · rcases (hnb' i k hk).1 hi with ⟨j, hj, hsj⟩ | hmem
      · rw [hsj, pot_state]
        exact hmax ⟨j, hj⟩
      · exact hmem.2.trans hk0

/-- Local rail invariance for one state node (THM, from C1 and C2): if the devices with a
channel terminal at `k` satisfy C1 and C2, and on `[a, b]` the other channel terminal of each of
them is `k` itself or has potential in `[0, V]`, then `e_k` stays in `[0, V]` once it starts
there. -/
theorem rail_invariance_node {k : Fin n}
    (hpass : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Passive (N.fet i).I)                                           -- MODEL (C1)
    (hreg : ∀ i, ((N.fet i).d = .state k ∨ (N.fet i).s = .state k) →
      Regular (N.fet i).I)                                           -- MODEL (C2)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b V : ℝ}
    (he : N.IsTrajOn u e a b)
    (hnb : ∀ t ∈ Icc a b, ∀ i,
      ((N.fet i).d = .state k →
        (N.fet i).s = .state k ∨ pot (u t) (e t) (N.fet i).s ∈ Icc 0 V) ∧
      ((N.fet i).s = .state k →
        (N.fet i).d = .state k ∨ pot (u t) (e t) (N.fet i).d ∈ Icc 0 V))  -- ENV
    (h0 : e a k ∈ Icc 0 V) :
    ∀ t ∈ Icc a b, e t k ∈ Icc 0 V := by
  intro t ht
  refine N.rail_invariance_set (K := {k}) (fun i j hj => ?_) (fun i j hj => ?_) he
    (fun t ht i j hj => ?_) (fun j hj => ?_) t ht k rfl
  · rw [mem_singleton_iff.1 hj]
    exact hpass i
  · rw [mem_singleton_iff.1 hj]
    exact hreg i
  · rw [mem_singleton_iff.1 hj]
    obtain ⟨h1, h2⟩ := hnb t ht i
    exact ⟨fun hd => (h1 hd).imp (fun h => ⟨k, rfl, h⟩) id,
      fun hs => (h2 hs).imp (fun h => ⟨k, rfl, h⟩) id⟩
  · rw [mem_singleton_iff.1 hj]
    exact h0

end Netlist

/-! ### One-dimensional comparison

A right-differentiable real function whose derivative is at least `r` below a level `c` reaches
`c` and stays above it. These are the timing arguments of THM L3.1. -/

/-- Barrier (THM): if `g` starts at least `c` and its right derivative is nonnegative wherever
`g ≤ c`, then `g` stays at least `c` on `[a, b]`. -/
theorem barrier_of_deriv_right_nonneg {g g' : ℝ → ℝ} {a b c : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (ha : c ≤ g a) (hface : ∀ t ∈ Ico a b, g t ≤ c → 0 ≤ g' t) :
    ∀ t ∈ Icc a b, c ≤ g t := by
  intro t ht
  have := max_principle (ι := Unit) (x := fun t _ => c - g t) (x' := fun t _ => -g' t) (V := 0)
    (continuousOn_pi.2 fun _ => continuousOn_const.sub hg)
    (fun t ht => hasDerivWithinAt_pi.2 fun _ => (hg' t ht).const_sub c)
    (fun _ => sub_nonpos.2 ha) (fun t ht _ h _ => neg_nonpos.2 (hface t ht (sub_nonneg.1 h)))
    t ht ()
  exact sub_nonpos.1 this

/-- Linear rise (THM): if the right derivative of `g` is at least `r ≥ 0` wherever `g ≤ c`, then
`g a + r (t − a) ≤ g t` at every `t ∈ [a, b]` with `g a + r (t − a) ≤ c`. -/
theorem linear_rise_of_deriv_right_ge {g g' : ℝ → ℝ} {a b c r : ℝ} (hr : 0 ≤ r)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hface : ∀ t ∈ Ico a b, g t ≤ c → r ≤ g' t) :
    ∀ t ∈ Icc a b, g a + r * (t - a) ≤ c → g a + r * (t - a) ≤ g t := by
  intro t ht hc
  have hsub : Ico a t ⊆ Ico a b := Ico_subset_Ico_right ht.2
  have hL : Continuous fun s => g a + r * (s - a) := by fun_prop
  have hd : ∀ s ∈ Ico a t,
      HasDerivWithinAt (fun s => g a + r * (s - a) - g s) (r - g' s) (Ici s) s := fun s hs =>
    ((((hasDerivAt_id s).sub_const a).const_mul r |>.const_add (g a)).congr_deriv
      (mul_one r)).hasDerivWithinAt.sub (hg' s (hsub hs))
  have := max_principle (ι := Unit) (x := fun s _ => g a + r * (s - a) - g s)
    (x' := fun s _ => r - g' s) (V := 0) (a := a) (b := t)
    (continuousOn_pi.2 fun _ => hL.continuousOn.sub (hg.mono (Icc_subset_Icc_right ht.2)))
    (fun s hs => hasDerivWithinAt_pi.2 fun _ => hd s hs) (fun _ => by simp)
    (fun s hs _ h _ => sub_nonpos.2 (hface s (hsub hs) (by
      have h' : g s ≤ g a + r * (s - a) := sub_nonneg.1 h
      nlinarith [hs.2])))
    t ⟨ht.1, le_rfl⟩ ()
  exact sub_nonpos.1 this

/-- Reaching a level (THM): if the right derivative of `g` is at least `r > 0` wherever `g ≤ c`,
then `c ≤ g t` at every `t ∈ [a, b]` with `c − g a ≤ r (t − a)`. -/
theorem reach_of_deriv_right_ge {g g' : ℝ → ℝ} {a b c r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hface : ∀ t ∈ Ico a b, g t ≤ c → r ≤ g' t) :
    ∀ t ∈ Icc a b, c - g a ≤ r * (t - a) → c ≤ g t := by
  intro t ht hct
  have hface0 : ∀ t ∈ Ico a b, g t ≤ c → 0 ≤ g' t := fun t ht h => hr.le.trans (hface t ht h)
  rcases le_or_gt c (g a) with hca | hca
  · exact barrier_of_deriv_right_nonneg hg hg' hca hface0 t ht
  set τ := a + (c - g a) / r with hτ
  have hτa : a ≤ τ := le_add_of_nonneg_right (div_nonneg (sub_nonneg.2 hca.le) hr.le)
  have hτt : τ ≤ t := by
    rw [hτ, ← le_sub_iff_add_le', div_le_iff₀' hr]
    exact hct
  have hgτ : g a + r * (τ - a) = c := by
    rw [hτ, add_sub_cancel_left, mul_div_cancel₀ _ hr.ne']
    ring
  have hcτ : c ≤ g τ := by
    have := linear_rise_of_deriv_right_ge hr.le hg hg' hface τ ⟨hτa, hτt.trans ht.2⟩ hgτ.le
    rwa [hgτ] at this
  exact barrier_of_deriv_right_nonneg (hg.mono (Icc_subset_Icc_left hτa))
    (fun s hs => hg' s ⟨hτa.trans hs.1, hs.2⟩) hcτ
    (fun s hs => hface0 s ⟨hτa.trans hs.1, hs.2⟩) t ⟨hτt, ht.2⟩

namespace Netlist

variable {n m : ℕ} {N : Netlist n m}

/-- A trajectory on `[a, b]` is a trajectory on every subinterval. -/
theorem IsTrajOn.mono {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b a' b' : ℝ}
    (he : N.IsTrajOn u e a b) (ha : a ≤ a') (hb : b' ≤ b) : N.IsTrajOn u e a' b' :=
  ⟨he.continuousOn.mono (Icc_subset_Icc ha hb),
    fun t ht => he.hasDerivWithinAt t ⟨ha.trans ht.1, ht.2.trans_le hb⟩⟩

end Netlist

end AsmPhys
