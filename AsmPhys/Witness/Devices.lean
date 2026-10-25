import AsmPhys.Params
import Mathlib.Order.Monotone.Union
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Non-vacuity of the FET contract

For any parameters with `V_off < V_on`, `G_on, I_sat, I_off ≥ 0` and
`min(G_on·V_max, I_sat) ≤ I_max`, the clamp device

  `I(g, d, s) = r(gate drive) · c(v_ds)`,
  `r(x) = clamp((x − V_off)/(V_on − V_off), 0, 1)`,  `c(x) = clamp(G_on·x, −I_sat, I_sat)`

meets the FET contract C1–C6 of either polarity. It conducts nothing when off, so `I_off = 0`
would do, and on the rails `|I| ≤ min(G_on·|v_ds|, I_sat)`. Every sheet satisfying K0–K13 meets
these conditions for both polarities, so the contracts of a consistent sheet are never vacuous.
-/

namespace AsmPhys.Witness

open Set

/-- Gate-drive ramp `r(x) = clamp((x − V_off)/(V_on − V_off), 0, 1)`. -/
noncomputable def ramp (P : FETParams) (x : ℝ) : ℝ :=
  max 0 (min 1 ((x - P.Voff) / (P.Von - P.Voff)))

/-- Channel characteristic `c(x) = clamp(G_on·x, −I_sat, I_sat)`. -/
noncomputable def chan (P : FETParams) (x : ℝ) : ℝ :=
  max (-P.Isat) (min P.Isat (P.Gon * x))

/-- The clamp device of polarity `pol`: `r(gate drive) · c(v_ds)`. -/
noncomputable def dev (pol : Polarity) (P : FETParams) (g d s : ℝ) : ℝ :=
  ramp P (gateDrive pol g d s) * chan P (d - s)

section Clamp

variable {P : FETParams}

lemma ramp_nonneg (x : ℝ) : 0 ≤ ramp P x := le_max_left _ _

lemma ramp_le_one (x : ℝ) : ramp P x ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- With `V_off < V_on`, the ramp vanishes at gate drives up to `V_off`. -/
lemma ramp_eq_zero (hV : P.Voff < P.Von) {x : ℝ} (hx : x ≤ P.Voff) : ramp P x = 0 :=
  max_eq_left <| (min_le_right _ _).trans <|
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) (sub_pos.2 hV).le

/-- With `V_off < V_on`, the ramp is `1` at gate drives from `V_on` on. -/
lemma ramp_eq_one (hV : P.Voff < P.Von) {x : ℝ} (hx : P.Von ≤ x) : ramp P x = 1 := by
  have h : 1 ≤ (x - P.Voff) / (P.Von - P.Voff) := by
    rw [le_div_iff₀ (sub_pos.2 hV)]; linarith
  rw [ramp, min_eq_left h, max_eq_right zero_le_one]

lemma ramp_mono (hV : P.Voff < P.Von) : Monotone (ramp P) := fun _ _ h =>
  max_le_max le_rfl <| min_le_min le_rfl <|
    div_le_div_of_nonneg_right (sub_le_sub_right h _) (sub_pos.2 hV).le

/-- Clamping from below by a constant does not increase distances. -/
lemma abs_max_sub_max_le' (a b c : ℝ) : |max c a - max c b| ≤ |a - b| :=
  (abs_max_sub_max_le_max _ _ _ _).trans (by simp)

/-- Clamping from above by a constant does not increase distances. -/
lemma abs_min_sub_min_le' (a b c : ℝ) : |min c a - min c b| ≤ |a - b| :=
  (abs_min_sub_min_le_max _ _ _ _).trans (by simp)

/-- With `V_off < V_on`, the ramp is Lipschitz with constant `1/(V_on − V_off)`. -/
lemma abs_ramp_sub_le (hV : P.Voff < P.Von) (x y : ℝ) :
    |ramp P x - ramp P y| ≤ |x - y| / (P.Von - P.Voff) := by
  unfold ramp
  calc _ ≤ |(x - P.Voff) / (P.Von - P.Voff) - (y - P.Voff) / (P.Von - P.Voff)| :=
        (abs_max_sub_max_le' _ _ _).trans (abs_min_sub_min_le' _ _ _)
    _ = |x - y| / (P.Von - P.Voff) := by
        rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos (sub_pos.2 hV)]

lemma chan_mono (hG : 0 ≤ P.Gon) : Monotone (chan P) := fun _ _ h =>
  max_le_max le_rfl <| min_le_min le_rfl <| mul_le_mul_of_nonneg_left h hG

lemma chan_nonneg (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ chan P x :=
  (le_min hI (mul_nonneg hG hx)).trans (le_max_right _ _)

lemma chan_nonpos (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) {x : ℝ} (hx : x ≤ 0) : chan P x ≤ 0 :=
  max_le (neg_nonpos.2 hI) ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos hG hx))

lemma abs_chan_le (hI : 0 ≤ P.Isat) (x : ℝ) : |chan P x| ≤ P.Isat :=
  abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self hI) (min_le_left _ _)⟩

/-- With `G_on ≥ 0`, the channel characteristic is Lipschitz with constant `G_on`. -/
lemma abs_chan_sub_le (hG : 0 ≤ P.Gon) (x y : ℝ) :
    |chan P x - chan P y| ≤ P.Gon * |x - y| := by
  unfold chan
  calc _ ≤ |P.Gon * x - P.Gon * y| :=
        (abs_max_sub_max_le' _ _ _).trans (abs_min_sub_min_le' _ _ _)
    _ = P.Gon * |x - y| := by rw [← mul_sub, abs_mul, abs_of_nonneg hG]

/-- With `G_on, I_sat ≥ 0`, `|c(x)| = min(G_on·|x|, I_sat)`. -/
lemma abs_chan (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (x : ℝ) :
    |chan P x| = min (P.Gon * |x|) P.Isat := by
  unfold chan
  rcases le_total 0 x with hx | hx
  · have h := le_min hI (mul_nonneg hG hx)
    rw [max_eq_right ((neg_nonpos.2 hI).trans h), abs_of_nonneg h, abs_of_nonneg hx, min_comm]
  · have h := mul_nonpos_of_nonneg_of_nonpos hG hx
    rw [min_eq_right (h.trans hI), abs_of_nonpos hx, mul_neg]
    rcases le_total (-P.Isat) (P.Gon * x) with h' | h'
    · rw [max_eq_right h', abs_of_nonpos h, min_eq_left (by linarith)]
    · rw [max_eq_left h', abs_neg, abs_of_nonneg hI, min_eq_right (by linarith)]

end Clamp

/-- The gate drive is Lipschitz: `|Δ(gate drive)| ≤ |Δg| + max(|Δd|, |Δs|)`. -/
lemma abs_gateDrive_sub_le (pol : Polarity) (g d s g' d' s' : ℝ) :
    |gateDrive pol g d s - gateDrive pol g' d' s'| ≤ |g - g'| + max |d - d'| |s - s'| := by
  cases pol
  · calc _ = |(g - g') - (min d s - min d' s')| := by simp only [gateDrive]; congr 1; ring
      _ ≤ |g - g'| + |min d s - min d' s'| := abs_sub _ _
      _ ≤ _ := by linarith [abs_min_sub_min_le_max d s d' s']
  · calc _ = |(max d s - max d' s') - (g - g')| := by simp only [gateDrive]; congr 1; ring
      _ ≤ |max d s - max d' s'| + |g - g'| := abs_sub _ _
      _ ≤ _ := by linarith [abs_max_sub_max_le_max d s d' s']

/-- From `|c₁| ≤ B` and `|r₂| ≤ A`, `|r₁c₁ − r₂c₂| ≤ |r₁ − r₂|·B + A·|c₁ − c₂|`. -/
lemma abs_mul_sub_mul_le_of_abs_le {r₁ r₂ c₁ c₂ A B : ℝ} (hc : |c₁| ≤ B) (hr : |r₂| ≤ A) :
    |r₁ * c₁ - r₂ * c₂| ≤ |r₁ - r₂| * B + A * |c₁ - c₂| :=
  calc |r₁ * c₁ - r₂ * c₂| = |(r₁ - r₂) * c₁ + r₂ * (c₁ - c₂)| := by congr 1; ring
    _ ≤ |r₁ - r₂| * |c₁| + |r₂| * |c₁ - c₂| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |r₁ - r₂| * B + A * |c₁ - c₂| := by gcongr

section Device

variable {P : FETParams}

/-- The clamp device carries at most the channel current: `|I| ≤ |c(d − s)|`. -/
lemma abs_dev_le (pol : Polarity) (g d s : ℝ) : |dev pol P g d s| ≤ |chan P (d - s)| := by
  rw [dev, abs_mul, abs_of_nonneg (ramp_nonneg _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (ramp_le_one _)

/-- With `G_on, I_sat ≥ 0`, the clamp device is passive (C1). -/
theorem dev_passive (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (pol : Polarity) :
    Passive (dev pol P) := by
  intro g d s
  unfold dev
  rcases le_total 0 (d - s) with h | h
  · exact mul_nonneg h (mul_nonneg (ramp_nonneg _) (chan_nonneg hG hI h))
  · exact mul_nonneg_of_nonpos_of_nonpos h
      (mul_nonpos_of_nonneg_of_nonpos (ramp_nonneg _) (chan_nonpos hG hI h))

/-- With `V_off < V_on` and `G_on, I_sat ≥ 0`, the clamp device is Lipschitz and bounded by
`I_sat` (C2). -/
theorem dev_regular (hV : P.Voff < P.Von) (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (pol : Polarity) :
    Regular (dev pol P) := by
  have hw : 0 < P.Von - P.Voff := sub_pos.2 hV
  have hK : 0 ≤ 2 * P.Isat / (P.Von - P.Voff) + 2 * P.Gon :=
    add_nonneg (div_nonneg (mul_nonneg zero_le_two hI) hw.le) (mul_nonneg zero_le_two hG)
  refine ⟨⟨⟨_, hK⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩,
    ⟨P.Isat, fun g d s => (abs_dev_le pol g d s).trans (abs_chan_le hI _)⟩⟩
  obtain ⟨g, d, s⟩ := x
  obtain ⟨g', d', s'⟩ := y
  simp only [Prod.dist_eq, Real.dist_eq, dev]
  set D := max |g - g'| (max |d - d'| |s - s'|)
  have hd : |d - d'| ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hs : |s - s'| ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hr : |ramp P (gateDrive pol g d s) - ramp P (gateDrive pol g' d' s')| ≤
      2 * D / (P.Von - P.Voff) :=
    (abs_ramp_sub_le hV _ _).trans <| div_le_div_of_nonneg_right
      ((abs_gateDrive_sub_le pol g d s g' d' s').trans
        (by linarith [le_max_left |g - g'| (max |d - d'| |s - s'|), max_le hd hs])) hw.le
  have hc : |chan P (d - s) - chan P (d' - s')| ≤ P.Gon * (2 * D) := by
    refine (abs_chan_sub_le hG _ _).trans (mul_le_mul_of_nonneg_left ?_ hG)
    calc |d - s - (d' - s')| = |(d - d') - (s - s')| := by congr 1; ring
      _ ≤ |d - d'| + |s - s'| := abs_sub _ _
      _ ≤ 2 * D := by linarith
  have h1 : |ramp P (gateDrive pol g' d' s')| ≤ 1 := by
    rw [abs_of_nonneg (ramp_nonneg _)]; exact ramp_le_one _
  calc _ ≤ _ := abs_mul_sub_mul_le_of_abs_le (abs_chan_le hI _) h1
    _ ≤ 2 * D / (P.Von - P.Voff) * P.Isat + 1 * (P.Gon * (2 * D)) :=
        add_le_add (mul_le_mul_of_nonneg_right hr hI) (mul_le_mul_of_nonneg_left hc zero_le_one)
    _ = (2 * P.Isat / (P.Von - P.Voff) + 2 * P.Gon) * D := by ring

/-- With `V_off < V_on` and `G_on, I_sat ≥ 0`, the clamp device is monotone in the drain (C5).
On each side of `d = s` one factor is fixed in sign and both move the right way. -/
theorem dev_mono_d (hV : P.Voff < P.Von) (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (pol : Polarity)
    (g s : ℝ) : Monotone fun d => dev pol P g d s := by
  refine MonotoneOn.Iic_union_Ici (a := s) ?_ ?_
  · rintro d₁ (h₁ : d₁ ≤ s) d₂ (h₂ : d₂ ≤ s) h
    have hc := chan_mono (P := P) hG (sub_le_sub_right h s)
    cases pol
    · -- n: the drive `g − d` falls and `c(d − s) ≤ 0` rises
      simp only [dev, gateDrive, min_eq_left h₁, min_eq_left h₂]
      exact (mul_le_mul_of_nonpos_right (ramp_mono hV (sub_le_sub_left h g))
        (chan_nonpos hG hI (sub_nonpos.2 h₁))).trans (mul_le_mul_of_nonneg_left hc (ramp_nonneg _))
    · -- p: the drive `s − g` is fixed
      simp only [dev, gateDrive, max_eq_right h₁, max_eq_right h₂]
      exact mul_le_mul_of_nonneg_left hc (ramp_nonneg _)
  · rintro d₁ (h₁ : s ≤ d₁) d₂ (h₂ : s ≤ d₂) h
    have hc := chan_mono (P := P) hG (sub_le_sub_right h s)
    cases pol
    · -- n: the drive `g − s` is fixed
      simp only [dev, gateDrive, min_eq_right h₁, min_eq_right h₂]
      exact mul_le_mul_of_nonneg_left hc (ramp_nonneg _)
    · -- p: the drive `d − g` and `c(d − s) ≥ 0` both rise
      simp only [dev, gateDrive, max_eq_left h₁, max_eq_left h₂]
      exact (mul_le_mul_of_nonneg_left hc (ramp_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (ramp_mono hV (sub_le_sub_right h g))
          (chan_nonneg hG hI (sub_nonneg.2 h₂)))

/-- With `V_off < V_on` and `G_on, I_sat ≥ 0`, the clamp device is antitone in the source (C5).
On each side of `s = d` one factor is fixed in sign and both move the right way. -/
theorem dev_anti_s (hV : P.Voff < P.Von) (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (pol : Polarity)
    (g d : ℝ) : Antitone fun s => dev pol P g d s := by
  refine AntitoneOn.Iic_union_Ici (a := d) ?_ ?_
  · rintro s₁ (h₁ : s₁ ≤ d) s₂ (h₂ : s₂ ≤ d) h
    have hc := chan_mono (P := P) hG (sub_le_sub_left h d)
    cases pol
    · -- n: the drive `g − s` and `c(d − s) ≥ 0` both fall
      simp only [dev, gateDrive, min_eq_right h₁, min_eq_right h₂]
      exact (mul_le_mul_of_nonneg_left hc (ramp_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (ramp_mono hV (sub_le_sub_left h g))
          (chan_nonneg hG hI (sub_nonneg.2 h₁)))
    · -- p: the drive `d − g` is fixed
      simp only [dev, gateDrive, max_eq_left h₁, max_eq_left h₂]
      exact mul_le_mul_of_nonneg_left hc (ramp_nonneg _)
  · rintro s₁ (h₁ : d ≤ s₁) s₂ (h₂ : d ≤ s₂) h
    have hc := chan_mono (P := P) hG (sub_le_sub_left h d)
    cases pol
    · -- n: the drive `g − d` is fixed
      simp only [dev, gateDrive, min_eq_left h₁, min_eq_left h₂]
      exact mul_le_mul_of_nonneg_left hc (ramp_nonneg _)
    · -- p: the drive `s − g` rises and `c(d − s) ≤ 0` falls
      simp only [dev, gateDrive, max_eq_right h₁, max_eq_right h₂]
      exact (mul_le_mul_of_nonpos_right (ramp_mono hV (sub_le_sub_right h g))
        (chan_nonpos hG hI (sub_nonpos.2 h₂))).trans
        (mul_le_mul_of_nonneg_left hc (ramp_nonneg _))

end Device

/-- The clamp device meets the FET contract C1–C6. -/
theorem dev_contract {pol : Polarity} {P : FETParams} {Vmax : ℝ} (hV : P.Voff < P.Von)
    (hG : 0 ≤ P.Gon) (hI : 0 ≤ P.Isat) (hoff : 0 ≤ P.Ioff)
    (hmax : min (P.Gon * Vmax) P.Isat ≤ P.Imax) :
    FETContract pol P Vmax (dev pol P) := by
  refine ⟨dev_passive hG hI pol, dev_regular hV hG hI pol, ?_, ?_, dev_mono_d hV hG hI pol,
    dev_anti_s hV hG hI pol, ?_⟩
  · -- C3: off, the ramp vanishes
    rintro g d s - - (h : gateDrive pol g d s ≤ P.Voff)
    rw [dev, ramp_eq_zero hV h, zero_mul, abs_zero]
    exact hoff
  · -- C4: on, the ramp is `1`
    rintro g d s - - (h : P.Von ≤ gateDrive pol g d s)
    rw [dev, ramp_eq_one hV h, one_mul, abs_chan hG hI]
  · -- C6: on the rails `|d − s| ≤ V_max`
    rintro g d s - hd hs
    refine (abs_dev_le pol g d s).trans ?_
    rw [abs_chan hG hI]
    refine le_trans (min_le_min (mul_le_mul_of_nonneg_left ?_ hG) le_rfl) hmax
    exact abs_sub_le_iff.2 ⟨by linarith [hd.2, hs.1], by linarith [hd.1, hs.2]⟩

/-- Every sheet satisfying K0–K13 has devices of both polarities meeting their contracts. -/
theorem _root_.AsmPhys.Params.Consistent.exists_fetContract {S : Params} (hS : S.Consistent) :
    FETContract .n S.pn S.VDDmax (dev .n S.pn) ∧ FETContract .p S.pp S.VDDmax (dev .p S.pp) := by
  obtain ⟨hOL, -, -, -, hOH⟩ := hS.K0
  obtain ⟨hn, hp⟩ := hS.K13_leak
  -- K6 and K5 with `I_off ≥ 0`: the on-drive floors are positive
  have h6 := lt_min_iff.1 (hp.trans_lt hS.K6)
  have h5 := lt_min_iff.1 (hn.trans_lt hS.K5)
  exact ⟨dev_contract hS.K9n (pos_of_mul_pos_left h6.1 hOL.le).le h6.2.le hn hS.K13_drive.1,
    dev_contract hS.K9p (pos_of_mul_pos_left h5.1 (sub_pos.2 hOH).le).le h5.2.le hp
      hS.K13_drive.2⟩

/-- A constant positive capacitance meets the node-capacitance contract. -/
theorem nodeCap_const {c : ℝ} (hc : 0 < c) : NodeCap c c fun _ => c :=
  ⟨hc, fun _ => ⟨le_rfl, le_rfl⟩, ⟨0, LipschitzWith.const c⟩⟩

end AsmPhys.Witness
