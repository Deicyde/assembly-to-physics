import AsmPhys.Cells.InverterCore
import AsmPhys.Cells.InverterCell

/-!
# Contamination along a chain of inverters

If three inverters in a chain `y₀ → y₁ → y₂` hold valid outputs `b, ¬b, b`, the last output stays a
valid input level `b` for the sum of the three contamination delays, whatever the chain's input
does within the rails: each stage keeps its output valid while its input is still valid (THM
L3.1(b)) and then stays readable for its own contamination delay (THM L3.2).
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- **Contamination chain.** Three inverters `inp → y₀ → y₁ → y₂` with valid outputs `b, ¬b, b` at
`t₁` keep `y₂` a valid input level `b` for `t_cd(y₀) + t_cd(y₁) + t_cd(y₂)`. -/
theorem contamination_chain3 {S : Params} (hS : S.Consistent)        -- THM (norm_num)
    {N : Netlist n m} {inp : Node n m} {y₀ y₁ y₂ : Fin n} {gnd vdd : Fin m}
    {i₀n i₀p i₁n i₁p i₂n i₂p : Fin N.nf}
    (h₀ : N.IsInverter inp y₀ gnd vdd i₀n i₀p)
    (h₁ : N.IsInverter (.state y₀) y₁ gnd vdd i₁n i₁p)
    (h₂ : N.IsInverter (.state y₁) y₂ gnd vdd i₂n i₂p)
    (hc : N.ContractOn S {i₀n, i₀p, i₁n, i₁p, i₂n, i₂p})              -- MODEL/MEAS
    {C₀ C₁ C₂ D₀ D₁ D₂ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)  -- MEAS
    (hcap₀ : ∀ v, N.C y₀ v ∈ Icc C₀ D₀) (hcap₁ : ∀ v, N.C y₁ v ∈ Icc C₁ D₁)  -- MEAS
    (hcap₂ : ∀ v, N.C y₂ v ∈ Icc C₂ D₂)                              -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {t₁ t₂ : ℝ}
    (he : N.IsTrajOn u e t₁ t₂)
    (hgnd : ∀ t ∈ Icc t₁ t₂, u t gnd = 0)                            -- ENV
    (hvdd : ∀ t ∈ Icc t₁ t₂, u t vdd = VDD)                          -- ENV
    (hin : ∀ t ∈ Icc t₁ t₂, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax)
    (hrail : ∀ t ∈ Icc t₁ t₂, e t y₀ ∈ Icc 0 S.VDDmax ∧ e t y₁ ∈ Icc 0 S.VDDmax ∧
      e t y₂ ∈ Icc 0 S.VDDmax)
    {b : Bool}
    (hb : S.validOut b (e t₁ y₀) ∧ S.validOut (!b) (e t₁ y₁) ∧ S.validOut b (e t₁ y₂)) :
    ∀ t ∈ Icc t₁ (min t₂ (t₁ + S.tcdINV C₀ + S.tcdINV C₁ + S.tcdINV C₂)),
      S.validIn b (e t y₂) := by
  have hcn : ∀ {i}, i ∈ ({i₀n, i₀p, i₁n, i₁p, i₂n, i₂p} : Finset (Fin N.nf)) →
      (N.fet i).pol = .n → FETContract .n S.pn S.VDDmax (N.fet i).I := fun hi hpol => by
    have h := hc _ hi
    rw [hpol] at h
    exact h
  have hcp : ∀ {i}, i ∈ ({i₀n, i₀p, i₁n, i₁p, i₂n, i₂p} : Finset (Fin N.nf)) →
      (N.fet i).pol = .p → FETContract .p S.pp S.VDDmax (N.fet i).I := fun hi hpol => by
    have h := hc _ hi
    rw [hpol] at h
    exact h
  have h₀n := hcn (by simp) h₀.pol_n
  have h₀p := hcp (by simp) h₀.pol_p
  have h₁n := hcn (by simp) h₁.pol_n
  have h₁p := hcp (by simp) h₁.pol_p
  have h₂n := hcn (by simp) h₂.pol_n
  have h₂p := hcp (by simp) h₂.pol_p
  have hcd₀ := hS.tcdINV_nonneg hC₀.le
  have hcd₁ := hS.tcdINV_nonneg hC₁.le
  set A := t₁ + S.tcdINV C₀ with hA
  set B := A + S.tcdINV C₁ with hB
  have hsub : ∀ {a b : ℝ}, t₁ ≤ a → b ≤ t₂ → ∀ s ∈ Icc a b, s ∈ Icc t₁ t₂ :=
    fun ha hb s hs => ⟨ha.trans hs.1, hs.2.trans hb⟩
  -- `y₀` is `validOut b` at `t₁`, so it stays `validIn b` up to `A` (THM L3.2).
  have c₀ : ∀ t ∈ Icc t₁ t₂, t ≤ A → S.validIn b (e t y₀) := fun t ht htA =>
    h₀.contamination_rail hS h₀n h₀p hC₀ hcap₀ hVDD he hgnd hvdd hin (fun s hs => (hrail s hs).1)
      hb.1 t ⟨ht.1, le_min ht.2 htA⟩
  -- `y₁`'s input is valid up to `A`, so `y₁` stays `validOut ¬b` (THM L3.1(b)).
  have p₁ : ∀ t ∈ Icc t₁ t₂, t ≤ A → S.validOut (!b) (e t y₁) := fun t ht htA => by
    have hle : min t₂ A ≤ t₂ := min_le_left _ _
    exact (h₁.propagation_rail hS h₁n h₁p hcap₁ hVDD (he.mono le_rfl hle)
      (fun s hs => hgnd s (hsub le_rfl hle s hs)) (fun s hs => hvdd s (hsub le_rfl hle s hs))
      (fun s hs => (hrail s (hsub le_rfl hle s hs)).2.1) (x := b)
      (fun s hs => c₀ s (hsub le_rfl hle s hs) (hs.2.trans (min_le_right _ _)))).2 t₁
      ⟨le_rfl, le_min (ht.1.trans ht.2) (ht.1.trans htA)⟩ hb.2.1 t ⟨ht.1, le_min ht.2 htA⟩
  -- `y₁` is `validOut ¬b` at `A`, so it stays `validIn ¬b` up to `B` (THM L3.2).
  have c₁ : ∀ t ∈ Icc t₁ t₂, t ≤ B → S.validIn (!b) (e t y₁) := fun t ht htB => by
    rcases le_or_gt t A with htA | hAt
    · exact hS.validIn_of_validOut (p₁ t ht htA)
    · have hA₁ : t₁ ≤ A := by linarith
      have hA₂ : A ≤ t₂ := hAt.le.trans ht.2
      exact h₁.contamination_rail hS h₁n h₁p hC₁ hcap₁ hVDD (he.mono hA₁ le_rfl)
        (fun s hs => hgnd s (hsub hA₁ le_rfl s hs)) (fun s hs => hvdd s (hsub hA₁ le_rfl s hs))
        (fun s hs => (hrail s (hsub hA₁ le_rfl s hs)).1)
        (fun s hs => (hrail s (hsub hA₁ le_rfl s hs)).2.1) (p₁ A ⟨hA₁, hA₂⟩ le_rfl) t
        ⟨hAt.le, le_min ht.2 htB⟩
  -- `y₂`'s input is valid up to `B`, so `y₂` stays `validOut b` (THM L3.1(b)).
  have p₂ : ∀ t ∈ Icc t₁ t₂, t ≤ B → S.validOut b (e t y₂) := fun t ht htB => by
    have hle : min t₂ B ≤ t₂ := min_le_left _ _
    have h := (h₂.propagation_rail hS h₂n h₂p hcap₂ hVDD (he.mono le_rfl hle)
      (fun s hs => hgnd s (hsub le_rfl hle s hs)) (fun s hs => hvdd s (hsub le_rfl hle s hs))
      (fun s hs => (hrail s (hsub le_rfl hle s hs)).2.2) (x := !b)
      (fun s hs => c₁ s (hsub le_rfl hle s hs) (hs.2.trans (min_le_right _ _)))).2 t₁
      ⟨le_rfl, le_min (ht.1.trans ht.2) (ht.1.trans htB)⟩ (by rw [Bool.not_not]; exact hb.2.2) t
      ⟨ht.1, le_min ht.2 htB⟩
    rwa [Bool.not_not] at h
  -- `y₂` is `validOut b` at `B`, so it stays `validIn b` for `t_cd(y₂)` more (THM L3.2).
  intro t ht
  have ht' : t ∈ Icc t₁ t₂ := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htC : t ≤ B + S.tcdINV C₂ := ht.2.trans (min_le_right _ _)
  rcases le_or_gt t B with htB | hBt
  · exact hS.validIn_of_validOut (p₂ t ht' htB)
  · have hB₁ : t₁ ≤ B := by linarith
    have hB₂ : B ≤ t₂ := hBt.le.trans ht'.2
    exact h₂.contamination_rail hS h₂n h₂p hC₂ hcap₂ hVDD (he.mono hB₁ le_rfl)
      (fun s hs => hgnd s (hsub hB₁ le_rfl s hs)) (fun s hs => hvdd s (hsub hB₁ le_rfl s hs))
      (fun s hs => (hrail s (hsub hB₁ le_rfl s hs)).2.1)
      (fun s hs => (hrail s (hsub hB₁ le_rfl s hs)).2.2) (p₂ B ⟨hB₁, hB₂⟩ le_rfl) t
      ⟨hBt.le, le_min ht'.2 htC⟩

end AsmPhys
