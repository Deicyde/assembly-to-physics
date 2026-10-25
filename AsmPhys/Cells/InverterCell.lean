import AsmPhys.Cells.Inverter
import AsmPhys.Cells.Compose

/-!
# The inverter as a composable cell

An inverter instance, read as a one-input cell computing `¬x` with `t_pd = tpdINV C_out^max` and
`t_cd = tcdINV C_out^min`, behaves along every trajectory whose output and input stay in the
rails: THM L3.1(a) and THM L3.2 hold on every subinterval. This is how THM L3.4 and THM L4.1 use
the inverter theorems; NAND2 and NOR2 enter the same way through H_cells.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

namespace Netlist.IsInverter

variable {N : Netlist n m} {inp : Node n m} {out : Fin n} {gnd vdd : Fin m} {iN iP : Fin N.nf}

/-- The inverter instance as a cell: one input `inp`, output `out`, function `¬x`, and the
inverter's propagation and contamination delays for output capacitance in `[Cmin, Cmax]`. -/
noncomputable def cell (_hinv : N.IsInverter inp out gnd vdd iN iP) (S : Params)
    (Cmin Cmax : ℝ) : Cell n m where
  ar := 1
  ar_pos := one_pos
  f := fun x => !x 0
  ins := fun _ => inp
  out := out
  tpd := S.tpdINV Cmax
  tcd := S.tcdINV Cmin

/-- `t_pd(INV) ≥ 0` under K0–K14. -/
theorem _root_.AsmPhys.Params.Consistent.tpdINV_nonneg {S : Params} (hS : S.Consistent)
    {Cmax : ℝ} (hC : 0 ≤ Cmax) : 0 ≤ S.tpdINV Cmax := by
  obtain ⟨hVOL, hK01, hK02, hK03, -⟩ := hS.K0
  exact mul_nonneg hC ((div_pos (by linarith) (sub_pos.2 hS.K5)).le.trans (le_max_left _ _))

/-- `t_cd(INV) ≥ 0` under K0–K14. -/
theorem _root_.AsmPhys.Params.Consistent.tcdINV_nonneg {S : Params} (hS : S.Consistent)
    {Cmin : ℝ} (hC : 0 ≤ Cmin) : 0 ≤ S.tcdINV Cmin := by
  obtain ⟨hVOL, hK01, hK02, hK03, hVOH⟩ := hS.K0
  -- `I_max > 0`: the n-FET's on-drive floor at full swing is positive (K6, K13).
  have hK6 := lt_min_iff.1 (hS.K13_leak.2.trans_lt hS.K6)
  have hGn : 0 < S.pn.Gon := pos_of_mul_pos_left hK6.1 hVOL.le
  have hImax : 0 < max S.pn.Imax S.pp.Imax :=
    (lt_min (mul_pos hGn (by linarith [hS.K13_supply])) hK6.2).trans_le
      (hS.K13_drive.1.trans (le_max_left _ _))
  have hNM : 0 ≤ min S.NML S.NMH :=
    le_min (sub_nonneg.2 hK01.le) (sub_nonneg.2 hK03.le)
  exact div_nonneg (mul_nonneg hNM hC) (by positivity)

/-- An inverter instance behaves as a cell along any trajectory on `[A, B]` whose output and input
stay in the rails. -/
theorem behaves {S : Params} (hS : S.Consistent)                      -- THM (norm_num)
    (hinv : N.IsInverter inp out gnd vdd iN iP)
    (hn : FETContract .n S.pn S.VDDmax (N.fet iN).I)                 -- MODEL/MEAS (C1–C6)
    (hp : FETContract .p S.pp S.VDDmax (N.fet iP).I)                 -- MODEL/MEAS (C1–C6)
    {Cmin Cmax : ℝ} (hCmin : 0 < Cmin)                               -- MEAS
    (hcap : ∀ v, N.C out v ∈ Icc Cmin Cmax)                          -- MEAS
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                   -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {A B : ℝ}
    (he : N.IsTrajOn u e A B)
    (hgnd : ∀ t ∈ Icc A B, u t gnd = 0)                              -- ENV
    (hvdd : ∀ t ∈ Icc A B, u t vdd = VDD)                            -- ENV
    (hout : ∀ t ∈ Icc A B, e t out ∈ Icc 0 VDD)
    (hin : ∀ t ∈ Icc A B, pot (u t) (e t) inp ∈ Icc 0 S.VDDmax) :
    (hinv.cell S Cmin Cmax).Behaves S u e A B := by
  have hCmax : 0 ≤ Cmax := hCmin.le.trans ((hcap 0).1.trans (hcap 0).2)
  have htpd := hS.tpdINV_nonneg hCmax
  refine ⟨htpd, hS.tcdINV_nonneg hCmin.le, fun x t₀ t₁ hA hB hx t ht => ?_,
    fun b t₁ ht₁ h1 t ht => ?_⟩
  · -- `t ∈ [t₀ + t_pd, t₁]` and `t_pd ≥ 0` give `t₀ ≤ t₁`, so `t₀ ∈ [A, B]`.
    have ht : t ∈ Icc (t₀ + S.tpdINV Cmax) t₁ := ht
    have hsub : Icc t₀ t₁ ⊆ Icc A B := Icc_subset_Icc hA hB
    have h0 := hout t₀ (hsub ⟨le_rfl, by linarith [ht.1, ht.2]⟩)
    exact (hinv.propagation hS hn hp hcap hVDD (he.mono hA hB) (fun s hs => hgnd s (hsub hs))
      (fun s hs => hvdd s (hsub hs)) (x := x ⟨0, one_pos⟩) (fun s hs => hx _ s hs) h0).1 t ht
  · have hsub : Icc t₁ B ⊆ Icc A B := Icc_subset_Icc_left ht₁.1
    exact hinv.contamination hS hn hp hCmin hcap hVDD (he.mono ht₁.1 le_rfl)
      (fun s hs => hgnd s (hsub hs)) (fun s hs => hvdd s (hsub hs)) (fun s hs => hin s (hsub hs))
      h1 (hout t₁ ht₁) t ht

end Netlist.IsInverter

end AsmPhys
