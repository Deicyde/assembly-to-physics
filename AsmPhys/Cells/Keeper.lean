import AsmPhys.Cells.Inverter
import AsmPhys.Circuit.Tube

/-!
# Static storage: a cross-coupled inverter pair holds its bit

Two inverters whose inputs are each other's outputs, `x = ¬y` and `y = ¬x`, form the keeper loop
of every static latch. The tube `{x ≤ V_OL, y ≥ V_OH}` is invariant for every pair of devices
meeting the FET contracts and every output capacitance law: on the face `x = V_OL` the inverter
driving `x` sees a valid-high input and pulls down with net current at least `I_fall > 0` (K6),
and on the face `y = V_OH` the other sees a valid-low input and pulls up with at least
`I_rise > 0` (K5). This is the first nonempty hold tube of the development.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

/-- **Keeper hold.** A cross-coupled inverter pair started with `x` a valid `0` and `y` a valid
`1`, both on the rails, keeps them so on `[a, b]`. -/
theorem keeper_hold {S : Params} (hS : S.Consistent)                 -- THM (norm_num)
    {N : Netlist n m} {x y : Fin n} {gnd vdd : Fin m} {i1n i1p i2n i2p : Fin N.nf}
    (h1 : N.IsInverter (.state y) x gnd vdd i1n i1p)
    (h2 : N.IsInverter (.state x) y gnd vdd i2n i2p)
    (h1n : FETContract .n S.pn S.VDDmax (N.fet i1n).I)                -- MODEL/MEAS (C1–C6)
    (h1p : FETContract .p S.pp S.VDDmax (N.fet i1p).I)                -- MODEL/MEAS (C1–C6)
    (h2n : FETContract .n S.pn S.VDDmax (N.fet i2n).I)                -- MODEL/MEAS (C1–C6)
    (h2p : FETContract .p S.pp S.VDDmax (N.fet i2p).I)                -- MODEL/MEAS (C1–C6)
    {VDD : ℝ} (hVDD : VDD ∈ Icc S.VDDmin S.VDDmax)                    -- ENV
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {a b : ℝ}
    (he : N.IsTrajOn u e a b)
    (hgnd : ∀ t ∈ Icc a b, u t gnd = 0)                               -- ENV
    (hvdd : ∀ t ∈ Icc a b, u t vdd = VDD)                             -- ENV
    (hx0 : e a x ∈ Icc 0 S.VOL) (hy0 : e a y ∈ Icc S.VOH VDD) :
    ∀ t ∈ Icc a b, e t x ≤ S.VOL ∧ S.VOH ≤ e t y := by
  obtain ⟨-, hOLIL, hILIH, hIHOH, -⟩ := hS.K0
  have hVDD0 : 0 ≤ VDD := hx0.1.trans (hx0.2.trans (by linarith [hy0.1, hy0.2]))
  have hrx := h1.out_mem_rails h1n.passive h1n.regular h1p.passive h1p.regular hVDD0 he hgnd hvdd
    ⟨hx0.1, by linarith [hx0.2, hy0.1, hy0.2]⟩
  have hry := h2.out_mem_rails h2n.passive h2n.regular h2p.passive h2p.regular hVDD0 he hgnd hvdd
    ⟨by linarith [hx0.1, hx0.2, hy0.1], hy0.2⟩
  have hIfall : 0 < S.Ifall := sub_pos.2 hS.K6
  have hIrise : 0 < S.Irise := sub_pos.2 hS.K5
  have key := invariant_of_strict (ι := Bool) (a := a) (b := b)
    (g := fun i t => bif i then S.VOH - e t y else e t x - S.VOL)
    (g' := fun i t => bif i then -N.vf (u t) (e t) y else N.vf (u t) (e t) x)
    (fun i => by
      cases i
      · exact (continuousOn_pi.1 he.continuousOn x).sub continuousOn_const
      · exact continuousOn_const.sub (continuousOn_pi.1 he.continuousOn y))
    (fun i t ht => by
      cases i
      · exact (hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) x).sub_const S.VOL
      · exact (hasDerivWithinAt_pi.1 (he.hasDerivWithinAt t ht) y).const_sub S.VOH)
    (fun i => by
      cases i
      · exact sub_nonpos.2 hx0.2
      · exact sub_nonpos.2 hy0.1)
    (fun t ht hall i hi => by
      have htI := Ico_subset_Icc_self ht
      have hxt : e t x ≤ S.VOL := sub_nonpos.1 (hall false)
      have hyt : S.VOH ≤ e t y := sub_nonpos.1 (hall true)
      cases i
      · have hxe : e t x = S.VOL := sub_eq_zero.1 hi
        have hF := h1.F_out_le_neg_Ifall hS h1n h1p hVDD (hgnd t htI) (hvdd t htI)
          (show S.VIH ≤ pot (u t) (e t) (.state y) by rw [pot_state]; linarith)
          ⟨hxe.ge, (hrx t htI).2⟩
        show N.F (u t) (e t) x / N.C x (e t x) < 0
        exact div_neg_of_neg_of_pos (by linarith) (N.C_pos x _)
      · have hye : e t y = S.VOH := (sub_eq_zero.1 hi).symm
        have hF := h2.Irise_le_F_out hS h2n h2p hVDD (hgnd t htI) (hvdd t htI)
          (show pot (u t) (e t) (.state x) ≤ S.VIL by rw [pot_state]; linarith)
          ⟨(hry t htI).1, hye.le⟩
        show -(N.F (u t) (e t) y / N.C y (e t y)) < 0
        exact neg_neg_of_pos (div_pos (by linarith) (N.C_pos y _)))
  exact fun t ht => ⟨sub_nonpos.1 (key t ht false), sub_nonpos.1 (key t ht true)⟩

end AsmPhys
