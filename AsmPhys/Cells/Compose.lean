import AsmPhys.Spec.Cells
import AsmPhys.Cells.Levels
import AsmPhys.Circuit.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# THM L3.4 — Combinational timing, per node

Cells and combinational DAGs are defined in `AsmPhys.Spec.Cells`. THM L3.4: if every DAG input is
`validIn` on its window and `a(m) ≤ min_{In(m)} b` for every cell `m` in a node's fan-in cone, then
that node is `validIn` of its value on its window. Dead logic outside the cone cannot block the
theorem.
-/

namespace AsmPhys

open Set

variable {n m : ℕ}

namespace CombDAG

variable (D : CombDAG n m)

/-- Cone membership is transitive. -/
theorem InCone.trans {i i' i'' : Fin D.nc} (h₁ : D.InCone i'' i') (h₂ : D.InCone i' i) :
    D.InCone i'' i := by
  induction h₁ with
  | refl => exact h₂
  | step j _ hs ih => exact .step j (ih h₂) hs

/-- `val` unfolded once, with each slot's value written as an `Option.elim` over its driver. -/
theorem val_eq (x : Node n m → Bool) (i : Fin D.nc) :
    D.val x i = (D.cell i).f fun j => (D.src i j).elim (x ((D.cell i).ins j)) (D.val x) := by
  rw [val.eq_1]
  congr 1
  funext j
  split <;> simp_all

/-- Each slot's arrival time (`a` of an undriven slot's node, `a(i')` of a slot driven by `i'`)
is at most `max_{In(i)} a`. -/
theorem le_inA (a : Node n m → ℝ) (i : Fin D.nc) (j : Fin (D.cell i).ar) :
    (D.src i j).elim (a ((D.cell i).ins j)) (D.arr a) ≤ D.inA a i := by
  rw [inA.eq_1]
  refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ j))
  split <;> simp_all [arr]

/-- `min_{In(i)} b` is at most each slot's expiry time (`b` of an undriven slot's node, `b(i')` of
a slot driven by `i'`). -/
theorem inB_le (b : Node n m → ℝ) (i : Fin D.nc) (j : Fin (D.cell i).ar) :
    D.inB b i ≤ (D.src i j).elim (b ((D.cell i).ins j)) (D.exp b) := by
  rw [inB.eq_1]
  refine le_trans (Finset.inf'_le _ (Finset.mem_univ j)) (le_of_eq ?_)
  split <;> simp_all [exp]

/-- THM L3.4 with the arrival bound carried through the induction: under the hypotheses of
`timing`, `A ≤ a(i)` and `i`'s output is `validIn` of its value on `[a(i), b(i)]`, up to `B`. -/
theorem timing_aux {S : Params} (hS : S.Consistent)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {A B : ℝ}
    (hbeh : ∀ i, (D.cell i).Behaves S u e A B)
    (x : Node n m → Bool) (a b : Node n m → ℝ)
    (hin : ∀ i j, D.src i j = none →
      A ≤ a ((D.cell i).ins j) ∧
        ∀ t ∈ Icc (a ((D.cell i).ins j)) (b ((D.cell i).ins j)), t ≤ B →
          S.validIn (x ((D.cell i).ins j)) (pot (u t) (e t) ((D.cell i).ins j)))
    (i : Fin D.nc)
    (hwin : ∀ i', D.InCone i' i → D.arr a i' ≤ D.inB b i') :          -- THM (finite check)
    A ≤ D.arr a i ∧
      ∀ t ∈ Icc (D.arr a i) (D.exp b i), t ≤ B → S.validIn (D.val x i) (e t (D.cell i).out) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  have hb := hbeh i
  -- Each slot starts no earlier than `A` and is `validIn` of its value on its window, up to `B`.
  have hslot : ∀ j, A ≤ (D.src i j).elim (a ((D.cell i).ins j)) (D.arr a) ∧
      ∀ t ∈ Icc ((D.src i j).elim (a ((D.cell i).ins j)) (D.arr a))
        ((D.src i j).elim (b ((D.cell i).ins j)) (D.exp b)), t ≤ B →
        S.validIn ((D.src i j).elim (x ((D.cell i).ins j)) (D.val x))
          (pot (u t) (e t) ((D.cell i).ins j)) := by
    intro j
    cases hs : D.src i j with
    | none => exact hin i j hs
    | some i' =>
      have hcone : D.InCone i' i := .step j (.refl i) hs
      obtain ⟨h1, h2⟩ := ih i' (D.src_lt i j i' hs) fun k hk => hwin k (InCone.trans D hk hcone)
      refine ⟨h1, fun t ht htB => ?_⟩
      rw [D.src_some i j i' hs, pot_state]
      exact h2 t ht htB
  have j₀ : Fin (D.cell i).ar := ⟨0, (D.cell i).ar_pos⟩
  have hAin : A ≤ D.inA a i := (hslot j₀).1.trans (D.le_inA a i j₀)
  have hArr : A ≤ D.arr a i := le_add_of_le_of_nonneg hAin hb.tpd_nonneg
  -- THM L3.1(a) on `[max_{In(i)} a, min (min_{In(i)} b) B]`.
  have hout : ∀ t ∈ Icc (D.arr a i) (min (D.inB b i) B),
      S.validOut (D.val x i) (e t (D.cell i).out) := by
    rw [D.val_eq x i]
    refine hb.prop _ (D.inA a i) (min (D.inB b i) B) hAin (min_le_right _ _) ?_
    intro j t ht
    exact (hslot j).2 t ⟨(D.le_inA a i j).trans ht.1,
      (ht.2.trans (min_le_left _ _)).trans (D.inB_le b i j)⟩ (ht.2.trans (min_le_right _ _))
  refine ⟨hArr, fun t ht htB => ?_⟩
  rcases le_or_gt t (D.inB b i) with htb | htb
  · exact hS.validIn_of_validOut (hout t ⟨ht.1, le_min htb htB⟩)
  -- Past `min_{In(i)} b`: THM L3.2 from the valid output at `min_{In(i)} b`.
  have hwi : D.arr a i ≤ D.inB b i := hwin i (.refl i)
  have hiB : D.inB b i ≤ B := htb.le.trans htB
  exact hb.contam _ (D.inB b i) ⟨hArr.trans hwi, hiB⟩ (hout _ ⟨hwi, le_min le_rfl hiB⟩) t
    ⟨htb.le, le_min htB ht.2⟩

/-- **THM L3.4** (combinational timing, per node). Every cell behaves along `e` on `[A, B]`, and
every DAG input slot is `validIn` of its value on its window `[a, b]`, which starts no earlier than
`A`. If `a(i') ≤ min_{In(i')} b` for every cell `i'` in the fan-in cone of `i`, then `i`'s output
is `validIn` of its value on `[a(i), b(i)]`, up to `B`. -/
theorem timing {S : Params} (hS : S.Consistent)                       -- THM (norm_num)
    {u : ℝ → Fin m → ℝ} {e : ℝ → Fin n → ℝ} {A B : ℝ}
    (hbeh : ∀ i, (D.cell i).Behaves S u e A B)                    -- MODEL (H_cells)
    (x : Node n m → Bool) (a b : Node n m → ℝ)
    (hin : ∀ i j, D.src i j = none →
      A ≤ a ((D.cell i).ins j) ∧
        ∀ t ∈ Icc (a ((D.cell i).ins j)) (b ((D.cell i).ins j)), t ≤ B →
          S.validIn (x ((D.cell i).ins j)) (pot (u t) (e t) ((D.cell i).ins j)))
    (i : Fin D.nc)
    (hwin : ∀ i', D.InCone i' i → D.arr a i' ≤ D.inB b i') :          -- THM (finite check)
    ∀ t ∈ Icc (D.arr a i) (D.exp b i), t ≤ B → S.validIn (D.val x i) (e t (D.cell i).out) :=
  (D.timing_aux hS hbeh x a b hin i hwin).2

end CombDAG

end AsmPhys
