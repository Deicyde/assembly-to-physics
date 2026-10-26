import AsmPhys.Spec.Circuit
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

/-!
# THM L2.1 — Tellegen's theorem

For any directed multigraph with incidence matrix `A`, if the branch voltages are potential
differences (`v = Aᵀ e`) and the branch currents satisfy KCL (`A i = 0`), then `v · i = 0`.
-/

namespace AsmPhys

open Matrix

/-- `Aᵀ e` is the vector of potential differences `e(tail β) − e(head β)`. -/
theorem incidence_transpose_mulVec {V Br : Type*} [Fintype V] [DecidableEq V]
    (tail head : Br → V) (e : V → ℝ) (β : Br) :
    ((incidence tail head)ᵀ *ᵥ e) β = e (tail β) - e (head β) := by
  simp [incidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- **THM L2.1** (Tellegen), for any matrix: if `v = Aᵀ e` and `A i = 0`, then `v ⬝ i = 0`. -/
theorem tellegen_matrix {V Br : Type*} [Fintype V] [Fintype Br] (A : Matrix V Br ℝ)
    (e : V → ℝ) (v i : Br → ℝ) (hv : v = Aᵀ *ᵥ e) (hi : A *ᵥ i = 0) : v ⬝ᵥ i = 0 := by
  rw [hv, mulVec_transpose, ← dotProduct_mulVec, hi, dotProduct_zero]

/-- **THM L2.1** (Tellegen): for any directed multigraph, if `v = Aᵀ e` and `A i = 0`, then
`v ⬝ i = 0`. -/
theorem tellegen {V Br : Type*} [Fintype V] [DecidableEq V] [Fintype Br] (tail head : Br → V)
    (e : V → ℝ) (v i : Br → ℝ) (hv : v = (incidence tail head)ᵀ *ᵥ e)
    (hi : incidence tail head *ᵥ i = 0) : v ⬝ᵥ i = 0 :=
  tellegen_matrix _ e v i hv hi

end AsmPhys
