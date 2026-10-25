import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

/-!
# THM L2.1 — Tellegen's theorem

For any directed multigraph with incidence matrix `A`, if the branch voltages are potential
differences (`v = Aᵀ e`) and the branch currents satisfy KCL (`A i = 0`), then `v · i = 0`.
-/

namespace AsmPhys

open Matrix

/-- Incidence matrix of a directed multigraph whose branch `β` runs from `tail β` to `head β`:
`A k β = +1` if `k = tail β`, `−1` if `k = head β`, and `0` otherwise (so `0` on a self-loop). -/
def incidence {V Br : Type*} [DecidableEq V] (tail head : Br → V) : Matrix V Br ℝ :=
  Matrix.of fun k β => (if k = tail β then 1 else 0) - (if k = head β then 1 else 0)

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
