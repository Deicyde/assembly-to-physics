import AsmPhys.Spec.Circuit

/-!
# Node potentials

Simp lemmas for `pot`.
-/

namespace AsmPhys

variable {n m : ℕ}

@[simp] lemma pot_state (u : Fin m → ℝ) (e : Fin n → ℝ) (k : Fin n) :
    pot u e (.state k) = e k := rfl

@[simp] lemma pot_bdry (u : Fin m → ℝ) (e : Fin n → ℝ) (j : Fin m) :
    pot u e (.bdry j) = u j := rfl

end AsmPhys
