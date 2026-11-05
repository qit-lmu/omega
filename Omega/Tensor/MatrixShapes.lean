module

public import Omega.Tensor.FactorPermutations

/-!
# The three special shapes of matrix multiplication

Removing singleton coordinates gives the three presentations in manuscript
Definition 2.4. The right-hand sides are the coefficient tensors of
`∑ i, eᵢ ⊗ e₁ ⊗ eᵢ`, `∑ i, eᵢ ⊗ eᵢ ⊗ e₁`, and
`∑ i, e₁ ⊗ eᵢ ⊗ eᵢ`, respectively. The formulas include `n = 0`.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable (R : Type*) [CommSemiring R]

/-- The special shape `⟨n,1,1⟩`: scalar multiplication of a column vector. -/
theorem matrixMul_n_one_one_equivalent (n : ℕ) :
    Equivalent (matrixMul R n 1 1)
      (fun (i : Fin n) (_ : Fin 1) (k : Fin n) => if i = k then 1 else 0) := by
  apply equivalent_of_reindex (Equiv.prodUnique (Fin n) (Fin 1))
    (Equiv.prodUnique (Fin 1) (Fin 1)) (Equiv.prodUnique (Fin n) (Fin 1))
  funext i j k
  have hj : j = 0 := Subsingleton.elim _ _
  simp [reindex, matrixMul, Equiv.prodUnique, hj]

/-- The special shape `⟨1,n,1⟩`: the dot product. -/
theorem matrixMul_one_n_one_equivalent (n : ℕ) :
    Equivalent (matrixMul R 1 n 1)
      (fun (i j : Fin n) (_ : Fin 1) => if i = j then 1 else 0) := by
  apply equivalent_of_reindex (Equiv.uniqueProd (Fin n) (Fin 1))
    (Equiv.prodUnique (Fin n) (Fin 1)) (Equiv.prodUnique (Fin 1) (Fin 1))
  funext i j k
  have hk : k = 0 := Subsingleton.elim _ _
  simp [reindex, matrixMul, Equiv.prodUnique, Equiv.uniqueProd, hk]

/-- The special shape `⟨1,1,n⟩`: scalar multiplication of a row vector. -/
theorem matrixMul_one_one_n_equivalent (n : ℕ) :
    Equivalent (matrixMul R 1 1 n)
      (fun (_ : Fin 1) (j k : Fin n) => if j = k then 1 else 0) := by
  apply equivalent_of_reindex (Equiv.prodUnique (Fin 1) (Fin 1))
    (Equiv.uniqueProd (Fin n) (Fin 1)) (Equiv.uniqueProd (Fin n) (Fin 1))
  funext i j k
  have hi : i = 0 := Subsingleton.elim _ _
  simp [reindex, matrixMul, Equiv.prodUnique, Equiv.uniqueProd, hi]

end MatrixMultiplication.Tensor
