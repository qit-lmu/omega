module

public import Omega.Tensor.ValueOperations

/-!
# Regrouping a matrix-block factor in a value witness
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R]
variable {I J L I' J' L' I'' J'' L'' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']
variable [Fintype I''] [Fintype J''] [Fintype L'']

/-- Reassociate three Kronecker factors. -/
theorem kronecker_assoc_equivalent (T : Tensor R I J L)
    (S : Tensor R I' J' L') (U : Tensor R I'' J'' L'') :
    Equivalent (kronecker (kronecker T S) U) (kronecker T (kronecker S U)) := by
  apply equivalent_of_reindex (Equiv.prodAssoc I I' I'')
    (Equiv.prodAssoc J J' J'') (Equiv.prodAssoc L L' L'')
  funext i j k
  exact mul_assoc _ _ _

/-- Exchange the second and third entries of a left-associated triple. -/
def swapTripleLastEquiv (A B C : Type*) : ((A × B) × C) ≃ ((A × C) × B) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Move a middle Kronecker factor to the right. -/
theorem kronecker_swap_last_equivalent (T : Tensor R I J L)
    (S : Tensor R I' J' L') (U : Tensor R I'' J'' L'') :
    Equivalent (kronecker (kronecker T S) U) (kronecker (kronecker T U) S) := by
  apply equivalent_of_reindex (swapTripleLastEquiv I I' I'')
    (swapTripleLastEquiv J J' J'') (swapTripleLastEquiv L L' L'')
  funext i j k
  exact mul_right_comm _ _ _

/-- A matrix-block factor in the symmetrization can be absorbed into the
auxiliary matrix blocks of a witness. -/
theorem valueSource_matrixBlock_equivalent {T : Tensor R I J L}
    {S : Tensor R I' J' L'} (r q : ℕ)
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul R q q q) r) (symmetrize T)))
    (c d N : ℕ) :
    Equivalent
      (kronecker (directSumCopies (matrixMul R d d d) c)
        (kroneckerPower (symmetrize S) N))
      (kronecker
        (directSumCopies (matrixMul R (d * q ^ N) (d * q ^ N) (d * q ^ N)) (c * r ^ N))
        (kroneckerPower (symmetrize T) N)) := by
  have hp := ((h.kroneckerPower N).trans (kroneckerPower_kronecker_equivalent _ _ N)).trans
    ((matrixMul_copies_kroneckerPower_equivalent (R := R) r q N).kronecker
      (Equivalent.refl _))
  exact ((Equivalent.refl _).kronecker hp).trans
    ((kronecker_assoc_equivalent _ _ _).symm.trans
      ((matrixMul_copies_kronecker_equivalent (R := R) c d (r ^ N) (q ^ N)).kronecker
        (Equivalent.refl _)))

/-- One identical block is equivalent to the original tensor. -/
theorem directSumCopies_one_equivalent (T : Tensor R I J L) :
    Equivalent (directSumCopies T 1) T := by
  apply equivalent_of_reindex (Equiv.uniqueProd I (Fin 1))
    (Equiv.uniqueProd J (Fin 1)) (Equiv.uniqueProd L (Fin 1))
  funext i j k
  simp [reindex, directSumCopies, kronecker, diagonal, Equiv.uniqueProd_symm_apply]

/-- A repeated scalar-multiplication tensor is the diagonal tensor. -/
theorem matrixMul_one_copies_equivalent_diagonal (r : ℕ) :
    Equivalent (directSumCopies (matrixMul R 1 1 1) r) (diagonal R r) := by
  have h := ((Equivalent.refl (diagonal R r)).kronecker
    (matrixMul_one_equivalent_diagonal R)).trans (diagonal_kronecker_equivalent r 1)
  rw [Nat.mul_one] at h
  exact h

end MatrixMultiplication.Tensor
