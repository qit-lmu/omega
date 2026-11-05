module

public import Omega.Tensor.Symmetrization
public import Omega.Tensor.MatrixMultiplication

/-!
# Symmetrization of matrix multiplication

Cyclically permuting the factors of a matrix-multiplication tensor cyclically
permutes its three matrix dimensions. The product of these three tensors is
square matrix multiplication of size `l*m*n`. The other three permutations
give a second copy, so the full symmetrization has square size `(l*m*n)^2`.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable (R : Type*) [CommSemiring R]

/-- Rotating the factors cyclically rotates the matrix dimensions, after
transposing the pair indices in the second and third factors. -/
theorem matrixMul_rotate_reindex (l m n : ℕ) :
    reindex (Equiv.refl (Fin m × Fin n)) (Equiv.prodComm (Fin l) (Fin n))
      (Equiv.prodComm (Fin l) (Fin m)) (rotate (matrixMul R l m n)) =
      matrixMul R m n l := by
  funext i j k
  simp [reindex, rotate, matrixMul, eq_comm, and_comm, and_left_comm]

/-- A rotation of matrix multiplication is equivalent to cyclically rotated
matrix dimensions. -/
theorem matrixMul_rotate_equivalent (l m n : ℕ) :
    Equivalent (rotate (matrixMul R l m n)) (matrixMul R m n l) :=
  equivalent_of_reindex _ _ _ (matrixMul_rotate_reindex R l m n)

/-- Two factor rotations give the other cyclic permutation of dimensions. -/
theorem matrixMul_rotate_rotate_equivalent (l m n : ℕ) :
    Equivalent (rotate (rotate (matrixMul R l m n))) (matrixMul R n l m) := by
  apply equivalent_of_reindex (Equiv.prodComm (Fin l) (Fin n))
    (Equiv.refl (Fin l × Fin m)) (Equiv.prodComm (Fin m) (Fin n))
  funext i j k
  simp [reindex, rotate, matrixMul, eq_comm, and_assoc, and_comm]

/-- Swapping the input factors reverses the outer matrix dimensions, after
transposing all three pair indices. -/
theorem matrixMul_swapFirstTwo_reindex (l m n : ℕ) :
    reindex (Equiv.prodComm (Fin m) (Fin n)) (Equiv.prodComm (Fin l) (Fin m))
      (Equiv.prodComm (Fin l) (Fin n)) (swapFirstTwo (matrixMul R l m n)) =
      matrixMul R n m l := by
  funext i j k
  simp [reindex, swapFirstTwo, matrixMul, eq_comm, and_assoc, and_comm]
  rfl

/-- Swapping the input factors is equivalent to reversing the outer dimensions. -/
theorem matrixMul_swapFirstTwo_equivalent (l m n : ℕ) :
    Equivalent (swapFirstTwo (matrixMul R l m n)) (matrixMul R n m l) :=
  equivalent_of_reindex _ _ _ (matrixMul_swapFirstTwo_reindex R l m n)

/-- The product of the three cyclic permutations is square matrix multiplication. -/
theorem cyclicSymmetrize_matrixMul (l m n : ℕ) :
    Equivalent (cyclicSymmetrize (matrixMul R l m n))
      (matrixMul R (l * m * n) (l * m * n) (l * m * n)) := by
  have hrotate := (Equivalent.refl (matrixMul R l m n)).kronecker
    ((matrixMul_rotate_equivalent R l m n).kronecker
      (matrixMul_rotate_rotate_equivalent R l m n))
  have hinner := (Equivalent.refl (matrixMul R l m n)).kronecker
    (matrixMul_kronecker_equivalent R m n l n l m)
  have houter := matrixMul_kronecker_equivalent R l m n (m * n) (n * l) (l * m)
  have h := hrotate.trans (hinner.trans houter)
  have hfirst : l * (m * n) = l * m * n := by ac_rfl
  have hsecond : m * (n * l) = l * m * n := by ac_rfl
  have hthird : n * (l * m) = l * m * n := by ac_rfl
  rw [hfirst, hsecond, hthird] at h
  exact h

private theorem cyclicSymmetrize_reindex
    {I J L I' J' L' : Type*} (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    (T : Tensor R I J L) :
    reindex (eI.prodCongr (eJ.prodCongr eL)) (eJ.prodCongr (eL.prodCongr eI))
      (eL.prodCongr (eI.prodCongr eJ)) (cyclicSymmetrize T) =
      cyclicSymmetrize (reindex eI eJ eL T) := rfl

/-- The six factor permutations of matrix multiplication give a square tensor
of size `(l*m*n)^2`, as in manuscript Lemma `sym-properties`, item four. -/
theorem symmetrize_matrixMul (l m n : ℕ) :
    Equivalent (symmetrize (matrixMul R l m n))
      (matrixMul R ((l * m * n) ^ 2) ((l * m * n) ^ 2) ((l * m * n) ^ 2)) := by
  have he := cyclicSymmetrize_reindex R (Equiv.prodComm (Fin m) (Fin n))
    (Equiv.prodComm (Fin l) (Fin m)) (Equiv.prodComm (Fin l) (Fin n))
    (swapFirstTwo (matrixMul R l m n))
  rw [matrixMul_swapFirstTwo_reindex] at he
  have hswap := (equivalent_of_reindex _ _ _ he).trans
    (cyclicSymmetrize_matrixMul R n m l)
  have hboth := (cyclicSymmetrize_matrixMul R l m n).kronecker hswap
  have hproduct := matrixMul_kronecker_equivalent R (l * m * n) (l * m * n)
    (l * m * n) (n * m * l) (n * m * l) (n * m * l)
  have h := hboth.trans hproduct
  have hsize : l * m * n * (n * m * l) = (l * m * n) ^ 2 := by
    rw [pow_two]
    ac_rfl
  rw [hsize] at h
  exact h

end MatrixMultiplication.Tensor
