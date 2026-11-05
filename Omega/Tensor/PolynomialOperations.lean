module

public import Omega.Tensor.PartialSumCalculus
public import Omega.Tensor.PermutedSymmetrization

/-!
# Coordinate models for polynomial multiplication

Repeated polynomial multiplication uses a literal common first factor, so
partially direct sums can be formed without hiding an identification with a
one-dimensional factor.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R I J L : Type*}

/-- Transpose the second and third tensor factors. -/
def swapLastTwo (T : Tensor R I J L) : Tensor R I L J := fun i k j => T i j k

/-- Polynomial multiplication repeated in the second and third factors. -/
def polynomialMulCopies (R : Type*) [Zero R] [One R] (a b r : ℕ) :
    Tensor R (Fin a) (Fin b × Fin r) (Fin (a + b - 1) × Fin r) :=
  fun i j k => if j.2 = k.2 then polynomialMul R a b i j.1 k.1 else 0

/-- The two inputs of polynomial multiplication may be interchanged. -/
theorem polynomialMul_swapFirstTwo [Zero R] [One R] (a b : ℕ) :
    reindex (Equiv.refl _) (Equiv.refl _)
      (finCongr (by omega : a + b - 1 = b + a - 1))
      (swapFirstTwo (polynomialMul R a b)) = polynomialMul R b a := by
  funext i j k
  simp [reindex, swapFirstTwo, polynomialMul, Nat.add_comm]

private def copiesCoordinateEquiv (b r : ℕ) :
    (Fin b × Fin r) ≃ Fin b × (Fin 1 × Fin r) where
  toFun j := (j.1, 0, j.2)
  invFun j := (j.1, j.2.2)
  left_inv j := rfl
  right_inv j := by
    rcases j with ⟨j, u, t⟩
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    rfl

/-- The repeated coordinate model agrees with the rectangular matrix factor. -/
theorem polynomialMulCopies_equivalent [CommSemiring R] (a b r : ℕ) :
    Equivalent (polynomialMulCopies R a b r)
      (kronecker (polynomialMul R a b) (matrixMul R 1 1 r)) := by
  let : Unique (Fin 1 × Fin 1) :=
    ⟨⟨(0, 0)⟩, fun x => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  apply equivalent_of_reindex (Equiv.prodUnique (Fin a) (Fin 1 × Fin 1)).symm
    (copiesCoordinateEquiv b r) (copiesCoordinateEquiv (a + b - 1) r)
  funext i j k
  simp [reindex, polynomialMulCopies, copiesCoordinateEquiv, kronecker, matrixMul,
    Equiv.prodUnique, Subsingleton.elim i.2.1 k.2.1, Subsingleton.elim i.2.2 j.2.1,
    mul_ite]

/-- Polynomial multiplication by a scalar is rectangular matrix multiplication. -/
theorem polynomialMul_one_equivalent_matrixMul [CommSemiring R] (b : ℕ) :
    Equivalent (polynomialMul R 1 b) (matrixMul R 1 1 b) := by
  let : Unique (Fin 1 × Fin 1) :=
    ⟨⟨(0, 0)⟩, fun x => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  apply equivalent_of_reindex (Equiv.ofUnique _ _)
    (Equiv.uniqueProd (Fin b) (Fin 1)).symm
    ((finCongr (by omega : 1 + b - 1 = b)).trans
      (Equiv.uniqueProd (Fin b) (Fin 1)).symm)
  funext i j k
  have hj : j.1 = i.2 := Subsingleton.elim _ _
  have hk : k.1 = i.1 := Subsingleton.elim _ _
  simp [reindex, polynomialMul, matrixMul, Equiv.ofUnique, Equiv.uniqueProd, hj, hk, Fin.val_inj]

end MatrixMultiplication.Tensor
