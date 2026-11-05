module

public import Omega.Tensor.SymmetrizationOperations
public import Omega.Tensor.MatrixMultiplication

/-!
# Tensor identities used to combine value witnesses

These are explicit restrictions coming from coordinate reindexings. They
distribute powers over products, commute powers with symmetrization, and
combine repeated square matrix-multiplication blocks.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

omit [Fintype I'] [Fintype J'] [Fintype L'] in
/-- Applying the same factor maps in every coordinate gives a restriction of powers. -/
theorem Restricts.kroneckerPower {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Restricts T S) (n : ℕ) : Restricts (kroneckerPower T n) (kroneckerPower S n) := by
  obtain ⟨A, B, C, rfl⟩ := h
  exact ⟨matrixPower A n, matrixPower B n, matrixPower C n, map_kroneckerPower A B C T n⟩

/-- Tensor equivalence is preserved by every nonnegative power. -/
theorem Equivalent.kroneckerPower {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Equivalent T S) (n : ℕ) :
    Equivalent (kroneckerPower T n) (kroneckerPower S n) :=
  ⟨h.1.kroneckerPower n, h.2.kroneckerPower n⟩

/-- Powering a product is equivalent to multiplying the two powers. -/
theorem kroneckerPower_kronecker_equivalent (T : Tensor R I J L)
    (S : Tensor R I' J' L') (n : ℕ) :
    Equivalent (kroneckerPower (kronecker T S) n)
      (kronecker (kroneckerPower T n) (kroneckerPower S n)) :=
  equivalent_of_reindex _ _ _ (kroneckerPower_kronecker_reindex T S n)

/-- Iterating a tensor power multiplies the two exponents. -/
theorem kroneckerPower_mul_equivalent (T : Tensor R I J L) (k n : ℕ) :
    Equivalent (kroneckerPower (kroneckerPower T k) n) (kroneckerPower T (n * k)) :=
  equivalent_of_reindex _ _ _ (kroneckerPower_mul_reindex T k n)

/-- Powering the three cyclic factors commutes with their product. -/
theorem cyclicSymmetrize_kroneckerPower_equivalent (T : Tensor R I J L) (n : ℕ) :
    Equivalent (cyclicSymmetrize (kroneckerPower T n))
      (kroneckerPower (cyclicSymmetrize T) n) := by
  exact ((kroneckerPower_kronecker_equivalent T
    (kronecker (rotate T) (rotate (rotate T))) n).trans
    ((Equivalent.refl _).kronecker
      (kroneckerPower_kronecker_equivalent (rotate T) (rotate (rotate T)) n))).symm

/-- Symmetrization commutes with every tensor power. -/
theorem symmetrize_kroneckerPower_equivalent (T : Tensor R I J L) (n : ℕ) :
    Equivalent (symmetrize (kroneckerPower T n)) (kroneckerPower (symmetrize T) n) := by
  exact ((cyclicSymmetrize_kroneckerPower_equivalent T n).kronecker
    (cyclicSymmetrize_kroneckerPower_equivalent (swapFirstTwo T) n)).trans
      (kroneckerPower_kronecker_equivalent (cyclicSymmetrize T)
        (cyclicSymmetrize (swapFirstTwo T)) n).symm

/-- Iterate a power after symmetrizing a power, keeping the exponent order
used in fractional-value witnesses. -/
theorem symmetrize_kroneckerPower_iterated_equivalent
    (T : Tensor R I J L) (n N : ℕ) :
    Equivalent (kroneckerPower (symmetrize (kroneckerPower T n)) N)
      (kroneckerPower (symmetrize T) (n * N)) := by
  have h := ((symmetrize_kroneckerPower_equivalent T n).kroneckerPower N).trans
    (kroneckerPower_mul_equivalent (symmetrize T) n N)
  rw [Nat.mul_comm N n] at h
  exact h

/-- Reorder four tensor factors by interchanging the two middle factors. -/
theorem kronecker_four_shuffle_equivalent
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I₁] [Fintype J₁] [Fintype L₁] [Fintype I₂] [Fintype J₂] [Fintype L₂]
    (T : Tensor R I J L) (S : Tensor R I' J' L')
    (U : Tensor R I₁ J₁ L₁) (V : Tensor R I₂ J₂ L₂) :
    Equivalent (kronecker (kronecker T S) (kronecker U V))
      (kronecker (kronecker T U) (kronecker S V)) := by
  apply equivalent_of_reindex (Equiv.prodProdProdComm I I' I₁ I₂)
    (Equiv.prodProdProdComm J J' J₁ J₂) (Equiv.prodProdProdComm L L' L₁ L₂)
  funext i j k
  change (T i.1.1 j.1.1 k.1.1 * S i.2.1 j.2.1 k.2.1) *
      (U i.1.2 j.1.2 k.1.2 * V i.2.2 j.2.2 k.2.2) = _
  simp only [kronecker]
  ac_rfl

/-- The number of identical blocks multiplies under Kronecker products. -/
theorem directSumCopies_kronecker_equivalent (T : Tensor R I J L)
    (S : Tensor R I' J' L') (a b : ℕ) :
    Equivalent (kronecker (directSumCopies T a) (directSumCopies S b))
      (directSumCopies (kronecker T S) (a * b)) :=
  (kronecker_four_shuffle_equivalent (diagonal R a) T (diagonal R b) S).trans
    ((diagonal_kronecker_equivalent a b).kronecker (Equivalent.refl _))

/-- Products of repeated square matrix-multiplication blocks multiply both sizes. -/
theorem matrixMul_copies_kronecker_equivalent (a b c d : ℕ) :
    Equivalent
      (kronecker (directSumCopies (matrixMul R b b b) a)
        (directSumCopies (matrixMul R d d d) c))
      (directSumCopies (matrixMul R (b * d) (b * d) (b * d)) (a * c)) :=
  (directSumCopies_kronecker_equivalent _ _ a c).trans
    ((Equivalent.refl (diagonal R (a * c))).kronecker
      (matrixMul_kronecker_equivalent R b b b d d d))

/-- Powers of repeated square matrix-multiplication blocks power both sizes. -/
theorem matrixMul_copies_kroneckerPower_equivalent (a b n : ℕ) :
    Equivalent (kroneckerPower (directSumCopies (matrixMul R b b b) a) n)
      (directSumCopies (matrixMul R (b ^ n) (b ^ n) (b ^ n)) (a ^ n)) :=
  (kroneckerPower_directSumCopies_equivalent _ a n).trans
    ((Equivalent.refl (diagonal R (a ^ n))).kronecker
      (matrixMul_kroneckerPower_equivalent R b b b n))

/-- Normalize the source of a powered value-witness degeneration. -/
theorem valueSource_kroneckerPower_equivalent (T : Tensor R I J L) (c d N n : ℕ) :
    Equivalent
      (kroneckerPower (kronecker (directSumCopies (matrixMul R d d d) c)
        (kroneckerPower T N)) n)
      (kronecker (directSumCopies (matrixMul R (d ^ n) (d ^ n) (d ^ n)) (c ^ n))
        (kroneckerPower T (N * n))) := by
  have h := (kroneckerPower_kronecker_equivalent _ _ n).trans
    ((matrixMul_copies_kroneckerPower_equivalent (R := R) c d n).kronecker
      (kroneckerPower_mul_equivalent T N n))
  rw [Nat.mul_comm n N] at h
  exact h

end MatrixMultiplication.Tensor
