module

public import Omega.Tensor.FactorPermutations
public import Omega.Tensor.AsymptoticOperations

/-!
# Kronecker symmetrization over all six factor permutations

The three cyclic permutations form one product. Multiplying it by the three
cyclic permutations of the transposition gives exactly the six elements of
the symmetric group on three letters, each occurring once.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L : Type*}

/-- The product of the identity permutation and the two nontrivial rotations. -/
def cyclicSymmetrize [Mul R] (T : Tensor R I J L) :
    Tensor R (I × J × L) (J × L × I) (L × I × J) :=
  kronecker T (kronecker (rotate T) (rotate (rotate T)))

/-- Kronecker symmetrization: the product of all six permutations of the
three tensor factors. The first cyclic product contains the even permutations;
the second contains the odd permutations. -/
def symmetrize [Mul R] (T : Tensor R I J L) :
    Tensor R ((I × J × L) × (J × I × L))
      ((J × L × I) × (I × L × J)) ((L × I × J) × (L × J × I)) :=
  kronecker (cyclicSymmetrize T) (cyclicSymmetrize (swapFirstTwo T))

/-- The product of the three rotations has asymptotic rank at most the cube. -/
theorem asymptoticRank_cyclicSymmetrize_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank (cyclicSymmetrize T) ≤ asymptoticRank T ^ 3 := by
  have h := asymptoticRank_kronecker_le (rotate T) (rotate (rotate T))
  simp only [asymptoticRank_rotate] at h
  calc
    _ ≤ asymptoticRank T * asymptoticRank (kronecker (rotate T) (rotate (rotate T))) :=
      asymptoticRank_kronecker_le _ _
    _ ≤ asymptoticRank T * (asymptoticRank T * asymptoticRank T) :=
      mul_le_mul_of_nonneg_left h (asymptoticRank_nonneg T)
    _ = _ := by ring

/-- Taking all six factor permutations costs at most the sixth power in
asymptotic rank. This holds over every commutative semiring. -/
theorem asymptoticRank_symmetrize_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank (symmetrize T) ≤ asymptoticRank T ^ 6 := by
  have h := asymptoticRank_cyclicSymmetrize_le (swapFirstTwo T)
  rw [asymptoticRank_swapFirstTwo] at h
  calc
    _ ≤ asymptoticRank (cyclicSymmetrize T) *
        asymptoticRank (cyclicSymmetrize (swapFirstTwo T)) :=
      asymptoticRank_kronecker_le _ _
    _ ≤ asymptoticRank T ^ 3 * asymptoticRank T ^ 3 :=
      mul_le_mul (asymptoticRank_cyclicSymmetrize_le T) h
        (asymptoticRank_nonneg _) (pow_nonneg (asymptoticRank_nonneg T) _)
    _ = _ := by ring

end MatrixMultiplication.Tensor
