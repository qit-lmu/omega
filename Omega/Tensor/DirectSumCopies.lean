module

public import Omega.Tensor.AsymptoticOperations
public import Omega.Tensor.FlatteningExamples
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Repeated direct sums of a tensor

The tensor `directSumCopies T a` has `a` independent blocks, each equal to
`T`. It is represented as the Kronecker product of the diagonal tensor of
size `a` with `T`. Its nth power consequently has `a^n` copies of `T^n`.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L : Type*}

/-- The ordinary direct sum of `a` identical copies of `T`. The first
coordinate of each basis index identifies the block. -/
def directSumCopies [Mul R] [Zero R] [One R] (T : Tensor R I J L) (a : ℕ) :
    Tensor R (Fin a × I) (Fin a × J) (Fin a × L) :=
  kronecker (diagonal R a) T

/-- Repeated direct sums have coefficient zero unless their block labels
coincide, and otherwise have the coefficient of the common tensor. -/
@[simp]
theorem directSumCopies_apply [MulZeroOneClass R] (T : Tensor R I J L) (a : ℕ)
    (i : Fin a × I) (j : Fin a × J) (k : Fin a × L) :
    directSumCopies T a i j k =
      if i.1 = j.1 ∧ j.1 = k.1 then T i.2 j.2 k.2 else 0 := by
  simp [directSumCopies, kronecker, diagonal, ite_mul]

/-- Encode a word of `n` block labels in one block label. -/
def diagonalPowerEquiv (a n : ℕ) : (Fin n → Fin a) ≃ Fin (a ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Powers of a diagonal tensor are diagonals with exponentially many labels. -/
theorem kroneckerPower_diagonal_reindex [CommMonoidWithZero R] (a n : ℕ) :
    reindex (diagonalPowerEquiv a n) (diagonalPowerEquiv a n)
      (diagonalPowerEquiv a n) (kroneckerPower (diagonal R a) n) =
      diagonal R (a ^ n) := by
  funext i j k
  simp [reindex, kroneckerPower, diagonal, Fintype.prod_boole, forall_and,
    ← funext_iff]

/-- Split a tuple of block-and-basis labels into its block word and basis tuple. -/
def directSumCopiesPowerEquiv (I : Type*) (a n : ℕ) :
    (Fin n → Fin a × I) ≃ Fin (a ^ n) × (Fin n → I) :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin a) (fun _ => I)).trans
    ((diagonalPowerEquiv a n).prodCongr (Equiv.refl _))

/-- Taking a tensor power raises the number of identical direct-sum blocks
to the same power. -/
theorem kroneckerPower_directSumCopies_reindex [CommSemiring R]
    (T : Tensor R I J L) (a n : ℕ) :
    reindex (directSumCopiesPowerEquiv I a n) (directSumCopiesPowerEquiv J a n)
      (directSumCopiesPowerEquiv L a n) (kroneckerPower (directSumCopies T a) n) =
      directSumCopies (kroneckerPower T n) (a ^ n) := by
  funext i j k
  change (∏ t, (diagonal R a)
      ((diagonalPowerEquiv a n).symm i.1 t)
      ((diagonalPowerEquiv a n).symm j.1 t)
      ((diagonalPowerEquiv a n).symm k.1 t) * T (i.2 t) (j.2 t) (k.2 t)) =
    diagonal R (a ^ n) i.1 j.1 k.1 * ∏ t, T (i.2 t) (j.2 t) (k.2 t)
  rw [Finset.prod_mul_distrib]
  congr 1
  exact congrFun (congrFun (congrFun (kroneckerPower_diagonal_reindex
    (R := R) a n) i.1) j.1) k.1

private theorem equivalent_of_reindex_eq [CommSemiring R]
    {I' J' L' : Type*} [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    (h : reindex eI eJ eL T = S) : Equivalent T S := by
  subst S
  refine ⟨restricts_reindex _ _ _ _, ?_⟩
  simpa only [reindex_symm] using restricts_reindex eI.symm eJ.symm eL.symm
    (reindex eI eJ eL T)

/-- The power identity for repeated direct sums as mutual restrictions. -/
theorem kroneckerPower_directSumCopies_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (a n : ℕ) :
    Equivalent (kroneckerPower (directSumCopies T a) n)
      (directSumCopies (kroneckerPower T n) (a ^ n)) :=
  equivalent_of_reindex_eq _ _ _ (kroneckerPower_directSumCopies_reindex T a n)

/-- The two descriptions of the power of a repeated direct sum have equal ranks. -/
theorem rank_kroneckerPower_directSumCopies [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (a n : ℕ) :
    rank (kroneckerPower (directSumCopies T a) n) =
      rank (directSumCopies (kroneckerPower T n) (a ^ n)) :=
  rank_eq_of_equivalent (kroneckerPower_directSumCopies_equivalent T a n)

/-- Selecting any one block from a positive number of copies is a restriction. -/
theorem directSumCopies_restricts [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) {a : ℕ} (ha : 0 < a) :
    Restricts (directSumCopies T a) T := by
  classical
  let c : Fin a := ⟨0, ha⟩
  refine ⟨Matrix.of (fun i p => (1 : Matrix (Fin a × I) (Fin a × I) R) (c, i) p),
    Matrix.of (fun j p => (1 : Matrix (Fin a × J) (Fin a × J) R) (c, j) p),
    Matrix.of (fun k p => (1 : Matrix (Fin a × L) (Fin a × L) R) (c, k) p), ?_⟩
  funext i j k
  simp only [map, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [directSumCopies, kronecker, diagonal]

/-- At least one block retains the asymptotic rank of the original tensor. -/
theorem asymptoticRank_le_directSumCopies [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) {a : ℕ} (ha : 0 < a) :
    asymptoticRank T ≤ asymptoticRank (directSumCopies T a) :=
  asymptoticRank_mono (directSumCopies_restricts T ha)

/-- The asymptotic rank of `a` identical blocks is at most `a` times that
of one block. -/
theorem asymptoticRank_directSumCopies_le [Field R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (a : ℕ) :
    asymptoticRank (directSumCopies T a) ≤ a * asymptoticRank T := by
  exact (asymptoticRank_kronecker_le (diagonal R a) T).trans_eq
    (by rw [asymptoticRank_diagonal])

end MatrixMultiplication.Tensor
