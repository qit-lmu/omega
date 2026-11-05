module

public import Omega.ExponentSize
public import Omega.Tensor.DirectSumCopies

/-!
# Capacity comparisons for blocks of matrix multiplication

A diagonal tensor with sufficiently many entries can realize any prescribed
rank decomposition. Combined with matrix-multiplication blocks, this gives the
capacity inequality used in the equal-block asymptotic sum argument.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- A larger diagonal tensor restricts to every smaller diagonal tensor. -/
theorem diagonal_restricts_of_le (R : Type*) [CommSemiring R]
    {r s : ℕ} (h : r ≤ s) : Restricts (diagonal R s) (diagonal R r) := by
  classical
  let A : Matrix (Fin r) (Fin s) R :=
    fun i j => if j = Fin.castLE h i then 1 else 0
  refine ⟨A, A, A, ?_⟩
  funext i j k
  by_cases hjk : j = k
  · subst k
    simp [map, A, diagonal, ite_and, eq_comm]
  · simp [map, A, diagonal, ite_and, hjk, Ne.symm hjk]

/-- A rank bound is witnessed by a restriction from a diagonal tensor of that size. -/
theorem diagonal_restricts_of_rank_le {R I J L : Type*} [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) {r : ℕ} (h : rank T ≤ r) :
    Restricts (diagonal R r) T :=
  (diagonal_restricts_of_le R h).trans (diagonal_restricts_of_rank T)

/-- Asymptotic rank is multiplicative for two square matrix-multiplication tensors. -/
theorem asymptoticRank_matrixMul_kronecker_eq (K : Type*) [Field K]
    (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    asymptoticRank (kronecker (matrixMul K u u u) (matrixMul K v v v)) =
      asymptoticRank (matrixMul K u u u) * asymptoticRank (matrixMul K v v v) := by
  rw [asymptoticRank_eq_of_equivalent (matrixMul_kronecker_equivalent K u u u v v v)]
  rw [asymptoticRank_matrixMul_square K (u * v)
      (by simpa only [Nat.one_mul] using Nat.mul_le_mul hu hv),
    asymptoticRank_matrixMul_square K u hu, asymptoticRank_matrixMul_square K v hv]
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- Multiplicativity for products of tensor powers of two positive square sizes. -/
theorem asymptoticRank_matrixMul_power_kronecker_eq (K : Type*) [Field K]
    (u v n m : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    asymptoticRank (kronecker (kroneckerPower (matrixMul K u u u) n)
      (kroneckerPower (matrixMul K v v v) m)) =
        asymptoticRank (matrixMul K u u u) ^ n *
          asymptoticRank (matrixMul K v v v) ^ m := by
  have hu' := matrixMul_kroneckerPower_equivalent K u u u n
  have hv' := matrixMul_kroneckerPower_equivalent K v v v m
  have he : Equivalent
      (kronecker (kroneckerPower (matrixMul K u u u) n)
        (kroneckerPower (matrixMul K v v v) m))
      (kronecker (matrixMul K (u ^ n) (u ^ n) (u ^ n))
        (matrixMul K (v ^ m) (v ^ m) (v ^ m))) :=
    ⟨hu'.1.kronecker hv'.1, hu'.2.kronecker hv'.2⟩
  rw [asymptoticRank_eq_of_equivalent he,
    asymptoticRank_matrixMul_kronecker_eq K (u ^ n) (v ^ m)
      (one_le_pow₀ hu) (one_le_pow₀ hv),
    asymptoticRank_matrixMul_pow, asymptoticRank_matrixMul_pow,
    asymptoticRank_pow, asymptoticRank_pow]

/-- If the number of blocks can realize a power of two-by-two matrix
multiplication, then the repeated block tensor has the corresponding capacity. -/
theorem matrixMul_capacity_inequality (K : Type*) [Field K]
    (a b n m : ℕ) (hb : 1 ≤ b)
    (hcap : rank (kroneckerPower (matrixMul K 2 2 2) n) ≤ a ^ m) :
    asymptoticRank (matrixMul K 2 2 2) ^ n * ((b : ℝ) ^ omega K) ^ m ≤
      asymptoticRank (directSumCopies (matrixMul K b b b) a) ^ m := by
  have hd := diagonal_restricts_of_rank_le
    (kroneckerPower (matrixMul K 2 2 2) n) hcap
  have ht := hd.kronecker (Restricts.refl (kroneckerPower (matrixMul K b b b) m))
  have hc := (kroneckerPower_directSumCopies_equivalent (matrixMul K b b b) a m).1
  have h := asymptoticRank_mono (hc.trans ht)
  rw [asymptoticRank_matrixMul_power_kronecker_eq K 2 b n m (by decide) hb,
    asymptoticRank_pow, asymptoticRank_matrixMul_square K b hb] at h
  exact h

end MatrixMultiplication.Tensor
