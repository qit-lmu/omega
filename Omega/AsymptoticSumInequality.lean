module

public import Omega.Tensor.MatrixCapacity
public import Omega.Analysis.CapacityGrowth
public import Omega.ExponentBounds
import Mathlib.Tactic.NormNum

/-!
# The equal-block asymptotic sum inequality

This is Lemma 2.7 (`cor:asymptotic-rank-lower-bound`) of the manuscript.
Repeated square matrix-multiplication blocks have asymptotic rank equal to
the number of blocks times the asymptotic rank of one block, over every field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- Equal-block asymptotic sum identity, over every field and for all positive
numbers of blocks and matrix dimensions. -/
theorem asymptoticRank_matrixMul_directPower (K : Type*) [Field K]
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    asymptoticRank (directSumCopies (matrixMul K b b b) a) =
      (a : ℝ) * (b : ℝ) ^ omega K := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.succ_le_iff.mp hb
  have hbrpow : 0 < (b : ℝ) ^ omega K := Real.rpow_pos_of_pos hbpos _
  have hblock : (b : ℝ) ^ omega K ≤
      asymptoticRank (directSumCopies (matrixMul K b b b) a) := by
    rw [← asymptoticRank_matrixMul_square K b hb]
    exact asymptoticRank_mono (directSumCopies_restricts _ (Nat.succ_le_iff.mp ha))
  apply le_antisymm
  · simpa only [asymptoticRank_matrixMul_square K b hb] using
      asymptoticRank_directSumCopies_le (matrixMul K b b b) a
  rcases eq_or_lt_of_le ha with ha | ha
  · subst a
    simpa only [Nat.cast_one, one_mul] using hblock
  have hq : 1 < asymptoticRank (matrixMul K 2 2 2) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 4)
      (four_le_asymptoticRank_matrixMul_two K)
  have hr : ∀ n : ℕ, 1 ≤ rank (kroneckerPower (matrixMul K 2 2 2) n) := by
    intro n
    have h := flatteningRank_le_rank (kroneckerPower (matrixMul K 2 2 2) n) 0
    rw [flatteningRank_kroneckerPower] at h
    norm_num only [flatteningRank_matrixMul_zero, Nat.reduceMul] at h
    exact (Nat.one_le_pow n 4 (by decide)).trans h
  have hp : 1 ≤ asymptoticRank (directSumCopies (matrixMul K b b b) a) /
      (b : ℝ) ^ omega K := (one_le_div hbrpow).mpr hblock
  have hcapacity : ∀ n m : ℕ,
      rank (kroneckerPower (matrixMul K 2 2 2) n) ≤ a ^ m →
      asymptoticRank (matrixMul K 2 2 2) ^ n ≤
        (asymptoticRank (directSumCopies (matrixMul K b b b) a) /
          (b : ℝ) ^ omega K) ^ m := by
    intro n m hnm
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos hbrpow m)).mpr
      (matrixMul_capacity_inequality K a b n m hb hnm)
  have h := le_of_root_limit_capacity ha hq hp hr
    (asymptoticRank_eq_limit (matrixMul K 2 2 2)) hcapacity
  exact (le_div_iff₀ hbrpow).mp h

end MatrixMultiplication.Tensor
