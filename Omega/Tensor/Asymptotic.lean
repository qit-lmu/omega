module

public import Omega.Tensor.Powers
public import Omega.Analysis.RankGrowth

/-!
# Limits of tensor-rank roots

The manuscript defines asymptotic rank as an infimum. Submultiplicativity
identifies this with the limit of the normalized ranks of tensor powers.
Polynomial overhead in a comparison of power ranks therefore disappears.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

open Filter
open scoped Topology

variable {R : Type*} {I J L I' J' L' : Type*}

/-- The real-valued sequence of tensor-power ranks is submultiplicative. -/
theorem rankPowerSequence_submultiplicative [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Submultiplicative (fun n : ℕ => (rank (kroneckerPower T n) : ℝ)) := by
  intro m n
  change (rank (kroneckerPower T (m + n)) : ℝ) ≤
    (rank (kroneckerPower T m) : ℝ) * (rank (kroneckerPower T n) : ℝ)
  exact_mod_cast rank_kroneckerPower_add_le T m n

/-- The infimum in the manuscript is the infimum in mathlib's
submultiplicative-sequence limit theorem. -/
theorem asymptoticRank_eq_submultiplicative_limit [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank T = (rankPowerSequence_submultiplicative T).lim := by
  unfold asymptoticRank Submultiplicative.lim
  congr 1
  ext x
  simp only [rankRootValues, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Ici, one_div]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, hx.symm⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, hx.symm⟩

/-- The nth roots of tensor-power ranks converge to asymptotic rank. -/
theorem asymptoticRank_eq_limit [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Tendsto (fun n : ℕ => (rank (kroneckerPower T n) : ℝ) ^ (n : ℝ)⁻¹)
      atTop (𝓝 (asymptoticRank T)) := by
  rw [asymptoticRank_eq_submultiplicative_limit]
  exact (rankPowerSequence_submultiplicative T).tendsto_lim (fun n => Nat.cast_nonneg _)

/-- If every positive tensor-power rank of `S` is bounded by that of `T`
with only polynomial overhead, then `S` has no larger asymptotic rank.
This statement makes no cardinality or characteristic assumption. -/
theorem asymptoticRank_le_of_power_rank_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') (d k : ℕ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      rank (kroneckerPower S n) ≤ (d * n + 1) ^ k * rank (kroneckerPower T n)) :
    asymptoticRank S ≤ asymptoticRank T := by
  rw [asymptoticRank_eq_submultiplicative_limit, asymptoticRank_eq_submultiplicative_limit]
  apply MatrixMultiplication.submultiplicative_limit_le_of_polynomial_bound
    (rankPowerSequence_submultiplicative T) (rankPowerSequence_submultiplicative S)
    (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _) d k
  intro n hn
  exact_mod_cast hbound n hn

end MatrixMultiplication.Tensor
