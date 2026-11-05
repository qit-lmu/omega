module

public import Omega.ExponentBounds
public import Omega.ExponentSize
import Mathlib.Tactic.Ring

/-!
# The exponent as an infimum of ordinary tensor-rank bounds

The manuscript defines `omega` through asymptotic rank at matrix size two.
This file identifies it with the infimum of the ordinary rank logarithmic
bounds over all square matrix sizes. The two excluded sizes use the elementary
upper bound three. The comparison does not use the main nine-quarters theorem.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped Topology

/-- Every ordinary rank bound at a matrix size at least two bounds the exponent. -/
theorem omega_le_log_rank_matrixMul (K : Type*) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    omega K ≤ Real.log (Tensor.rank (Tensor.matrixMul K n n n) : ℝ) /
      Real.log (n : ℝ) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h := Tensor.asymptoticRank_le_rank (Tensor.matrixMul K n n n)
  rw [Tensor.asymptoticRank_matrixMul_square K n (by omega)] at h
  have hlog := Real.logb_le_logb_of_le hn'
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n) (omega K)) h
  rw [Real.logb_rpow (by positivity : (0 : ℝ) < n) (ne_of_gt hn')] at hlog
  exact hlog

/-- Ordinary matrix rank logarithms along powers of two converge to the exponent. -/
theorem log_rank_matrixMul_pow_two_tendsto (K : Type*) [Field K] :
    Tendsto (fun n : ℕ =>
      Real.log (Tensor.rank (Tensor.matrixMul K (2 ^ n) (2 ^ n) (2 ^ n)) : ℝ) /
        Real.log ((2 ^ n : ℕ) : ℝ)) atTop (𝓝 (omega K)) := by
  have hpos : ∀ n : ℕ,
      0 < (Tensor.rank (Tensor.kroneckerPower (Tensor.matrixMul K 2 2 2) n) : ℝ) := by
    intro n
    rw [← Tensor.rank_matrixMul_pow]
    have hn : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by omega) n)
    have h := Tensor.asymptoticRank_le_rank (Tensor.matrixMul K (2 ^ n) (2 ^ n) (2 ^ n))
    rw [Tensor.asymptoticRank_matrixMul_square K (2 ^ n) hn] at h
    exact (Real.rpow_pos_of_pos (by positivity) (omega K)).trans_le h
  have hlim := (Real.continuousAt_logb
    (b := (2 : ℝ))
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
      (four_le_asymptoticRank_matrixMul_two K)))).tendsto.comp
        (Tensor.asymptoticRank_eq_limit (Tensor.matrixMul K 2 2 2))
  change Tendsto _ atTop (𝓝 (omega K)) at hlim
  convert hlim using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [Tensor.rank_matrixMul_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (hpos n), Real.logb]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The infimum definition using ordinary square-matrix ranks agrees with the
manuscript's asymptotic-rank definition, over every field. -/
theorem iInf_log_rank_matrixMul_eq_omega (K : Type*) [Field K] :
    (⨅ n : ℕ, if 2 ≤ n then
      Real.log (Tensor.rank (Tensor.matrixMul K n n n) : ℝ) / Real.log (n : ℝ)
      else 3) = omega K := by
  let f : ℕ → ℝ := fun n => if 2 ≤ n then
    Real.log (Tensor.rank (Tensor.matrixMul K n n n) : ℝ) / Real.log (n : ℝ)
    else 3
  have hlower : ∀ n, omega K ≤ f n := by
    intro n
    dsimp [f]
    split_ifs with hn
    · exact omega_le_log_rank_matrixMul K n hn
    · exact omega_le_three K
  have hbounded : BddBelow (Set.range f) := ⟨omega K, by
    rintro _ ⟨n, rfl⟩
    exact hlower n⟩
  change (⨅ n, f n) = omega K
  apply le_antisymm
  · apply ge_of_tendsto (log_rank_matrixMul_pow_two_tendsto K)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have htwo : 2 ≤ 2 ^ n := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    simpa only [f, ite_eq_left htwo] using ciInf_le hbounded (2 ^ n)
  · exact le_ciInf hlower

end MatrixMultiplication
