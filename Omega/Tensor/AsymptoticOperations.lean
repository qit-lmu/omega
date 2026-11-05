module

public import Omega.Tensor.PowerReindex
public import Omega.Tensor.Asymptotic
import Mathlib.Tactic.Positivity

/-!
# Tensor powers and products of asymptotic ranks

The root-limit characterization makes asymptotic rank exactly multiplicative
under powers, and submultiplicative under Kronecker products.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

open Filter
open scoped Topology

variable {R : Type*} {I J L I' J' L' : Type*}

/-- The empty tensor power has asymptotic rank one over a nontrivial semiring. -/
@[simp]
theorem asymptoticRank_kroneckerPower_zero [CommSemiring R] [Nontrivial R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank (kroneckerPower T 0) = 1 := by
  have h := asymptoticRank_eq_limit (kroneckerPower T 0)
  simp only [rank_kroneckerPower_kroneckerPower, Nat.mul_zero,
    rank_kroneckerPower_zero, Nat.cast_one, Real.one_rpow] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Asymptotic rank is exactly multiplicative under every tensor power. -/
theorem asymptoticRank_pow [CommSemiring R] [Nontrivial R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (k : ℕ) :
    asymptoticRank (kroneckerPower T k) = asymptoticRank T ^ k := by
  by_cases hk : k = 0
  · subst k
    simpa only [pow_zero] using asymptoticRank_kroneckerPower_zero T
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hkreal : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hsub : Tendsto (fun n : ℕ => n * k) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro n
    exact Nat.le_mul_of_pos_right n hkpos
  have h := ((asymptoticRank_eq_limit T).comp hsub).pow k
  have he : (fun n : ℕ => ((rank (kroneckerPower T (n * k)) : ℝ) ^
      ((n * k : ℕ) : ℝ)⁻¹) ^ k) =
      (fun n : ℕ => (rank (kroneckerPower (kroneckerPower T k) n) : ℝ) ^
        (n : ℝ)⁻¹) := by
    funext n
    rw [rank_kroneckerPower_kroneckerPower,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_mul, mul_inv_rev, mul_right_comm, inv_mul_cancel₀ hkreal, one_mul]
  change Tendsto (fun n : ℕ => ((rank (kroneckerPower T (n * k)) : ℝ) ^
    ((n * k : ℕ) : ℝ)⁻¹) ^ k) atTop (𝓝 (asymptoticRank T ^ k)) at h
  rw [he] at h
  exact tendsto_nhds_unique (asymptoticRank_eq_limit (kroneckerPower T k)) h

/-- Asymptotic rank is submultiplicative under Kronecker products. -/
theorem asymptoticRank_kronecker_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    asymptoticRank (kronecker T S) ≤ asymptoticRank T * asymptoticRank S := by
  apply le_of_tendsto_of_tendsto (asymptoticRank_eq_limit (kronecker T S))
    ((asymptoticRank_eq_limit T).mul (asymptoticRank_eq_limit S))
  apply Filter.Eventually.of_forall
  intro n
  have h : (rank (kroneckerPower (kronecker T S) n) : ℝ) ≤
      (rank (kroneckerPower T n) : ℝ) * (rank (kroneckerPower S n) : ℝ) := by
    rw [rank_kroneckerPower_kronecker]
    exact_mod_cast rank_kronecker_le (kroneckerPower T n) (kroneckerPower S n)
  have hroot := Real.rpow_le_rpow (Nat.cast_nonneg _) h
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hroot

end MatrixMultiplication.Tensor
