module

public import Omega.ValuePolynomial
public import Omega.Analysis.GammaGrowth

/-!
# The sharper Gamma bound for polynomial multiplication

This file instantiates the quantitative part of Lemma 6.1. It is separate
from the elementary growth argument used by the main exponent theorem.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- The Gamma-function lower bound of Lemma 6.1, over every field. -/
theorem polynomialMul_value_gamma_lower_bound (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (a : ℕ) (ha : 1 ≤ a) :
    (3 * (a : ℝ) - 1) / (2 * Real.Gamma (4 / 3)) *
        (Real.Gamma ((a : ℝ) + 1 / 3) / Real.Gamma a) ≤
      polynomialMulValue K τ a a :=
  (polynomialMul_value_growthHypotheses K hτ hτω).diagonal_gamma_lower_bound ha

/-- Both inequalities of `eq:lem4/3`, with the exact Gamma expression between
the normalized value and the elementary power bound. -/
theorem polynomialMul_value_gamma_bounds (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (a : ℕ) (ha : 1 ≤ a) :
    gammaGrowthBound a ≤ polynomialMulValue K τ a a ∧
      (a : ℝ) ^ (4 / 3 : ℝ) ≤ gammaGrowthBound a :=
  ⟨polynomialMul_value_gamma_lower_bound K hτ hτω a ha, rpow_le_gammaGrowthBound ha⟩

/-- The finite-product lower bound in `eq:PM-Gamma`. -/
theorem polynomialMul_value_prod_lower_bound (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (a : ℕ) (ha : 1 ≤ a) :
    (3 * (a : ℝ) - 1) / 2 *
        (∏ i ∈ Finset.Ico 1 a, (3 * (i : ℝ) + 1) / (3 * i)) ≤
      polynomialMulValue K τ a a := by
  rw [← gammaGrowthBound_eq_prod a ha]
  exact polynomialMul_value_gamma_lower_bound K hτ hτω a ha

end MatrixMultiplication.Tensor
