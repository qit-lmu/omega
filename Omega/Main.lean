module

public import Omega.ValuePolynomial
import Mathlib.Tactic.Linarith

/-!
# The matrix-multiplication exponent over every field

The polynomial-multiplication value satisfies the checked growth hypotheses.
At `τ = omega K / 3`, its elementary lower bound and the uniform diagonal
degeneration upper bound imply the manuscript's main theorem.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The matrix-multiplication exponent is at most nine quarters over every field. -/
theorem omega_le_nine_quarters (K : Type*) [Field K] : omega K ≤ (9 : ℝ) / 4 := by
  have htwo := two_le_omega K
  have hτ : (2 : ℝ) / 3 ≤ omega K / 3 := by linarith
  exact exponent_le_nine_quarters_of_growth
    (Tensor.polynomialMul_value_growthHypotheses K hτ le_rfl)
    (by linarith : 0 < omega K)
    (fun a ha => Tensor.polynomialMulValue_diagonal_rpow_le K a ha hτ le_rfl)

end MatrixMultiplication
