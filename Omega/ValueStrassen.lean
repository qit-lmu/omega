module

public import Omega.Tensor.Strassen
public import Omega.Tensor.MatrixShapes
public import Omega.ValuePartialSum
public import Omega.ValueNormalization
public import Omega.ExponentBounds
public import Omega.Analysis.StrassenBound
import Mathlib.Tactic.Linarith

/-!
# The fractional-value bound from Strassen's tensor

The two scalar-multiplication blocks each have value `n^τ`. Binary
partial-sum superadditivity therefore gives `(2n)^τ`, while the exact
asymptotic rank gives the upper bound `n+1`. At `τ = omega K / 3` and
`n = 3`, this proves the comparison in manuscript Remark 4.11 directly.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]

/-- The left block in Strassen's tensor is scalar multiplication. -/
theorem fractionalValue_strassenLeft (n : ℕ) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (strassenLeft K n) τ = (n : ℝ≥0∞) ^ τ := by
  have he := matrixMul_n_one_one_equivalent K n
  change Equivalent (matrixMul K n 1 1) (strassenLeft K n) at he
  rw [← fractionalValue_eq_of_equivalent he τ,
    fractionalValue_matrixMul n 1 1 hn le_rfl le_rfl hτ hτω]
  simp

/-- The right block in Strassen's tensor is a dot product. -/
theorem fractionalValue_strassenRight (n : ℕ) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (strassenRight K n) τ = (n : ℝ≥0∞) ^ τ := by
  have he := matrixMul_one_n_one_equivalent K n
  change Equivalent (matrixMul K 1 n 1) (strassenRight K n) at he
  rw [← fractionalValue_eq_of_equivalent he τ,
    fractionalValue_matrixMul 1 n 1 le_rfl hn le_rfl hτ hτω]
  simp

/-- Partial-sum superadditivity gives the lower bound `(2n)^τ`. -/
theorem rpow_le_fractionalValue_strassenTensor (n : ℕ) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (2 * (n : ℝ)) ^ τ ≤ (fractionalValue (strassenTensor K n) τ).toReal := by
  have hτpos : 0 < τ := by linarith
  have h := fractionalValue_partialSum_toReal_add_le
    (strassenLeft K n) (strassenRight K n) hτ hτω
  rw [fractionalValue_strassenLeft n hn hτ hτω,
    fractionalValue_strassenRight n hn hτ hτω] at h
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    Real.rpow_rpow_inv (Nat.cast_nonneg n) hτpos.ne'] at h
  have hp := Real.rpow_le_rpow (by positivity) h hτpos.le
  rw [Real.rpow_inv_rpow ENNReal.toReal_nonneg hτpos.ne'] at hp
  simpa only [two_mul, strassenTensor] using hp

/-- Strassen's tensor gives `n+1 ≥ (2n)^τ` throughout the admissible interval. -/
theorem strassen_value_inequality (n : ℕ) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (2 * (n : ℝ)) ^ τ ≤ (n : ℝ) + 1 := by
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (fractionalValue_le_asymptoticRank (strassenTensor K n) hτ hτω)
  rw [ENNReal.toReal_ofReal (asymptoticRank_nonneg _),
    asymptoticRank_strassenTensor K n hn] at hu
  exact (rpow_le_fractionalValue_strassenTensor n hn hτ hτω).trans (by simpa using hu)

end MatrixMultiplication.Tensor

namespace MatrixMultiplication

/-- The endpoint parameter gives the exponent inequality from Strassen's tensor. -/
theorem strassen_exponent_inequality (K : Type*) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℝ)) ^ (omega K / 3) ≤ (n : ℝ) + 1 :=
  Tensor.strassen_value_inequality n hn (by linarith [two_le_omega K]) le_rfl

/-- Remark 4.11's exponent bound, obtained from the size-three Strassen tensor. -/
theorem omega_le_strassen_bound (K : Type*) [Field K] :
    omega K ≤ 3 * Real.log 4 / Real.log 6 := by
  apply exponent_le_strassen_bound
  convert strassen_exponent_inequality K 3 (by decide) using 1 <;> norm_num

/-- The numerical comparison is certified with exact rational logarithm bounds. -/
theorem omega_lt_strassen_decimal (K : Type*) [Field K] :
    omega K < (232112 : ℝ) / 100000 :=
  (omega_le_strassen_bound K).trans_lt strassen_bound_lt_decimal

end MatrixMultiplication
