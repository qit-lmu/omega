module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The numerical Strassen bound

The inequality `6^(w/3) ≤ 4` gives `w ≤ 3 log(4)/log(6)`. Rational
partial sums of the logarithm series certify the decimal upper bound in
Remark 4.11, independently of the main nine-quarters theorem.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The exact logarithmic conclusion of the Strassen tensor inequality. -/
theorem exponent_le_strassen_bound {w : ℝ} (h : (6 : ℝ) ^ (w / 3) ≤ 4) :
    w ≤ 3 * Real.log 4 / Real.log 6 := by
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) _) h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 6)] at hlog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 6))).2
  linarith

private theorem log_four_upper : Real.log 4 < (1386295 : ℝ) / 1000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (3 : ℝ) / 5) (by norm_num) (by norm_num) 15
  norm_num only [show (1 + (3 : ℝ) / 5) / (1 - 3 / 5) = 4 by norm_num] at h
  have hnum :
      2 * ((∑ i ∈ Finset.range 15, ((3 : ℝ) / 5) ^ (2 * i + 1) / (2 * i + 1)) +
        ((3 : ℝ) / 5) ^ (2 * 15 + 1) / (1 - ((3 : ℝ) / 5) ^ 2)) <
      (1386295 : ℝ) / 1000000 := by
    norm_num [Finset.sum_range_succ]
  linarith

private theorem log_six_lower : (1791759 : ℝ) / 1000000 < Real.log 6 := by
  have h := Real.sum_range_le_log_div
    (x := (5 : ℝ) / 7) (by norm_num) (by norm_num) 18
  norm_num only [show (1 + (5 : ℝ) / 7) / (1 - 5 / 7) = 6 by norm_num] at h
  have hnum : (1791759 : ℝ) / 1000000 <
      2 * (∑ i ∈ Finset.range 18, ((5 : ℝ) / 7) ^ (2 * i + 1) / (2 * i + 1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- A rigorous decimal enclosure for the upper bound in Remark 4.11. -/
theorem strassen_bound_lt_decimal :
    3 * Real.log 4 / Real.log 6 < (232112 : ℝ) / 100000 := by
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 6))).2
  nlinarith [log_four_upper, log_six_lower]

/-- The numerical consequence of the Strassen tensor inequality. -/
theorem exponent_lt_strassen_decimal {w : ℝ} (h : (6 : ℝ) ^ (w / 3) ≤ 4) :
    w < (232112 : ℝ) / 100000 :=
  (exponent_le_strassen_bound h).trans_lt strassen_bound_lt_decimal

end MatrixMultiplication
