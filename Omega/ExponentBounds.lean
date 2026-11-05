module

public import Omega.Tensor.MatrixMultiplication
import Mathlib.Tactic.NormNum

/-!
# Elementary bounds on the matrix-multiplication exponent

The first flattening of `⟨2,2,2⟩` has rank four over every field. Its lower
bound on asymptotic rank gives `2 ≤ omega K`. The elementary decomposition
into eight pure tensors gives `omega K ≤ 3`.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The asymptotic rank of two-by-two matrix multiplication is at least four. -/
theorem four_le_asymptoticRank_matrixMul_two (K : Type*) [Field K] :
    (4 : ℝ) ≤ Tensor.asymptoticRank (Tensor.matrixMul K 2 2 2) := by
  have h := Tensor.flatteningRank_le_asymptoticRank (Tensor.matrixMul K 2 2 2) 0
  simpa using h

/-- The matrix-multiplication exponent is at least two over every field. -/
theorem two_le_omega (K : Type*) [Field K] : (2 : ℝ) ≤ omega K := by
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 4) (four_le_asymptoticRank_matrixMul_two K)
  have hfour : Real.logb 2 4 = 2 := by
    calc
      Real.logb 2 4 = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
  simpa only [hfour, omega] using h

/-- The elementary algorithm bounds the matrix-multiplication exponent by three. -/
theorem omega_le_three (K : Type*) [Field K] : omega K ≤ (3 : ℝ) := by
  have hupper : Tensor.asymptoticRank (Tensor.matrixMul K 2 2 2) ≤ 8 := by
    have h := Tensor.asymptoticRank_le_rank (Tensor.matrixMul K 2 2 2)
    have hrank := Tensor.rank_matrixMul_le K 2 2 2
    norm_num at hrank
    exact h.trans (by exact_mod_cast hrank)
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
      (four_le_asymptoticRank_matrixMul_two K)) hupper
  have height : Real.logb 2 8 = 3 := by
    calc
      Real.logb 2 8 = Real.logb 2 ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
  simpa only [height, omega] using h

end MatrixMultiplication
