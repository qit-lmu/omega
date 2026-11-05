module

public import Omega.Tensor.MatrixMultiplication
public import Omega.Tensor.AsymptoticOperations
public import Omega.Analysis.MonotonePowers

/-!
# Matrix size independence of the exponent

Rounded binary powers give the explicit restriction sandwich of
`eq:n-matmul-to-2`. The manuscript's `eq:omega-log-n` is then established in
its power formulation for every positive matrix size, including size one,
over every field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- Floor and ceiling binary logarithms bracket every positive integer power. -/
theorem pow_two_log_rounding (n m : ℕ) (hn : 1 ≤ n) :
    2 ^ ⌊(m : ℝ) * Real.logb 2 n⌋₊ ≤ n ^ m ∧
      n ^ m ≤ 2 ^ ⌈(m : ℝ) * Real.logb 2 n⌉₊ := by
  have hf : ⌊(m : ℝ) * Real.logb 2 n⌋₊ = Nat.log 2 (n ^ m) := by
    rw [← Real.natFloor_logb_natCast]
    simp only [Nat.cast_pow, Real.logb_pow, Nat.cast_ofNat]
  have hc : ⌈(m : ℝ) * Real.logb 2 n⌉₊ = Nat.clog 2 (n ^ m) := by
    rw [← Real.natCeil_logb_natCast]
    simp only [Nat.cast_pow, Real.logb_pow, Nat.cast_ofNat]
  rw [hf, hc]
  exact ⟨Nat.pow_log_le_self 2 (pow_ne_zero m (by omega)),
    Nat.le_pow_clog (by decide : 1 < 2) _⟩

/-- The full restriction and equivalence chain in `eq:n-matmul-to-2`.
The statement also allows scalar multiplication and the zeroth power. -/
theorem matrixMul_kroneckerPower_log_sandwich (R : Type*) [CommSemiring R]
    (n m : ℕ) (hn : 1 ≤ n) :
    Restricts (kroneckerPower (matrixMul R n n n) m)
        (kroneckerPower (matrixMul R 2 2 2) ⌊(m : ℝ) * Real.logb 2 n⌋₊) ∧
      Equivalent (kroneckerPower (matrixMul R n n n) m)
        (matrixMul R (n ^ m) (n ^ m) (n ^ m)) ∧
      Restricts (kroneckerPower (matrixMul R 2 2 2) ⌈(m : ℝ) * Real.logb 2 n⌉₊)
        (matrixMul R (n ^ m) (n ^ m) (n ^ m)) := by
  obtain ⟨hlo, hhi⟩ := pow_two_log_rounding n m hn
  have hnPower := matrixMul_kroneckerPower_equivalent R n n n m
  refine ⟨hnPower.1.trans ((matrixMul_restricts_of_le R hlo hlo hlo).trans
    (matrixMul_kroneckerPower_equivalent R 2 2 2 _).2), hnPower, ?_⟩
  exact (matrixMul_kroneckerPower_equivalent R 2 2 2 _).1.trans
    (matrixMul_restricts_of_le R hhi hhi hhi)

/-- The asymptotic rank of square matrix multiplication is `n ^ omega K`
for every positive size, including scalar multiplication. -/
theorem asymptoticRank_matrixMul_square (K : Type*) [Field K]
    (n : ℕ) (hn : 1 ≤ n) :
    asymptoticRank (matrixMul K n n n) = (n : ℝ) ^ omega K := by
  apply eq_rpow_logb_of_monotone_pow
    (fun a => asymptoticRank (matrixMul K a a a))
  · intro a b hab
    exact asymptoticRank_matrixMul_mono K hab hab hab
  · exact asymptoticRank_matrixMul_one K
  · intro a k
    rw [asymptoticRank_matrixMul_pow, asymptoticRank_pow]
  · exact hn

end MatrixMultiplication.Tensor
