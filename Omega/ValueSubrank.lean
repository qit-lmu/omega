module

public import Omega.Tensor.Subrank
public import Omega.ValueNormalization
public import Omega.ValueMultiplicativity

/-!
# Fractional value between asymptotic subrank and asymptotic rank

This completes manuscript Corollary 4.9 (`lem:rank-value`). A maximal
diagonal restriction, monotonicity, and normalization bound subrank by value.
The exact power law then bounds every positive-power subrank root. Taking
their supremum proves the lower bound directly, without a convergence lemma.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

/-- Border subrank is bounded by fractional value on the admissible interval. -/
theorem borderSubrank_le_fractionalValue (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (borderSubrank T : ℝ≥0∞) ≤ fractionalValue T τ := by
  rw [← fractionalValue_diagonal (borderSubrank T) hτ hτω]
  exact fractionalValue_mono (degenerates_diagonal_of_borderSubrank T) τ

/-- Subrank is bounded by fractional value on the admissible interval. -/
theorem subrank_le_fractionalValue (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (subrank T : ℝ≥0∞) ≤ fractionalValue T τ := by
  rw [← fractionalValue_diagonal (subrank T) hτ hτω]
  exact fractionalValue_mono (restricts_diagonal_of_subrank T).degenerates τ

/-- Every positive-power subrank root is bounded by fractional value. -/
theorem subrankRoot_le_fractionalValue_toReal (T : Tensor K I J L)
    {n : ℕ} (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (subrank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ)) ≤
      (fractionalValue T τ).toReal := by
  have h := subrank_le_fractionalValue (kroneckerPower T n) hτ hτω
  have hr := (ENNReal.toReal_le_toReal (by simp)
    (fractionalValue_ne_top _ hτ hτω)).mpr h
  rw [fractionalValue_pow_of_pos T n hn τ, ENNReal.toReal_pow] at hr
  simp only [ENNReal.toReal_natCast] at hr
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  calc
    _ ≤ ((fractionalValue T τ).toReal ^ n) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hr (by positivity)
    _ = (fractionalValue T τ).toReal := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
      simp [hn0]

/-- The lower bound in manuscript Corollary 4.9, in real-valued form. -/
theorem asymptoticSubrank_le_fractionalValue_toReal (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    asymptoticSubrank T ≤ (fractionalValue T τ).toReal := by
  apply csSup_le (subrankRootValues_nonempty T)
  rintro x ⟨n, hn, rfl⟩
  exact subrankRoot_le_fractionalValue_toReal T hn hτ hτω

/-- The lower bound in manuscript Corollary 4.9, with the value's native codomain. -/
theorem asymptoticSubrank_le_fractionalValue (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    ENNReal.ofReal (asymptoticSubrank T) ≤ fractionalValue T τ := by
  exact (ENNReal.ofReal_le_iff_le_toReal (fractionalValue_ne_top T hτ hτω)).mpr
    (asymptoticSubrank_le_fractionalValue_toReal T hτ hτω)

/-- The full subrank/value/rank sandwich in manuscript Corollary 4.9. -/
theorem fractionalValue_rank_sandwich (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    ENNReal.ofReal (asymptoticSubrank T) ≤ fractionalValue T τ ∧
      fractionalValue T τ ≤ ENNReal.ofReal (asymptoticRank T) :=
  ⟨asymptoticSubrank_le_fractionalValue T hτ hτω,
    fractionalValue_le_asymptoticRank T hτ hτω⟩

/-- The same sandwich as inequalities of finite real numbers. -/
theorem fractionalValue_toReal_rank_sandwich (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    asymptoticSubrank T ≤ (fractionalValue T τ).toReal ∧
      (fractionalValue T τ).toReal ≤ asymptoticRank T := by
  refine ⟨asymptoticSubrank_le_fractionalValue_toReal T hτ hτω, ?_⟩
  exact (ENNReal.le_ofReal_iff_toReal_le (fractionalValue_ne_top T hτ hτω)
    (asymptoticRank_nonneg T)).mp (fractionalValue_le_asymptoticRank T hτ hτω)

end MatrixMultiplication.Tensor
