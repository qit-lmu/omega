module

public import Omega.ValueFiniteUnit
public import Omega.Tensor.MatrixSubrank
public import Omega.Analysis.Growth

/-!
# Infinite value outside the admissible interval

This file proves Lemma 4.5. Finiteness forces unit normalization, and
comparison with rank and with a quadratic diagonal degeneration gives the
two necessary bounds on the value parameter.
-/

@[expose] public section

namespace MatrixMultiplication

/-- A quadratic power cannot be bounded on all positive integers by a
smaller power of twice the argument. -/
theorem two_le_of_nat_sq_le_double_rpow {r : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 2 ≤ (2 * (n : ℝ)) ^ r) : 2 ≤ r := by
  by_contra hr
  have hrp : 0 < 2 - r := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ) ^ (r / (2 - r)))
  have hn0 : (0 : ℝ) < n :=
    lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    hn hrp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    div_mul_cancel₀ _ hrp.ne'] at hp
  have hb := h n hn1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le] at hb
  have he : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 - r) * (n : ℝ) ^ r := by
    rw [← Real.rpow_add hn0, sub_add_cancel, Real.rpow_two]
  rw [he] at hb
  exact (not_lt_of_ge hb) (mul_lt_mul_of_pos_right hp (Real.rpow_pos_of_pos hn0 _))

namespace Tensor

open scoped ENNReal

variable {K : Type*} [Field K]

/-- The explicit quadratic degeneration forces the lower endpoint whenever
the unit value is finite. The sharper Strassen border-subrank bound is not
needed for this conclusion. -/
theorem two_thirds_le_of_unit_ne_top {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) : (2 : ℝ) / 3 ≤ τ := by
  have hp : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ^ 2 ≤ (2 * (q : ℝ)) ^ (3 * τ) := by
    intro q hq
    have h := ENNReal.toReal_mono
      (fractionalValue_ne_top_of_unit_ne_top (matrixMul K (2*q) (2*q) (2*q)) hU)
      (fractionalValue_mono (matrixMul_degenerates_diagonal_quadratic K q) τ)
    rw [fractionalValue_diagonal_of_unit_ne_top (q ^ 2) hU,
      fractionalValue_matrixMul_of_unit_ne_top (2*q) (2*q) (2*q)
        (by omega) (by omega) (by omega) hU,
      ← ENNReal.toReal_rpow, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h
    push_cast at h
    have he : (2 * (q : ℝ) * (2 * q) * (2 * q)) ^ τ =
        (2 * (q : ℝ)) ^ (3 * τ) := by
      rw [show 2 * (q : ℝ) * (2 * q) * (2 * q) = (2 * q) ^ (3 : ℕ) by ring,
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * q)]
      norm_num
    rwa [he] at h
  have h := two_le_of_nat_sq_le_double_rpow hp
  linarith

/-- The unit value is infinite below the lower admissible endpoint. -/
theorem fractionalValue_unit_eq_top_of_lt_two_thirds {τ : ℝ}
    (hτ : τ < (2 : ℝ) / 3) : fractionalValue (diagonal K 1) τ = ⊤ := by
  by_contra hU
  exact (not_le_of_gt hτ) (two_thirds_le_of_unit_ne_top hU)

variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

/-- Finiteness of any nonzero tensor value forces both admissible endpoints. -/
theorem fractionalValue_parameter_bounds_of_ne_top (T : Tensor K I J L) (hT : T ≠ 0)
    {τ : ℝ} (hfinite : fractionalValue T τ ≠ ⊤) :
    (2 : ℝ) / 3 ≤ τ ∧ τ ≤ omega K / 3 := by
  have hU : fractionalValue (diagonal K 1) τ ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (fractionalValue_mono (restricts_diagonal_one_of_ne_zero T hT).degenerates τ)
  exact ⟨two_thirds_le_of_unit_ne_top hU, le_omega_div_three_of_unit_ne_top hU⟩

/-- Lemma 4.5: every nonzero tensor has infinite value at a positive
parameter outside the admissible interval. -/
theorem fractionalValue_eq_top_of_outside_range (T : Tensor K I J L) (hT : T ≠ 0)
    {τ : ℝ} (_hτ : 0 < τ) (hout : τ ∉ Set.Icc ((2 : ℝ) / 3) (omega K / 3)) :
    fractionalValue T τ = ⊤ := by
  by_contra hfinite
  exact hout (fractionalValue_parameter_bounds_of_ne_top T hT hfinite)

/-- Finiteness is equivalent to membership in the admissible interval.
The library's formula is defined for every real parameter, so this stronger
statement also covers nonpositive parameters. -/
theorem fractionalValue_ne_top_iff (T : Tensor K I J L) (hT : T ≠ 0) (τ : ℝ) :
    fractionalValue T τ ≠ ⊤ ↔ τ ∈ Set.Icc ((2 : ℝ) / 3) (omega K / 3) := by
  constructor
  · exact fractionalValue_parameter_bounds_of_ne_top T hT
  · rintro ⟨hτ, hτω⟩
    exact fractionalValue_ne_top T hτ hτω

end Tensor

end MatrixMultiplication
