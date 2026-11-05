module

public import Omega.ValueNormalization
public import Omega.ValueMultiplicativity
public import Omega.ExponentSize

/-!
# Consequences of a finite value for the unit tensor

Finiteness of the unit value forces its normalization to one. Scaling,
monotonicity, and the positive-power law then bound all tensor values by
asymptotic rank, without assuming that the parameter is admissible. Applied
to matrix multiplication, this forces the upper admissible endpoint.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]

/-- A finite unit value is one, at any real parameter. -/
theorem fractionalValue_unit_eq_one_of_ne_top {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue (diagonal K 1) τ = 1 := by
  have hprod := fractionalValue_kronecker_ge (diagonal K 1) (diagonal K 1) τ
  rw [fractionalValue_eq_of_equivalent (kronecker_diagonal_one_equivalent _) τ] at hprod
  have hp := ENNReal.toReal_mono hU hprod
  rw [ENNReal.toReal_mul] at hp
  have hle := ENNReal.toReal_mono hU
    (one_le_fractionalValue (diagonal K 1) (diagonal_ne_zero (by decide)) τ)
  rw [ENNReal.toReal_one] at hle
  apply (ENNReal.toReal_eq_one_iff _).mp
  nlinarith [sq_nonneg ((fractionalValue (diagonal K 1) τ).toReal - 1)]

/-- Diagonal normalization follows from finiteness of the unit value. -/
theorem fractionalValue_diagonal_of_unit_ne_top (r : ℕ) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue (diagonal K r) τ = (r : ℝ≥0∞) := by
  have h := fractionalValue_diagonal_kronecker (diagonal K 1) r τ
  rw [fractionalValue_eq_of_equivalent (kronecker_diagonal_one_equivalent _) τ,
    fractionalValue_unit_eq_one_of_ne_top hU, mul_one] at h
  exact h

/-- Matrix-multiplication normalization follows from finiteness of the unit
value, with no separate lower or upper bound on the real parameter. -/
theorem fractionalValue_matrixMul_of_unit_ne_top (l m n : ℕ)
    (hl : 1 ≤ l) (hm : 1 ≤ m) (hn : 1 ≤ n) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue (matrixMul K l m n) τ = ((l * m * n : ℕ) : ℝ≥0∞) ^ τ := by
  have h := fractionalValue_matrixMul_kronecker (diagonal K 1) l m n hl hm hn τ
  rw [fractionalValue_eq_of_equivalent (kronecker_diagonal_one_equivalent _) τ,
    fractionalValue_unit_eq_one_of_ne_top hU, mul_one, ENNReal.ofReal_natCast] at h
  exact h

variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

/-- Rank bounds value whenever the unit value is finite. -/
theorem fractionalValue_le_rank_of_unit_ne_top (T : Tensor K I J L) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue T τ ≤ (rank T : ℝ≥0∞) := by
  have h := fractionalValue_mono (diagonal_restricts_of_rank T).degenerates τ
  rwa [fractionalValue_diagonal_of_unit_ne_top (rank T) hU] at h

/-- All tensor values are finite if the unit value is finite. -/
theorem fractionalValue_ne_top_of_unit_ne_top (T : Tensor K I J L) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue T τ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (fractionalValue_le_rank_of_unit_ne_top T hU)

/-- Each positive-power rank root bounds value if the unit value is finite. -/
theorem fractionalValue_toReal_le_rankRoot_of_unit_ne_top
    (T : Tensor K I J L) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) {n : ℕ} (hn : 1 ≤ n) :
    (fractionalValue T τ).toReal ≤
      (rank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ)) := by
  have hr := ENNReal.toReal_mono (by simp)
    (fractionalValue_le_rank_of_unit_ne_top (kroneckerPower T n) hU)
  rw [fractionalValue_pow_of_pos T n hn τ, ENNReal.toReal_pow,
    ENNReal.toReal_natCast] at hr
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hroot := Real.rpow_le_rpow (pow_nonneg ENNReal.toReal_nonneg n) hr
    (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg] at hroot
  simpa only [mul_one_div_cancel hn0, Real.rpow_one] using hroot

/-- Asymptotic rank bounds value if the unit value is finite. -/
theorem fractionalValue_le_asymptoticRank_of_unit_ne_top
    (T : Tensor K I J L) {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) :
    fractionalValue T τ ≤ ENNReal.ofReal (asymptoticRank T) := by
  apply (ENNReal.le_ofReal_iff_toReal_le
    (fractionalValue_ne_top_of_unit_ne_top T hU) (asymptoticRank_nonneg T)).mpr
  apply le_csInf (rankRootValues_nonempty T)
  rintro x ⟨n, hn, rfl⟩
  exact fractionalValue_toReal_le_rankRoot_of_unit_ne_top T hU hn

/-- Finiteness of the unit value forces the upper endpoint of the
admissible interval. -/
theorem le_omega_div_three_of_unit_ne_top {τ : ℝ}
    (hU : fractionalValue (diagonal K 1) τ ≠ ⊤) : τ ≤ omega K / 3 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (fractionalValue_le_asymptoticRank_of_unit_ne_top (matrixMul K 2 2 2) hU)
  rw [fractionalValue_matrixMul_of_unit_ne_top 2 2 2 (by omega) (by omega) (by omega) hU,
    ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (asymptoticRank_nonneg _),
    asymptoticRank_matrixMul_square K 2 (by omega)] at h
  have hpow : (8 : ℝ) ^ τ = (2 : ℝ) ^ (3 * τ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at h
  rw [hpow] at h
  have he := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h
  linarith

/-- The unit value is infinite above the upper admissible endpoint. -/
theorem fractionalValue_unit_eq_top_of_omega_div_three_lt {τ : ℝ}
    (hτ : omega K / 3 < τ) : fractionalValue (diagonal K 1) τ = ⊤ := by
  by_contra hU
  exact (not_le_of_gt hτ) (le_omega_div_three_of_unit_ne_top hU)

end MatrixMultiplication.Tensor
