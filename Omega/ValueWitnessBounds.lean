module

public import Omega.FractionalValue
public import Omega.ValueWitnessUnit
public import Omega.AsymptoticSumInequality
public import Omega.Tensor.FlatteningDegeneration
public import Omega.Tensor.FlatteningCopies
public import Omega.Analysis.WitnessInterpolation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fractional-value witness bounds before supremum calculus

The upper endpoint follows from asymptotic rank and the equal-block sum
identity. The lower endpoint follows from flattening rank. Every intermediate
witness is controlled by these endpoints, before any supremum is taken.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]

/-- The asymptotic-rank endpoint bound for a single fractional-value witness. -/
theorem ValueWitness.bound_omega {T : Tensor K I J L} (w : ValueWitness T) :
    (w.a : ℝ) * (w.b : ℝ) ^ omega K ≤
      (w.c : ℝ) * (w.d : ℝ) ^ omega K * asymptoticRank T ^ (6 * w.N) := by
  calc
    _ = asymptoticRank (directSumCopies (matrixMul K w.b w.b w.b) w.a) :=
      (asymptoticRank_matrixMul_directPower K w.a w.b w.ha w.hb).symm
    _ ≤ asymptoticRank (kronecker (directSumCopies (matrixMul K w.d w.d w.d) w.c)
        (kroneckerPower (symmetrize T) w.N)) :=
      asymptoticRank_mono_degeneration w.degeneration
    _ ≤ asymptoticRank (directSumCopies (matrixMul K w.d w.d w.d) w.c) *
        asymptoticRank (kroneckerPower (symmetrize T) w.N) :=
      asymptoticRank_kronecker_le _ _
    _ = (w.c : ℝ) * (w.d : ℝ) ^ omega K * asymptoticRank (symmetrize T) ^ w.N := by
      rw [asymptoticRank_matrixMul_directPower K w.c w.d w.hc w.hd,
        asymptoticRank_pow]
    _ ≤ (w.c : ℝ) * (w.d : ℝ) ^ omega K * (asymptoticRank T ^ 6) ^ w.N := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (asymptoticRank_nonneg _) (asymptoticRank_symmetrize_le T) w.N)
      positivity
    _ = _ := by rw [pow_mul]

/-- The quadratic endpoint bound follows from the first flattening. -/
theorem ValueWitness.bound_two {T : Tensor K I J L} (w : ValueWitness T) :
    (w.a : ℝ) * (w.b : ℝ) ^ (2 : ℕ) ≤
      (w.c : ℝ) * (w.d : ℝ) ^ (2 : ℕ) * asymptoticRank T ^ (6 * w.N) := by
  have h := flatteningRank_mono_degeneration w.degeneration 0
  rw [flatteningRank_kronecker, flatteningRank_kroneckerPower,
    flatteningRank_directSumCopies_matrixMul_zero K w.a w.b w.hb,
    flatteningRank_directSumCopies_matrixMul_zero K w.c w.d w.hd] at h
  have hcast : (w.a : ℝ) * (w.b : ℝ) ^ (2 : ℕ) ≤
      (w.c : ℝ) * (w.d : ℝ) ^ (2 : ℕ) *
        (flatteningRank (symmetrize T) 0 : ℝ) ^ w.N := by exact_mod_cast h
  have hsym : (flatteningRank (symmetrize T) 0 : ℝ) ≤ asymptoticRank T ^ 6 :=
    (flatteningRank_le_asymptoticRank _ _).trans (asymptoticRank_symmetrize_le T)
  apply hcast.trans
  rw [pow_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hsym w.N) (by positivity)

/-- Every admissible fractional-value witness is bounded by asymptotic rank. -/
theorem valueWitness_le_asymptoticRank {T : Tensor K I J L}
    (w : ValueWitness T) {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    w.score τ ≤ asymptoticRank T := by
  apply witness_root_le_of_endpoint_bounds
    (by exact_mod_cast Nat.succ_le_iff.mp w.ha)
    (by exact_mod_cast Nat.succ_le_iff.mp w.hb)
    (by exact_mod_cast Nat.succ_le_iff.mp w.hc)
    (by exact_mod_cast Nat.succ_le_iff.mp w.hd)
    (Nat.mul_pos (by decide) (Nat.succ_le_iff.mp w.hN))
    (asymptoticRank_nonneg T) (by linarith) (by linarith)
    w.bound_two w.bound_omega

/-- Taking the extended-real supremum preserves the uniform witness bound. -/
theorem fractionalValue_le_asymptoticRank (T : Tensor K I J L)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue T τ ≤ ENNReal.ofReal (asymptoticRank T) := by
  apply iSup_le
  intro w
  exact ENNReal.ofReal_le_ofReal (valueWitness_le_asymptoticRank w hτ hτω)

/-- Fractional value is finite throughout the admissible interval. -/
theorem fractionalValue_ne_top (T : Tensor K I J L)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue T τ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (fractionalValue_le_asymptoticRank T hτ hτω)

/-- The unit diagonal has fractional value one throughout the admissible interval. -/
theorem fractionalValue_unit {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (diagonal K 1) τ = 1 := by
  apply le_antisymm
  · simpa only [asymptoticRank_diagonal, Nat.cast_one, ENNReal.ofReal_one] using
      fractionalValue_le_asymptoticRank (diagonal K 1) hτ hτω
  · exact one_le_fractionalValue _ (diagonal_ne_zero (by decide)) τ

end MatrixMultiplication.Tensor
