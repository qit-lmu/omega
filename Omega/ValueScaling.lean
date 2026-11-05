module

public import Omega.ValueWitnessScaling
public import Omega.ValueScalingScore
public import Omega.ValueMonotonicity
public import Omega.Tensor.SymmetrizationMatrix
import Mathlib.Tactic.NormNum

/-!
# Exact scaling laws for fractional symmetrized value

A repeated square matrix-multiplication factor in the symmetrization can be
transferred to either side of every witness degeneration. Its score factor
therefore pulls through the extended-real supremum. This gives the diagonal
and matrix-multiplication scaling laws for every real value parameter.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

/-- Stripping a matrix block divides the score by its fixed scaling factor. -/
theorem ValueWitness.stripMatrixBlock_score_mul {T : Tensor K I J L}
    {S : Tensor K I' J' L'} {r q : ℕ} (w : ValueWitness S)
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul K q q q) r) (symmetrize T)))
    (hr : 1 ≤ r) (hq : 1 ≤ q) (τ : ℝ) :
    (w.stripMatrixBlock h hr hq).score τ *
      ((r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2)) = w.score τ :=
  ValueWitness.score_mul_of_denominator_scale w (w.stripMatrixBlock h hr hq)
    r q hr hq rfl rfl rfl rfl rfl τ

/-- Adding a matrix block multiplies the score by its fixed scaling factor. -/
theorem ValueWitness.addMatrixBlock_score {T : Tensor K I J L}
    {S : Tensor K I' J' L'} {r q : ℕ} (w : ValueWitness T)
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul K q q q) r) (symmetrize T)))
    (hr : 1 ≤ r) (hq : 1 ≤ q) (τ : ℝ) :
    (w.addMatrixBlock h hr hq).score τ =
      ((r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2)) * w.score τ :=
  ValueWitness.score_of_numerator_scale w (w.addMatrixBlock h hr hq)
    r q hr hq rfl rfl rfl rfl rfl τ

/-- A matrix-block factor in the symmetrization scales fractional value by
the sixth root of its multiplicity and the appropriate matrix-size power. -/
theorem fractionalValue_eq_mul_of_symmetrize_matrixBlock
    {T : Tensor K I J L} {S : Tensor K I' J' L'} {r q : ℕ}
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul K q q q) r) (symmetrize T)))
    (hr : 1 ≤ r) (hq : 1 ≤ q) (τ : ℝ) :
    fractionalValue S τ =
      ENNReal.ofReal ((r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2)) * fractionalValue T τ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hr
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hq
  have hf : 0 < (r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2) :=
    mul_pos (Real.rpow_pos_of_pos hrpos _) (Real.rpow_pos_of_pos hqpos _)
  rw [fractionalValue_eq_iSup S, fractionalValue_eq_iSup T]
  apply le_antisymm
  · apply iSup_le
    intro w
    rw [← w.stripMatrixBlock_score_mul h hr hq τ,
      ENNReal.ofReal_mul ((w.stripMatrixBlock h hr hq).score_pos τ).le, mul_comm]
    exact mul_le_mul' le_rfl (le_iSup (fun v : ValueWitness T => ENNReal.ofReal (v.score τ))
      (w.stripMatrixBlock h hr hq))
  · rw [ENNReal.mul_iSup]
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_mul hf.le, ← w.addMatrixBlock_score h hr hq τ]
    exact le_iSup (fun v : ValueWitness S => ENNReal.ofReal (v.score τ))
      (w.addMatrixBlock h hr hq)

/-- A positive diagonal tensor scales fractional value by its size, for
every real parameter and including infinite values. -/
theorem fractionalValue_diagonal_kronecker_of_pos (T : Tensor K I J L)
    (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) :
    fractionalValue (kronecker (diagonal K r) T) τ = (r : ℝ≥0∞) * fractionalValue T τ := by
  have he := (symmetrize_kronecker_equivalent (diagonal K r) T).trans
    (((symmetrize_diagonal_equivalent r).trans
      (matrixMul_one_copies_equivalent_diagonal (R := K) (r ^ 6)).symm).kronecker
        (Equivalent.refl _))
  have h := fractionalValue_eq_mul_of_symmetrize_matrixBlock he (one_le_pow₀ hr) le_rfl τ
  have hf : ((r ^ 6 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (1 : ℝ) ^ (τ / 2) = r := by
    rw [Nat.cast_pow, Real.one_rpow, mul_one]
    simpa only [Nat.cast_ofNat, one_div] using
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg r) (by decide : (6 : ℕ) ≠ 0)
  rw [Nat.cast_one, hf, ENNReal.ofReal_natCast] at h
  exact h

/-- The diagonal scaling law also includes zero copies under the standard
extended-real convention `0 * ∞ = 0`. -/
theorem fractionalValue_diagonal_kronecker (T : Tensor K I J L) (r : ℕ) (τ : ℝ) :
    fractionalValue (kronecker (diagonal K r) T) τ = (r : ℝ≥0∞) * fractionalValue T τ := by
  by_cases hr : r = 0
  · subst r
    have hz : kronecker (diagonal K 0) T = 0 := by
      funext i j k
      exact Fin.elim0 i.1
    simp [hz]
  · exact fractionalValue_diagonal_kronecker_of_pos T r (Nat.one_le_iff_ne_zero.mpr hr) τ

/-- The value of an ordinary sum of identical copies is exactly its multiplicity
times the value of one copy. -/
theorem fractionalValue_directSumCopies (T : Tensor K I J L) (r : ℕ) (τ : ℝ) :
    fractionalValue (directSumCopies T r) τ = (r : ℝ≥0∞) * fractionalValue T τ :=
  fractionalValue_diagonal_kronecker T r τ

/-- A positive rectangular matrix-multiplication tensor scales fractional value
by `(l*m*n)^τ`, over every field and for every real parameter. -/
theorem fractionalValue_matrixMul_kronecker (T : Tensor K I J L)
    (l m n : ℕ) (hl : 1 ≤ l) (hm : 1 ≤ m) (hn : 1 ≤ n) (τ : ℝ) :
    fractionalValue (kronecker (matrixMul K l m n) T) τ =
      ENNReal.ofReal ((l * m * n : ℕ) : ℝ) ^ τ * fractionalValue T τ := by
  have hsize : 1 ≤ l * m * n :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hl hm) hn
  have he := (symmetrize_kronecker_equivalent (matrixMul K l m n) T).trans
    (((symmetrize_matrixMul K l m n).trans (directSumCopies_one_equivalent _).symm).kronecker
      (Equivalent.refl _))
  have h := fractionalValue_eq_mul_of_symmetrize_matrixBlock he le_rfl
    (one_le_pow₀ hsize) τ
  have hf : (1 : ℝ) ^ (1 / 6 : ℝ) * (((l * m * n) ^ 2 : ℕ) : ℝ) ^ (τ / 2) =
      ((l * m * n : ℕ) : ℝ) ^ τ := by
    rw [Real.one_rpow, one_mul, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [Nat.cast_one, hf] at h
  rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast Nat.succ_le_iff.mp hsize)] at h
  exact h

/-- The introduction's matrix-multiplication scaling identity, with the
matrix tensor on the right. It holds for every real parameter. -/
theorem fractionalValue_kronecker_matrixMul (T : Tensor K I J L)
    (l m n : ℕ) (hl : 1 ≤ l) (hm : 1 ≤ m) (hn : 1 ≤ n) (τ : ℝ) :
    fractionalValue (kronecker T (matrixMul K l m n)) τ =
      ENNReal.ofReal ((l * m * n : ℕ) : ℝ) ^ τ * fractionalValue T τ := by
  have he : Equivalent (kronecker T (matrixMul K l m n))
      (kronecker (matrixMul K l m n) T) := by
    apply equivalent_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
      (Equiv.prodComm _ _)
    funext i j k
    simp [reindex, kronecker, mul_comm]
  rw [fractionalValue_eq_of_equivalent he τ]
  exact fractionalValue_matrixMul_kronecker T l m n hl hm hn τ

end MatrixMultiplication.Tensor
