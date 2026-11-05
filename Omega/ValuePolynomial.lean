module

public import Omega.ValuePartialSum
public import Omega.ValueNormalization
public import Omega.Tensor.PolynomialDegeneration
public import Omega.Tensor.PolynomialTripling
public import Omega.Tensor.PolynomialConcavity
public import Omega.ValuePolynomialSupport
public import Omega.Analysis.Growth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Growth inequalities for the value of polynomial multiplication

The normalized value of polynomial multiplication supplies the function in
the numerical growth argument. Its concavity and tripling inequalities follow
from the corresponding tensor degenerations and partial-sum superadditivity.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

/-- The normalized polynomial-multiplication value used in Section 6. -/
noncomputable def polynomialMulValue (K : Type*) [Field K] (τ : ℝ) (a b : ℕ) : ℝ :=
  (fractionalValue (polynomialMul K a b) τ).toReal ^ τ⁻¹

theorem polynomialMulValue_nonneg (K : Type*) [Field K] (τ : ℝ) (a b : ℕ) :
    0 ≤ polynomialMulValue K τ a b := Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- The diagonal degeneration gives the upper bound needed for the final
exponent comparison, without an exact rank formula. -/
theorem polynomialMulValue_rpow_le (K : Type*) [Field K] (a b : ℕ)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    polynomialMulValue K τ a b ^ τ ≤ ((a + b - 1 : ℕ) : ℝ) := by
  have hτpos : 0 < τ := by linarith
  rw [polynomialMulValue, Real.rpow_inv_rpow ENNReal.toReal_nonneg hτpos.ne']
  have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (fractionalValue_le_asymptoticRank (polynomialMul K a b) hτ hτω)
  rw [ENNReal.toReal_ofReal (asymptoticRank_nonneg _)] at hv
  have hd := asymptoticRank_mono_degeneration (diagonal_degenerates_polynomialMul K a b)
  rw [asymptoticRank_diagonal] at hd
  exact hv.trans hd

/-- On the diagonal the uniform upper bound has the linear form used by the
numerical exponent theorem. -/
theorem polynomialMulValue_diagonal_rpow_le (K : Type*) [Field K] (a : ℕ) (ha : 1 ≤ a)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    polynomialMulValue K τ a a ^ τ ≤ 2 * (a : ℝ) - 1 := by
  have h := polynomialMulValue_rpow_le K a a hτ hτω
  have hc : ((a + a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a + a), Nat.cast_add, Nat.cast_one]
    ring
  rwa [hc] at h

private theorem fractionalValue_root_mono
    {K I J L I' J' L' : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'} (h : Degenerates T S)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (fractionalValue S τ).toReal ^ τ⁻¹ ≤ (fractionalValue T τ).toReal ^ τ⁻¹ := by
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (fractionalValue_ne_top T hτ hτω) (fractionalValue_mono h τ))
  exact inv_nonneg.mpr (by linarith)

/-- Symmetry in the two polynomial input sizes. -/
theorem polynomialMulValue_symmetry (K : Type*) [Field K] (τ : ℝ) (a b : ℕ) :
    polynomialMulValue K τ a b = polynomialMulValue K τ b a := by
  simp only [polynomialMulValue, polynomialMul_value_swap K a b τ]

/-- Multiplication by a scalar gives the boundary normalization. -/
theorem polynomialMulValue_boundary (K : Type*) [Field K] (b : ℕ) (hb : 1 ≤ b)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    polynomialMulValue K τ 1 b = b := by
  have hτpos : 0 < τ := by linarith
  rw [polynomialMulValue,
    fractionalValue_eq_of_equivalent (polynomialMul_one_equivalent_matrixMul (R := K) b) τ,
    fractionalValue_matrixMul 1 1 b le_rfl le_rfl hb hτ hτω]
  simp only [one_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    Real.rpow_rpow_inv (Nat.cast_nonneg b) hτpos.ne']

/-- The concavity degeneration implies the normalized-value inequality. -/
theorem polynomialMul_value_concavity_of_degeneration
    (K : Type*) [Field K] (a b p : ℕ) (hp : 1 ≤ p)
    (hdeg : Degenerates (polynomialMulCopies K a b (p + 1))
      (partialSum (polynomialMulCopies K a (b - 1) p) (polynomialMul K a (b + p))))
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (p : ℝ) * polynomialMulValue K τ a (b - 1) + polynomialMulValue K τ a (b + p) ≤
      ((p : ℝ) + 1) * polynomialMulValue K τ a b := by
  have h := (fractionalValue_partialSum_toReal_add_le
    (polynomialMulCopies K a (b - 1) p) (polynomialMul K a (b + p)) hτ hτω).trans
    (fractionalValue_root_mono hdeg hτ hτω)
  rw [polynomialMulCopies_value_root K a (b - 1) p hp hτ hτω,
    polynomialMulCopies_value_root K a b (p + 1) (by omega) hτ hτω] at h
  simpa only [Nat.cast_add, Nat.cast_one, polynomialMulValue] using h

/-- Concavity of normalized polynomial value. The zero multiplicity case is
equality; the endpoint `b=1` is also included. -/
theorem polynomialMul_value_concavity (K : Type*) [Field K] (a b p : ℕ) (hb : 1 ≤ b)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (p : ℝ) * polynomialMulValue K τ a (b - 1) + polynomialMulValue K τ a (b + p) ≤
      ((p : ℝ) + 1) * polynomialMulValue K τ a b := by
  by_cases hp : p = 0
  · simp [hp]
  · exact polynomialMul_value_concavity_of_degeneration K a b p
      (Nat.one_le_iff_ne_zero.mpr hp) (polynomialMul_concavity_degeneration K a b p hb)
      hτ hτω

/-- The three-block degeneration bounds the sum of the three normalized values. -/
theorem polynomialMul_value_threeBlock (K : Type*) [Field K] (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    polynomialMulValue K τ a b + polynomialMulValue K τ a c + polynomialMulValue K τ a d ≤
      polynomialMulValue K τ a (a + b + c + d - 1) := by
  have h₁ := fractionalValue_partialSum_toReal_add_le (polynomialMul K a b)
    (swapLastTwo (polynomialMul K a c)) hτ hτω
  have h₂ := fractionalValue_partialSum_toReal_add_le
    (partialSum (polynomialMul K a b) (swapLastTwo (polynomialMul K a c)))
    (polynomialMul K a d) hτ hτω
  have h := ((add_le_add h₁ (le_refl ((fractionalValue (polynomialMul K a d) τ).toReal ^ τ⁻¹))).trans h₂).trans
    (fractionalValue_root_mono
      (polynomialMul_threeBlock_degeneration K a b c d ha hb hc hd) hτ hτω)
  simpa only [fractionalValue_swapLastTwo, polynomialMulValue] using h

/-- The tripling inequality on the diagonal, as used in Section 6. -/
theorem polynomialMul_value_tripling (K : Type*) [Field K] (a : ℕ) (ha : 1 ≤ a)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    3 * polynomialMulValue K τ a a ≤ polynomialMulValue K τ a (4 * a - 1) := by
  have h := polynomialMul_value_threeBlock K a a a a ha ha ha ha hτ hτω
  have hsize : a + a + a + a - 1 = 4 * a - 1 := by omega
  rw [hsize] at h
  linarith

/-- The tensor value supplies all numerical growth hypotheses once the
concavity degeneration is available. The zero multiplicity case is equality. -/
theorem polynomialMul_value_growthHypotheses_of_concavity
    (K : Type*) [Field K]
    (hconc : ∀ a b p : ℕ, 1 ≤ a → 2 ≤ b → 1 ≤ p →
      Degenerates (polynomialMulCopies K a b (p + 1))
        (partialSum (polynomialMulCopies K a (b - 1) p) (polynomialMul K a (b + p))))
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    GrowthHypotheses (polynomialMulValue K τ) where
  symmetry a b _ _ := polynomialMulValue_symmetry K τ a b
  boundary a ha := polynomialMulValue_boundary K a ha hτ hτω
  concavity a b p ha hb := by
    by_cases hp : p = 0
    · simp [hp]
    · have hp' : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
      have h := polynomialMul_value_concavity_of_degeneration K a (b + 1) p hp'
        (hconc a (b + 1) p ha (by omega) hp') hτ hτω
      simpa only [Nat.add_sub_cancel, Nat.add_right_comm b 1 p] using h
  tripling a ha := polynomialMul_value_tripling K a ha hτ hτω

/-- Fractional value of polynomial multiplication supplies the numerical
growth hypotheses over every field. -/
theorem polynomialMul_value_growthHypotheses (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    GrowthHypotheses (polynomialMulValue K τ) :=
  polynomialMul_value_growthHypotheses_of_concavity K
    (fun a b p _ hb _ => polynomialMul_concavity_degeneration K a b p (by omega)) hτ hτω

/-- The checked diagonal recurrence for polynomial-multiplication value. -/
theorem polynomialMul_value_diagonal_recurrence (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (a : ℕ) (ha : 1 ≤ a) :
    growthRatio a * polynomialMulValue K τ a a ≤ polynomialMulValue K τ (a + 1) (a + 1) :=
  (polynomialMul_value_growthHypotheses K hτ hτω).diagonal_recurrence ha

/-- The elementary diagonal lower bound used by the main exponent proof. -/
theorem polynomialMul_value_elementary_lower_bound (K : Type*) [Field K]
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (a : ℕ) (ha : 1 ≤ a) :
    (a : ℝ) ^ (4 / 3 : ℝ) ≤ polynomialMulValue K τ a a :=
  (polynomialMul_value_growthHypotheses K hτ hτω).diagonal_rpow_lower_bound ha

end MatrixMultiplication.Tensor
