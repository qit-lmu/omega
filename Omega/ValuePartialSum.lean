module

public import Omega.Tensor.PartialSum
public import Omega.Tensor.ProductFamily
public import Omega.Tensor.TypeSeparation
public import Omega.ValueScaling
public import Omega.Analysis.TypeBounds
public import Omega.Analysis.Entropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fractional value of partial direct sums

Type separation gives a uniform bound on each multinomial term. Summing over
all types proves superadditivity; weighted AM-GM then gives the entropy bound.
Both results hold for every field throughout the admissible value interval.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace MatrixMultiplication.Tensor

private theorem kronecker_comm_equivalent {K A B C D E F : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    (T : Tensor K A B C) (S : Tensor K D E F) :
    Equivalent (kronecker T S) (kronecker S T) := by
  apply equivalent_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (Equiv.prodComm _ _)
  funext i j k
  simp [reindex, kronecker, mul_comm]

variable {K H I : Type*} {J L : H → Type*} [Field K]
variable [Fintype H] [DecidableEq H] [Fintype I]
variable [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
variable (T : ∀ h, Tensor K I (J h) (L h))
variable (hsep : ∀ n : ℕ, 1 ≤ n → ∀ c : H → ℕ, (∑ h, c h) = n →
  Degenerates
    (directSumCopies (kroneckerPower (partialSumFamily T) n)
      (2 * Nat.multinomial Finset.univ c - 1))
    (kronecker
      (directSumCopies (tensorProductFamily (fun h => kroneckerPower (T h) (c h)))
        (Nat.multinomial Finset.univ c))
      (matrixMul K 1 1 (Nat.multinomial Finset.univ c))))

include hsep

/-- A type contributes at most twice the value of the full tensor power. -/
theorem fractionalValue_type_bound_of_type_separation
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (n : ℕ) (hn : 1 ≤ n) (c : H → ℕ) (hc : (∑ h, c h) = n) :
    (Nat.multinomial Finset.univ c : ℝ) ^ τ *
      ∏ h, (fractionalValue (T h) τ).toReal ^ c h ≤
        2 * (fractionalValue (partialSumFamily T) τ).toReal ^ n := by
  let Q := Nat.multinomial Finset.univ c
  let P := tensorProductFamily (fun h => kroneckerPower (T h) (c h))
  have hQ : 1 ≤ Q := Nat.multinomial_pos _ _
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hm := fractionalValue_mono (hsep n hn c hc) τ
  rw [fractionalValue_eq_of_equivalent (kronecker_comm_equivalent _ _) τ,
    fractionalValue_matrixMul_kronecker _ 1 1 Q le_rfl le_rfl hQ τ,
    fractionalValue_directSumCopies, fractionalValue_directSumCopies,
    fractionalValue_pow _ n hτ hτω] at hm
  simp only [one_mul, ENNReal.ofReal_natCast] at hm
  have hmr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (fractionalValue_ne_top _ hτ hτω))) hm
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    ENNReal.toReal_pow] at hmr
  have hp := fractionalValue_tensorProductFamily_ge
    (fun h => kroneckerPower (T h) (c h)) hτ hτω
  simp only [fractionalValue_pow _ _ hτ hτω] at hp
  have hpr := ENNReal.toReal_mono (fractionalValue_ne_top P hτ hτω) hp
  simp only [ENNReal.toReal_prod, ENNReal.toReal_pow] at hpr
  have hnat : ((2 * Q - 1 : ℕ) : ℝ) ≤ 2 * (Q : ℝ) := by
    exact_mod_cast Nat.sub_le (2 * Q) 1
  apply (mul_le_mul_iff_right₀ hQreal).mp
  calc
    (Q : ℝ) * ((Q : ℝ) ^ τ * ∏ h, (fractionalValue (T h) τ).toReal ^ c h)
      = (Q : ℝ) ^ τ * ((Q : ℝ) * ∏ h, (fractionalValue (T h) τ).toReal ^ c h) := by ring
    _ ≤ (Q : ℝ) ^ τ * ((Q : ℝ) * (fractionalValue P τ).toReal) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpr hQreal.le)
        (Real.rpow_nonneg hQreal.le _)
    _ ≤ ((2 * Q - 1 : ℕ) : ℝ) *
        (fractionalValue (partialSumFamily T) τ).toReal ^ n := hmr
    _ ≤ (2 * (Q : ℝ)) * (fractionalValue (partialSumFamily T) τ).toReal ^ n :=
      mul_le_mul_of_nonneg_right hnat (by positivity)
    _ = (Q : ℝ) * (2 * (fractionalValue (partialSumFamily T) τ).toReal ^ n) := by ring

/-- Real-valued superadditivity, obtained by summing over all finite types. -/
theorem fractionalValue_partialSum_toReal_superadditive_of_type_separation
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∑ h, (fractionalValue (T h) τ).toReal ^ τ⁻¹) ≤
      (fractionalValue (partialSumFamily T) τ).toReal ^ τ⁻¹ := by
  have hτpos : 0 < τ := by linarith
  apply sum_le_of_multinomial_bounds _ (fun _ => by positivity)
    (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) τ⁻¹)
  intro n hn c hc
  have h := Real.rpow_le_rpow (by positivity)
    (fractionalValue_type_bound_of_type_separation T hsep hτ hτω n hn c hc)
    (inv_nonneg.mpr hτpos.le)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_rpow_inv (Nat.cast_nonneg _) hτpos.ne',
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
    ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)] at h
  simpa only [← Real.rpow_pow_comm ENNReal.toReal_nonneg] using h

/-- Extended-real superadditivity in the admissible interval. -/
theorem fractionalValue_partialSum_superadditive_of_type_separation
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∑ h, fractionalValue (T h) τ ^ τ⁻¹) ≤
      fractionalValue (partialSumFamily T) τ ^ τ⁻¹ := by
  have hτpos : 0 < τ := by linarith
  have hf (h : H) : fractionalValue (T h) τ ^ τ⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hτpos.le)
      (fractionalValue_ne_top _ hτ hτω)
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun h _ => hf h))
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hτpos.le)
      (fractionalValue_ne_top _ hτ hτω))).mp
  rw [ENNReal.toReal_sum (fun h _ => hf h)]
  simp only [← ENNReal.toReal_rpow]
  exact fractionalValue_partialSum_toReal_superadditive_of_type_separation T hsep hτ hτω

/-- The entropy bound follows from superadditivity and weighted AM-GM. -/
theorem fractionalValue_partialSum_entropy_of_type_separation
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (q : H → ℝ) (hq : ∀ h, 0 ≤ q h) (hqsum : ∑ h, q h = 1) :
    (2 : ℝ≥0∞) ^ (τ * entropy q) * ∏ h, fractionalValue (T h) τ ^ q h ≤
      fractionalValue (partialSumFamily T) τ := by
  have hτpos : 0 < τ := by linarith
  have hreal := (entropy_variational_rpow_le
    (fun h => (fractionalValue (T h) τ).toReal) q
    (fun _ => ENNReal.toReal_nonneg) hq hqsum hτpos).trans
    (Real.rpow_le_rpow (by positivity)
      (fractionalValue_partialSum_toReal_superadditive_of_type_separation T hsep hτ hτω)
      hτpos.le)
  rw [Real.rpow_inv_rpow ENNReal.toReal_nonneg hτpos.ne'] at hreal
  apply (ENNReal.toReal_le_toReal ?_ (fractionalValue_ne_top _ hτ hτω)).mp
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_prod, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofNat] using hreal
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (by norm_num)
    · exact ENNReal.prod_ne_top (fun h _ =>
        ENNReal.rpow_ne_top_of_nonneg (hq h) (fractionalValue_ne_top _ hτ hτω))

omit hsep

/-- The real-valued root of fractional value is superadditive on finite
partial direct sums, including empty families and zero summands. -/
theorem fractionalValue_partialSum_toReal_superadditive
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∑ h, (fractionalValue (T h) τ).toReal ^ τ⁻¹) ≤
      (fractionalValue (partialSumFamily T) τ).toReal ^ τ⁻¹ :=
  fractionalValue_partialSum_toReal_superadditive_of_type_separation T
    (fun n _ c hc => partialSum_type_separation T n c hc) hτ hτω

/-- The partial-sum superadditivity inequality from the manuscript. -/
theorem fractionalValue_partialSum_superadditive
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∑ h, fractionalValue (T h) τ ^ τ⁻¹) ≤
      fractionalValue (partialSumFamily T) τ ^ τ⁻¹ :=
  fractionalValue_partialSum_superadditive_of_type_separation T
    (fun n _ c hc => partialSum_type_separation T n c hc) hτ hτω

/-- The partial-sum entropy inequality, for every real probability vector
and with zero probabilities and zero tensor values included. -/
theorem fractionalValue_partialSum_entropy
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3)
    (q : H → ℝ) (hq : ∀ h, 0 ≤ q h) (hqsum : ∑ h, q h = 1) :
    (2 : ℝ≥0∞) ^ (τ * entropy q) * ∏ h, fractionalValue (T h) τ ^ q h ≤
      fractionalValue (partialSumFamily T) τ :=
  fractionalValue_partialSum_entropy_of_type_separation T
    (fun n _ c hc => partialSum_type_separation T n c hc) hτ hτω q hq hqsum

universe u v

/-- The finite-family value inequality specialized to a binary partial sum. -/
theorem fractionalValue_partialSum_toReal_add_le
    {K : Type v} [Field K] {I J L J' L' : Type u}
    [Fintype I] [Fintype J] [Fintype L] [Fintype J'] [Fintype L']
    (T : Tensor K I J L) (S : Tensor K I J' L')
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (fractionalValue T τ).toReal ^ τ⁻¹ + (fractionalValue S τ).toReal ^ τ⁻¹ ≤
      (fractionalValue (partialSum T S) τ).toReal ^ τ⁻¹ := by
  let U : ∀ b : Bool, Tensor K I (bif b then J' else J) (bif b then L' else L)
    | false => T
    | true => S
  let : ∀ b : Bool, Fintype (bif b then J' else J)
    | false => inferInstanceAs (Fintype J)
    | true => inferInstanceAs (Fintype J')
  let : ∀ b : Bool, Fintype (bif b then L' else L)
    | false => inferInstanceAs (Fintype L)
    | true => inferInstanceAs (Fintype L')
  have he : Equivalent (partialSumFamily U) (partialSum T S) := by
    apply equivalent_of_reindex (Equiv.refl I) (Equiv.sumEquivSigmaBool J J').symm
      (Equiv.sumEquivSigmaBool L L').symm
    funext i j k
    cases j <;> cases k <;>
      simp [reindex, Equiv.sumEquivSigmaBool, partialSumFamily, partialSum, U]
  have hv := fractionalValue_partialSum_toReal_superadditive U hτ hτω
  rw [fractionalValue_eq_of_equivalent he τ] at hv
  simpa [U, add_comm] using hv

end MatrixMultiplication.Tensor
