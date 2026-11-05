module

public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entropy and the variational sum identity

Entropy uses base-two logarithms. The real logarithm's value at zero gives
the convention `0 * log 0 = 0`; real powers give `0 ^ 0 = 1`. Weighted AM-GM
therefore applies without discarding zero weights or zero coordinates.
-/

@[expose] public section

namespace MatrixMultiplication

open scoped BigOperators

/-- Base-two entropy of a finite real weight vector. The probability
conditions are hypotheses of the theorems using this definition. -/
noncomputable def entropy {H : Type*} [Fintype H] (q : H → ℝ) : ℝ :=
  -(∑ h, q h * Real.log (q h)) / Real.log 2

/-- The exponential of entropy is a product, including zero probabilities. -/
theorem two_rpow_entropy_eq_prod {H : Type*} [Fintype H]
    (q : H → ℝ) (hq : ∀ h, 0 ≤ q h) :
    (2 : ℝ) ^ entropy q = ∏ h, (q h ^ q h)⁻¹ := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log 2 * entropy q = ∑ h, -(q h * Real.log (q h)) := by
    rw [Finset.sum_neg_distrib]
    dsimp [entropy]
    field_simp
  rw [hlog, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro h _
  by_cases hz : q h = 0
  · simp [hz]
  · rw [Real.rpow_def_of_pos (lt_of_le_of_ne (hq h) (Ne.symm hz)), Real.exp_neg]
    congr 2
    ring

/-- The entropy-weighted geometric mean is at most the sum. -/
theorem entropy_variational_le {H : Type*} [Fintype H]
    (a q : H → ℝ) (ha : ∀ h, 0 ≤ a h) (hq : ∀ h, 0 ≤ q h)
    (hqsum : ∑ h, q h = 1) :
    (2 : ℝ) ^ entropy q * ∏ h, a h ^ q h ≤ ∑ h, a h := by
  rw [two_rpow_entropy_eq_prod q hq, ← Finset.prod_mul_distrib]
  calc
    ∏ h, (q h ^ q h)⁻¹ * a h ^ q h
      = ∏ h, (a h / q h) ^ q h := by
        apply Finset.prod_congr rfl
        intro h _
        by_cases hz : q h = 0
        · simp [hz]
        · rw [Real.div_rpow (ha h) (hq h), div_eq_mul_inv, mul_comm]
    _ ≤ ∑ h, q h * (a h / q h) :=
      Real.geom_mean_le_arith_mean_weighted Finset.univ q (fun h => a h / q h)
        (fun h _ => hq h) hqsum (fun h _ => div_nonneg (ha h) (hq h))
    _ ≤ ∑ h, a h := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hz : q h = 0
      · simpa [hz] using ha h
      · rw [mul_div_cancel₀ _ hz]

/-- Normalizing nonnegative coordinates of positive total mass attains the
entropy variational bound, including coordinates that vanish. -/
theorem entropy_variational_normalized {H : Type*} [Fintype H]
    (a : H → ℝ) (ha : ∀ h, 0 ≤ a h) (hs : 0 < ∑ h, a h) :
    (2 : ℝ) ^ entropy (fun h => a h / ∑ i, a i) *
      ∏ h, a h ^ (a h / ∑ i, a i) = ∑ h, a h := by
  have hq : ∀ h, 0 ≤ a h / ∑ i, a i := fun h => div_nonneg (ha h) hs.le
  rw [two_rpow_entropy_eq_prod _ hq, ← Finset.prod_mul_distrib]
  calc
    ∏ h, ((a h / ∑ i, a i) ^ (a h / ∑ i, a i))⁻¹ * a h ^ (a h / ∑ i, a i)
        = ∏ h, (∑ i, a i) ^ (a h / ∑ i, a i) := by
          apply Finset.prod_congr rfl
          intro h _
          by_cases hz : a h = 0
          · simp [hz]
          · rw [mul_comm, ← div_eq_mul_inv, ← Real.div_rpow (ha h) (hq h)]
            congr 1
            field_simp
    _ = (∑ i, a i) ^ (∑ h, a h / ∑ i, a i) :=
      (Real.rpow_sum_of_pos hs _ _).symm
    _ = ∑ h, a h := by rw [← Finset.sum_div, div_self hs.ne', Real.rpow_one]

/-- The entropy variational bound is attained by a probability distribution.
For positive total mass use normalized coordinates; for zero total mass any
point mass suffices. -/
theorem entropy_variational_attained {H : Type*} [Fintype H] [Nonempty H]
    (a : H → ℝ) (ha : ∀ h, 0 ≤ a h) :
    ∃ q : H → ℝ, (∀ h, 0 ≤ q h) ∧ (∑ h, q h = 1) ∧
      (2 : ℝ) ^ entropy q * ∏ h, a h ^ q h = ∑ h, a h := by
  classical
  have hs : 0 ≤ ∑ h, a h := Finset.sum_nonneg fun h _ => ha h
  rcases hs.eq_or_lt with hs | hs
  · let h₀ : H := Classical.arbitrary H
    let q : H → ℝ := fun h => if h = h₀ then 1 else 0
    have hq : ∀ h, 0 ≤ q h := by intro h; dsimp [q]; split <;> norm_num
    have hqsum : ∑ h, q h = 1 := by simp [q]
    refine ⟨q, hq, hqsum, le_antisymm (entropy_variational_le a q ha hq hqsum) ?_⟩
    rw [← hs]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Finset.prod_nonneg fun h _ => Real.rpow_nonneg (ha h) _)
  · refine ⟨fun h => a h / ∑ i, a i, fun h => div_nonneg (ha h) hs.le, ?_,
      entropy_variational_normalized a ha hs⟩
    rw [← Finset.sum_div, div_self hs.ne']

/-- Lemma 2.8: the maximum entropy-weighted product is the sum of the
nonnegative coordinates. `IsGreatest` records both attainment and the bound. -/
theorem entropy_variational_sum {H : Type*} [Fintype H] [Nonempty H]
    (a : H → ℝ) (ha : ∀ h, 0 ≤ a h) :
    IsGreatest {v : ℝ | ∃ q : H → ℝ, (∀ h, 0 ≤ q h) ∧ (∑ h, q h = 1) ∧
      v = (2 : ℝ) ^ entropy q * ∏ h, a h ^ q h} (∑ h, a h) := by
  obtain ⟨q, hq, hqsum, heq⟩ := entropy_variational_attained a ha
  refine ⟨⟨q, hq, hqsum, heq.symm⟩, ?_⟩
  rintro v ⟨q, hq, hqsum, rfl⟩
  exact entropy_variational_le a q ha hq hqsum

/-- The supremum formulation of the entropy variational identity. -/
theorem entropy_variational_sSup {H : Type*} [Fintype H] [Nonempty H]
    (a : H → ℝ) (ha : ∀ h, 0 ≤ a h) :
    sSup {v : ℝ | ∃ q : H → ℝ, (∀ h, 0 ≤ q h) ∧ (∑ h, q h = 1) ∧
      v = (2 : ℝ) ^ entropy q * ∏ h, a h ^ q h} = ∑ h, a h :=
  (entropy_variational_sum a ha).csSup_eq

/-- Raising the variational bound to a positive parameter gives the entropy
expression used for fractional value. -/
theorem entropy_variational_rpow_le {H : Type*} [Fintype H]
    (v q : H → ℝ) (hv : ∀ h, 0 ≤ v h) (hq : ∀ h, 0 ≤ q h)
    (hqsum : ∑ h, q h = 1) {τ : ℝ} (hτ : 0 < τ) :
    (2 : ℝ) ^ (τ * entropy q) * ∏ h, v h ^ q h ≤
      (∑ h, v h ^ τ⁻¹) ^ τ := by
  have hprod : 0 ≤ ∏ h, (v h ^ τ⁻¹) ^ q h :=
    Finset.prod_nonneg fun h _ => Real.rpow_nonneg (Real.rpow_nonneg (hv h) _) _
  have h := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hprod)
    (entropy_variational_le (fun h => v h ^ τ⁻¹) q
      (fun h => Real.rpow_nonneg (hv h) _) hq hqsum) hτ.le
  rw [Real.mul_rpow (by positivity) hprod,
    ← Real.rpow_mul (by positivity),
    ← Real.finsetProd_rpow _ _
      (fun h _ => Real.rpow_nonneg (Real.rpow_nonneg (hv h) _) _)] at h
  convert h using 1
  congr 1
  · congr 1
    exact mul_comm _ _
  · apply Finset.prod_congr rfl
    intro h _
    rw [← Real.rpow_mul (Real.rpow_nonneg (hv h) _), ← Real.rpow_mul (hv h)]
    congr 1
    field_simp

end MatrixMultiplication
