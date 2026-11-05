module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Rational probability approximation with unchanged support

Round each scaled coordinate upward to a natural number, then divide by
the total count. Zero coordinates remain zero, every positive coordinate
remains positive, and the normalized counts converge to the original
probability vector. The natural counts are suitable for multinomial
arguments without any further choice of common denominators.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped BigOperators Topology

/-- A finite probability vector is the coordinatewise limit of normalized
natural counts with exactly the same support and a positive total count. -/
theorem probability_count_approximation {H : Type*} [Fintype H]
    (q : H → ℝ) (hq : ∀ h, 0 ≤ q h) (hqsum : ∑ h, q h = 1) :
    ∃ (c : ℕ → H → ℕ) (N : ℕ → ℕ),
      (∀ n, 0 < N n) ∧ (∀ n, ∑ h, c n h = N n) ∧
      (∀ n h, c n h = 0 ↔ q h = 0) ∧
      ∀ h, Tendsto (fun n => (c n h : ℝ) / (N n : ℝ)) atTop (𝓝 (q h)) := by
  classical
  let c : ℕ → H → ℕ := fun n h => ⌈q h * ((n + 1 : ℕ) : ℝ)⌉₊
  let N : ℕ → ℕ := fun n => ∑ h, c n h
  have hscale_pos (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNlower (n : ℕ) : n + 1 ≤ N n := by
    have hlower : ((n + 1 : ℕ) : ℝ) ≤ (N n : ℝ) := by
      calc
        ((n + 1 : ℕ) : ℝ) = (∑ h, q h) * ((n + 1 : ℕ) : ℝ) := by
          rw [hqsum, one_mul]
        _ = ∑ h, q h * ((n + 1 : ℕ) : ℝ) := Finset.sum_mul ..
        _ ≤ ∑ h, (c n h : ℝ) := Finset.sum_le_sum fun h _ => Nat.le_ceil _
        _ = (N n : ℝ) := by simp [N]
    exact_mod_cast hlower
  have hNpos (n : ℕ) : 0 < N n := (Nat.succ_pos n).trans_le (hNlower n)
  have hsupport (n : ℕ) (h : H) : c n h = 0 ↔ q h = 0 := by
    dsimp only [c]
    rw [Nat.ceil_eq_zero]
    constructor
    · intro hzero
      have heq : q h * ((n + 1 : ℕ) : ℝ) = 0 :=
        le_antisymm hzero (mul_nonneg (hq h) (hscale_pos n).le)
      exact (mul_eq_zero.mp heq).resolve_right (hscale_pos n).ne'
    · intro hzero
      simp [hzero]
  have hscale : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hc (h : H) :
      Tendsto (fun n => (c n h : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (q h)) :=
    (tendsto_nat_ceil_mul_div_atTop (hq h)).comp hscale
  have hN : Tendsto (fun n => (N n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := tendsto_finsetSum Finset.univ (fun h _ => hc h)
    simpa only [← Finset.sum_div, ← Nat.cast_sum, hqsum] using h
  refine ⟨c, N, hNpos, fun _ => rfl, hsupport, fun h => ?_⟩
  have hlim := (hc h).div hN (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlim
  refine hlim.congr' (Eventually.of_forall fun n => ?_)
  exact div_div_div_cancel_right₀ (hscale_pos n).ne' _ _

/-- Every finite real probability vector admits rational probability
approximations whose zero coordinates agree with it at every stage. -/
theorem rational_probability_approximation {H : Type*} [Fintype H]
    (q : H → ℝ) (hq : ∀ h, 0 ≤ q h) (hqsum : ∑ h, q h = 1) :
    ∃ r : ℕ → H → ℚ,
      (∀ n h, 0 ≤ r n h) ∧ (∀ n, ∑ h, r n h = 1) ∧
      (∀ n h, r n h = 0 ↔ q h = 0) ∧
      ∀ h, Tendsto (fun n => (r n h : ℝ)) atTop (𝓝 (q h)) := by
  classical
  obtain ⟨c, N, hN, hsum, hsupport, hlim⟩ := probability_count_approximation q hq hqsum
  let r : ℕ → H → ℚ := fun n h => (c n h : ℚ) / (N n : ℚ)
  have hNne (n : ℕ) : (N n : ℚ) ≠ 0 := by exact_mod_cast (hN n).ne'
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro n h
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    dsimp only [r]
    rw [← Finset.sum_div, ← Nat.cast_sum, hsum, div_self (hNne n)]
  · intro n h
    simpa only [r, div_eq_zero_iff, hNne n, or_false, Nat.cast_eq_zero] using hsupport n h
  · intro h
    simpa only [r, Rat.cast_div, Rat.cast_natCast] using hlim h

end MatrixMultiplication
