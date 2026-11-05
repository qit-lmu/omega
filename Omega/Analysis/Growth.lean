module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# The numerical growth argument

This file isolates the numerical part of Section 6 of `material/main.tex`.
The hypotheses will be supplied by the fractional value of polynomial
multiplication tensors. No tensor-theoretic assertions are assumed globally.

The proof uses the elementary argument in the proof of `lem:4/3`.
The sharper Gamma-function estimate in that lemma is a separate result.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The properties of the normalized polynomial-multiplication value
used in Section 6. The concavity inequality is indexed without subtraction:
its middle argument is `b + 1` and its left endpoint is `b`. -/
structure GrowthHypotheses (P : ℕ → ℕ → ℝ) : Prop where
  symmetry : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → P a b = P b a
  boundary : ∀ a : ℕ, 1 ≤ a → P 1 a = a
  concavity : ∀ a b p : ℕ, 1 ≤ a → 1 ≤ b →
    (p : ℝ) * P a b + P a (b + p + 1) ≤ ((p : ℝ) + 1) * P a (b + 1)
  tripling : ∀ a : ℕ, 1 ≤ a → 3 * P a a ≤ P a (4 * a - 1)

/-- The multiplicative factor in the paper's recurrence `eq:PM-recurrence`. -/
noncomputable def growthRatio (a : ℝ) : ℝ :=
  (3 * a + 1) * (3 * a + 2) / (3 * a * (3 * a - 1))

theorem growthRatio_pos {a : ℝ} (ha : 1 ≤ a) : 0 < growthRatio a := by
  unfold growthRatio
  have ha0 : 0 < a := by linarith
  have hden : 0 < 3 * a - 1 := by linarith
  positivity

namespace GrowthHypotheses

variable {P : ℕ → ℕ → ℝ} (h : GrowthHypotheses P)

include h

/-- The first application of concavity in the proof of `lem:4/3`. -/
theorem off_diagonal {a : ℕ} (ha : 1 ≤ a) :
    (3 * (a : ℝ) + 1) * P a a ≤ (3 * (a : ℝ) - 1) * P (a + 1) a := by
  have hc := h.concavity a a (3 * a - 2) ha ha
  have hi : a + (3 * a - 2) + 1 = 4 * a - 1 := by omega
  have hp : ((3 * a - 2 : ℕ) : ℝ) = 3 * (a : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hi, hp, h.symmetry a (a + 1) ha (by omega)] at hc
  have ht := h.tripling a ha
  nlinarith

/-- The second application of concavity in the proof of `lem:4/3`. -/
theorem diagonal_step {a : ℕ} (ha : 1 ≤ a) :
    (3 * (a : ℝ) + 2) * P (a + 1) a ≤ 3 * (a : ℝ) * P (a + 1) (a + 1) := by
  have hc := h.concavity (a + 1) a (3 * a + 2) (by omega) ha
  have hi : a + (3 * a + 2) + 1 = 4 * (a + 1) - 1 := by omega
  rw [hi] at hc
  push_cast at hc
  have ht := h.tripling (a + 1) (by omega)
  nlinarith

/-- A denominator-free version of `eq:PM-recurrence`. -/
theorem diagonal_recurrence_mul {a : ℕ} (ha : 1 ≤ a) :
    (3 * (a : ℝ) + 1) * (3 * (a : ℝ) + 2) * P a a ≤
      (3 * (a : ℝ)) * (3 * (a : ℝ) - 1) * P (a + 1) (a + 1) := by
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h₁ := mul_le_mul_of_nonneg_left (h.off_diagonal ha)
    (by linarith : 0 ≤ 3 * (a : ℝ) + 2)
  have h₂ := mul_le_mul_of_nonneg_left (h.diagonal_step ha)
    (by linarith : 0 ≤ 3 * (a : ℝ) - 1)
  nlinarith

/-- The paper's recurrence `eq:PM-recurrence`. -/
theorem diagonal_recurrence {a : ℕ} (ha : 1 ≤ a) :
    growthRatio a * P a a ≤ P (a + 1) (a + 1) := by
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hden : 0 < 3 * (a : ℝ) * (3 * (a : ℝ) - 1) := by
    have : 0 < 3 * (a : ℝ) - 1 := by linarith
    positivity
  unfold growthRatio
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith [h.diagonal_recurrence_mul ha]

end GrowthHypotheses

/-- Cubing the elementary growth-factor inequality avoids fractional powers.
The polynomial identity supplies a certificate valid for every `a ≥ 1`. -/
theorem growthRatio_cube_mul {a : ℝ} (ha : 1 ≤ a) :
    (a + 1) ^ 4 ≤ growthRatio a ^ 3 * a ^ 4 := by
  have ha0 : 0 < a := by linarith
  have ht : 0 ≤ a - 1 := by linarith
  have hden : 0 < 3 * a * (3 * a - 1) := by
    have : 0 < 3 * a - 1 := by linarith
    positivity
  unfold growthRatio
  rw [div_pow, div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hden 3)).2
  have hpoly : 0 ≤ a ^ 3 *
      (4544 + 17936 * (a - 1) + 27324 * (a - 1) ^ 2 +
        20007 * (a - 1) ^ 3 + 7074 * (a - 1) ^ 4 + 972 * (a - 1) ^ 5) := by
    positivity
  have hid : ((3 * a + 1) * (3 * a + 2)) ^ 3 * a ^ 4 -
      (a + 1) ^ 4 * (3 * a * (3 * a - 1)) ^ 3 =
      a ^ 3 * (4544 + 17936 * (a - 1) + 27324 * (a - 1) ^ 2 +
        20007 * (a - 1) ^ 3 + 7074 * (a - 1) ^ 4 + 972 * (a - 1) ^ 5) := by
    ring
  linarith

namespace GrowthHypotheses

variable {P : ℕ → ℕ → ℝ} (h : GrowthHypotheses P)

include h

/-- The elementary diagonal lower bound, expressed using natural powers. -/
theorem diagonal_nonneg_and_cube {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ P a a ∧ (a : ℝ) ^ 4 ≤ (P a a) ^ 3 := by
  induction a, ha using Nat.le_induction with
  | base =>
      rw [h.boundary 1 (by omega)]
      norm_num
  | succ a ha ih =>
      have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hr : 0 ≤ growthRatio a := (growthRatio_pos har).le
      have hrec := h.diagonal_recurrence ha
      have hprod : 0 ≤ growthRatio a * P a a := mul_nonneg hr ih.1
      refine ⟨hprod.trans hrec, ?_⟩
      calc
        ((a + 1 : ℕ) : ℝ) ^ 4 = ((a : ℝ) + 1) ^ 4 := by norm_num
        _ ≤ growthRatio a ^ 3 * (a : ℝ) ^ 4 := growthRatio_cube_mul har
        _ ≤ growthRatio a ^ 3 * (P a a) ^ 3 :=
          mul_le_mul_of_nonneg_left ih.2 (pow_nonneg hr 3)
        _ = (growthRatio a * P a a) ^ 3 := by ring
        _ ≤ (P (a + 1) (a + 1)) ^ 3 := by gcongr

/-- The elementary bound in the proof of `lem:4/3`. -/
theorem diagonal_rpow_lower_bound {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ^ (4 / 3 : ℝ) ≤ P a a := by
  have hg := h.diagonal_nonneg_and_cube ha
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg a) _) hg.1
    (by norm_num : (0 : ℝ) < 3)).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg a)]
  norm_num
  exact hg.2

end GrowthHypotheses

/-- A power bounded by a fixed linear function on positive integers has
exponent at most one. This avoids an asymptotic-limit argument. -/
theorem exponent_le_one_of_nat_rpow_le_two_mul {r : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ r ≤ 2 * (n : ℝ)) : r ≤ 1 := by
  by_contra hr
  have hrp : 0 < r - 1 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ) ^ (r - 1)⁻¹)
  have hn0 : (0 : ℝ) < n :=
    lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    hn hrp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    inv_mul_cancel₀ (ne_of_gt hrp), Real.rpow_one] at hp
  have heq : (n : ℝ) ^ r = (n : ℝ) ^ (r - 1) * (n : ℝ) := by
    conv_lhs => rw [show r = (r - 1) + 1 by ring]
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hb := h n hn1
  rw [heq] at hb
  have hc := mul_lt_mul_of_pos_right hp hn0
  linarith

/-- The numerical conclusion of Section 6. Tensor theory must establish
`GrowthHypotheses` and the upper bound before this result applies. -/
theorem exponent_le_nine_quarters_of_growth {P : ℕ → ℕ → ℝ}
    (h : GrowthHypotheses P) {w : ℝ} (hw : 0 < w)
    (hupper : ∀ a : ℕ, 1 ≤ a → (P a a) ^ (w / 3) ≤ 2 * (a : ℝ) - 1) :
    w ≤ 9 / 4 := by
  have hpow : ∀ a : ℕ, 1 ≤ a → (a : ℝ) ^ (4 * w / 9) ≤ 2 * (a : ℝ) := by
    intro a ha
    have hlo := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg a) _)
      (h.diagonal_rpow_lower_bound ha) (by positivity : 0 ≤ w / 3)
    rw [← Real.rpow_mul (Nat.cast_nonneg a)] at hlo
    have he : (4 / 3 : ℝ) * (w / 3) = 4 * w / 9 := by ring
    rw [he] at hlo
    linarith [hupper a ha]
  have hbound := exponent_le_one_of_nat_rpow_le_two_mul hpow
  linarith

end MatrixMultiplication
