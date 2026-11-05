module

public import Omega.Analysis.Growth
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma-function growth bound

The exact lower bound in Lemma 6.1 follows directly from the Gamma functional
equation and the diagonal recurrence. Its asymptotic coefficient follows from
Euler's limit formula for Gamma.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped Topology

/-- The exact lower bound in Lemma 6.1. -/
noncomputable def gammaGrowthBound (a : ℕ) : ℝ :=
  (3 * a - 1) / (2 * Real.Gamma (4 / 3)) *
    (Real.Gamma (a + 1 / 3) / Real.Gamma a)

theorem gammaGrowthBound_one : gammaGrowthBound 1 = 1 := by
  have hg := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne'
  norm_num [gammaGrowthBound, Real.Gamma_one, show (1 : ℝ) + 1 / 3 = 4 / 3 by norm_num]
  field_simp

theorem gammaGrowthBound_pos {a : ℕ} (ha : 1 ≤ a) :
    0 < gammaGrowthBound a := by
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  unfold gammaGrowthBound
  have hnum : 0 < 3 * (a : ℝ) - 1 := by linarith
  positivity

theorem gammaGrowthBound_succ {a : ℕ} (ha : 1 ≤ a) :
    gammaGrowthBound (a + 1) = growthRatio a * gammaGrowthBound a := by
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (a : ℝ) ≠ 0 := by linarith
  have ha1 : (a : ℝ) + 1 / 3 ≠ 0 := by linarith
  have hd : 3 * (a : ℝ) - 1 ≠ 0 := by linarith
  unfold gammaGrowthBound growthRatio
  push_cast
  rw [show (a : ℝ) + 1 + 1 / 3 = (a + 1 / 3) + 1 by ring,
    Real.Gamma_add_one ha1, Real.Gamma_add_one ha0]
  field_simp
  ring

/-- The exact Gamma bound itself dominates the elementary power bound. -/
theorem rpow_le_gammaGrowthBound {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ^ (4 / 3 : ℝ) ≤ gammaGrowthBound a := by
  have hc : (a : ℝ) ^ 4 ≤ gammaGrowthBound a ^ 3 := by
    induction a, ha using Nat.le_induction with
    | base => rw [gammaGrowthBound_one]; norm_num
    | succ a ha ih =>
        have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
        rw [gammaGrowthBound_succ ha, mul_pow, Nat.cast_add, Nat.cast_one]
        exact (growthRatio_cube_mul har).trans
          (mul_le_mul_of_nonneg_left ih (pow_nonneg (growthRatio_pos har).le 3))
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg a) _)
    (gammaGrowthBound_pos ha).le (by norm_num : (0 : ℝ) < 3)).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg a)]
  norm_num
  exact hc

/-- Iterating the Gamma functional equation as a finite product. -/
theorem gamma_add_nat_eq_prod {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.Gamma (s + n) = Real.Gamma s * ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
        Real.Gamma_add_one (by positivity : s + n ≠ 0), ih, Finset.prod_range_succ]
      ring

/-- The finite product in `eq:PM-Gamma`, including the empty product at `a=1`. -/
theorem gammaGrowthBound_prod_eq_gamma (a : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ Finset.Ico 1 a, ((i : ℝ) + 1 / 3) / i) =
      Real.Gamma (a + 1 / 3) / (Real.Gamma (4 / 3) * Real.Gamma a) := by
  induction a, ha using Nat.le_induction with
  | base =>
      have hg := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne'
      norm_num [show (1 : ℝ) + 1 / 3 = 4 / 3 by norm_num, hg]
  | succ a ha ih =>
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      rw [Finset.prod_Ico_succ_top ha, ih]
      push_cast
      rw [show (a : ℝ) + 1 + 1 / 3 = (a + 1 / 3) + 1 by ring,
        Real.Gamma_add_one (by positivity : (a : ℝ) + 1 / 3 ≠ 0),
        Real.Gamma_add_one ha0.ne']
      ring

/-- The explicit rational-product expression for the Gamma lower bound. -/
theorem gammaGrowthBound_eq_prod (a : ℕ) (ha : 1 ≤ a) :
    gammaGrowthBound a = (3 * (a : ℝ) - 1) / 2 *
      ∏ i ∈ Finset.Ico 1 a, (3 * (i : ℝ) + 1) / (3 * i) := by
  have hprod : (∏ i ∈ Finset.Ico 1 a, (3 * (i : ℝ) + 1) / (3 * i)) =
      ∏ i ∈ Finset.Ico 1 a, ((i : ℝ) + 1 / 3) / i := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hprod, gammaGrowthBound_prod_eq_gamma a ha]
  unfold gammaGrowthBound
  ring

/-- Euler's approximants express the quotient of Gamma functions. -/
theorem gamma_ratio_eq_gammaSeq {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) :
    Real.Gamma (n + s) / (Real.Gamma n * (n : ℝ) ^ s) =
      ((n : ℝ) / (n + s)) * (Real.Gamma s / Real.GammaSeq s n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgs := (Real.Gamma_pos_of_pos hs).ne'
  have hgn := (Real.Gamma_pos_of_pos hnpos).ne'
  have hgns := (Real.Gamma_pos_of_pos (add_pos hnpos hs)).ne'
  have hnp := (Real.rpow_pos_of_pos hnpos s).ne'
  have hns : (n : ℝ) + s ≠ 0 := (add_pos hnpos hs).ne'
  have hprod : (∏ j ∈ Finset.range (n + 1), (s + j)) =
      ((n : ℝ) + s) * Real.Gamma (n + s) / Real.Gamma s := by
    apply (eq_div_iff hgs).2
    rw [mul_comm, ← gamma_add_nat_eq_prod hs,
      Nat.cast_add, Nat.cast_one, show s + ((n : ℝ) + 1) = (n + s) + 1 by ring,
      Real.Gamma_add_one hns]
  have hfact : (n.factorial : ℝ) = (n : ℝ) * Real.Gamma n := by
    rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_add_one hnpos.ne']
  rw [Real.GammaSeq, hprod, hfact]
  field_simp

/-- The Gamma quotient asymptotic used in Remark 6.2, directly from Euler's
limit formula. -/
theorem gamma_ratio_rpow_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => Real.Gamma (n + s) / (Real.Gamma n * (n : ℝ) ^ s))
      atTop (𝓝 1) := by
  have hg := (Real.Gamma_pos_of_pos hs).ne'
  have h := (tendsto_natCast_div_add_atTop s).mul
    (tendsto_const_nhds (x := Real.Gamma s) |>.div (Real.GammaSeq_tendsto_Gamma s) hg)
  simp only [div_self hg, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (gamma_ratio_eq_gammaSeq hs hn).symm

/-- The Gamma quotient in the manuscript is asymptotic to `a^(1/3)`. -/
theorem gamma_ratio_one_third_asymptotic :
    Tendsto (fun a : ℕ => Real.Gamma (a + 1 / 3) /
      (Real.Gamma a * (a : ℝ) ^ (1 / 3 : ℝ))) atTop (𝓝 1) :=
  gamma_ratio_rpow_tendsto (by norm_num)

/-- The coefficient of `a^(4/3)` in the exact Gamma lower bound. -/
theorem gammaGrowthBound_div_rpow_tendsto :
    Tendsto (fun a : ℕ => gammaGrowthBound a / (a : ℝ) ^ (4 / 3 : ℝ))
      atTop (𝓝 (3 / (2 * Real.Gamma (4 / 3)))) := by
  have h := ((tendsto_const_nhds (x := (3 : ℝ))).sub
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const
    (2 * Real.Gamma (4 / 3)) |>.mul gamma_ratio_one_third_asymptotic
  simp only [sub_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with a ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hpow : (a : ℝ) ^ (4 / 3 : ℝ) = (a : ℝ) * (a : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add ha0, Real.rpow_one]
  rw [gammaGrowthBound, hpow]
  field_simp

namespace GrowthHypotheses

variable {P : ℕ → ℕ → ℝ} (h : GrowthHypotheses P)

include h

/-- The sharp Gamma-function lower bound in Lemma 6.1. -/
theorem diagonal_gamma_lower_bound {a : ℕ} (ha : 1 ≤ a) :
    gammaGrowthBound a ≤ P a a := by
  induction a, ha using Nat.le_induction with
  | base => rw [gammaGrowthBound_one, h.boundary 1 (by omega)]; norm_num
  | succ a ha ih =>
      rw [gammaGrowthBound_succ ha]
      exact (mul_le_mul_of_nonneg_left ih
        (growthRatio_pos (by exact_mod_cast ha)).le).trans (h.diagonal_recurrence ha)

end GrowthHypotheses

end MatrixMultiplication
