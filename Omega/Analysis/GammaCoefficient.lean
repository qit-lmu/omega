module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic

/-!
# A certified enclosure for the Gamma coefficient

The coefficient in Remark 6.2 is bounded using rational products. Cubing removes
all fractional powers, and a shifted denominator accelerates Euler's limit.
-/

@[expose] public section

open Filter Topology

namespace MatrixMultiplication

/-- The rational product `∏ k = 1, ..., n, (1 + 1 / (3k))`. -/
def gammaThirdProduct : ℕ → ℚ
  | 0 => 1
  | n + 1 => gammaThirdProduct n * (3 * n + 4) / (3 * n + 3)

private theorem gammaThirdProduct_pos (n : ℕ) : 0 < gammaThirdProduct n := by
  induction n with
  | zero => norm_num [gammaThirdProduct]
  | succ n hn => simp only [gammaThirdProduct]; positivity

private theorem gammaThirdProduct_cast_succ (n : ℕ) :
    (gammaThirdProduct (n + 1) : ℝ) =
      (gammaThirdProduct n : ℝ) * (3 * n + 4) / (3 * n + 3) := by
  simp [gammaThirdProduct]

private theorem gammaThirdProduct_cast_pos (n : ℕ) :
    0 < (gammaThirdProduct n : ℝ) := by exact_mod_cast gammaThirdProduct_pos n

private theorem gammaThirdProduct_mul_factorial (n : ℕ) :
    (gammaThirdProduct n : ℝ) * n.factorial =
      ∏ j ∈ Finset.range n, ((1 : ℝ) / 3 + (j + 1)) := by
  induction n with
  | zero => simp [gammaThirdProduct]
  | succ n hn =>
    rw [gammaThirdProduct_cast_succ, Nat.factorial_succ, Nat.cast_mul,
      Finset.prod_range_succ, ← hn]
    have h : (3 * (n : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private theorem gammaThirdProduct_GammaSeq (n : ℕ) :
    (gammaThirdProduct n : ℝ) * Real.GammaSeq (1/3) n =
      3 * (n : ℝ) ^ (1/3 : ℝ) := by
  rw [Real.GammaSeq, Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [← gammaThirdProduct_mul_factorial]
  have hp := gammaThirdProduct_cast_pos n
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- An upper rational approximation to `Γ(4/3)⁻³`. -/
noncomputable def gammaThirdUpper (n : ℕ) : ℝ :=
  (gammaThirdProduct n : ℝ) ^ 3 / ((n : ℝ) + 2/3)

/-- A lower rational approximation to `Γ(4/3)⁻³`, for positive `n`. -/
noncomputable def gammaThirdLower (n : ℕ) : ℝ :=
  (gammaThirdProduct n : ℝ) ^ 3 / ((n : ℝ) + 2/3 + 1/(9*n))

private theorem gammaThirdUpper_antitone : Antitone gammaThirdUpper := by
  apply antitone_nat_of_succ_le
  intro n
  rw [gammaThirdUpper, gammaThirdUpper, gammaThirdProduct_cast_succ]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 0 < 3 * (n : ℝ) + 3 := by positivity
  have h₀ : 0 < (n : ℝ) + 2/3 := by positivity
  have h₁ : 0 < ((n + 1 : ℕ) : ℝ) + 2/3 := by positivity
  rw [div_pow, div_le_div_iff₀ h₁ h₀, div_mul_eq_mul_div,
    div_le_iff₀ (pow_pos hd 3)]
  push_cast
  nlinarith [pow_nonneg (gammaThirdProduct_cast_pos n).le 3]

private theorem gammaThirdLower_step (n : ℕ) (hn : 1 ≤ n) :
    gammaThirdLower n ≤ gammaThirdLower (n + 1) := by
  rw [gammaThirdLower, gammaThirdLower, gammaThirdProduct_cast_succ]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < 3 * (n : ℝ) + 3 := by positivity
  have h₀ : 0 < (n : ℝ) + 2/3 + 1/(9*n) := by positivity
  have h₁ : 0 < ((n + 1 : ℕ) : ℝ) + 2/3 + 1/(9*((n+1:ℕ):ℝ)) := by positivity
  rw [div_pow, div_le_div_iff₀ h₀ h₁, div_mul_eq_mul_div,
    le_div_iff₀ (pow_pos hd 3)]
  push_cast
  field_simp
  nlinarith [pow_nonneg (gammaThirdProduct_cast_pos n).le 3]

private theorem gammaThirdProduct_cube (n : ℕ) :
    (gammaThirdProduct n : ℝ) ^ 3 * Real.GammaSeq (1/3) n ^ 3 = 27 * n := by
  have h := congrArg (fun x : ℝ => x ^ 3) (gammaThirdProduct_GammaSeq n)
  have hroot : ((n : ℝ) ^ (1/3 : ℝ)) ^ 3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [mul_pow, mul_pow, hroot] at h
  norm_num at h
  exact h

private theorem GammaSeq_third_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    Real.GammaSeq (1/3) n ≠ 0 := by
  intro h
  have hc := gammaThirdProduct_cube n
  rw [h, zero_pow (by omega), mul_zero] at hc
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem gammaThird_limit_value :
    27 / Real.Gamma (1/3) ^ 3 = 1 / Real.Gamma (4/3) ^ 3 := by
  have hg := Real.Gamma_add_one (by norm_num : (1/3 : ℝ) ≠ 0)
  norm_num at hg
  rw [hg]
  ring

private theorem gammaThirdUpper_tendsto :
    Tendsto gammaThirdUpper atTop (𝓝 (1 / Real.Gamma (4/3) ^ 3)) := by
  have hg : Real.Gamma (1/3) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h := ((tendsto_const_nhds (x := (27 : ℝ))).mul
    (tendsto_natCast_div_add_atTop (2/3 : ℝ))).div
    ((Real.GammaSeq_tendsto_Gamma (1/3)).pow 3) hg
  rw [mul_one, gammaThird_limit_value] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (n : ℝ) + 2/3 ≠ 0 := by positivity
  have hc := gammaThirdProduct_cube n
  have hgs := GammaSeq_third_ne_zero hn
  dsimp only [Pi.div_apply]
  unfold gammaThirdUpper
  field_simp
  nlinarith

private theorem gammaThirdLower_tendsto :
    Tendsto gammaThirdLower atTop (𝓝 (1 / Real.Gamma (4/3) ^ 3)) := by
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := (2/3 : ℝ))).mul hinv) |>.add
    ((tendsto_const_nhds (x := (1/9 : ℝ))).mul (hinv.pow 2))
  norm_num at hd
  have hg : Real.Gamma (1/3) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h := ((tendsto_const_nhds (x := (27 : ℝ))).div hd (by norm_num)).div
    ((Real.GammaSeq_tendsto_Gamma (1/3)).pow 3) hg
  rw [div_one, gammaThird_limit_value] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hgs := GammaSeq_third_ne_zero hn
  have hc := gammaThirdProduct_cube n
  have hd₀ : (1 : ℝ) + 2/3 * (1/n) + 1/9 * (1/n)^2 ≠ 0 := by positivity
  have hd₁ : (n : ℝ) + 2/3 + 1/(9*n) ≠ 0 := by positivity
  dsimp only [Pi.div_apply]
  unfold gammaThirdLower
  field_simp
  nlinarith

/-- The accelerated rational products bracket the reciprocal Gamma cube. -/
theorem gammaThird_bracket (n : ℕ) (hn : 1 ≤ n) :
    gammaThirdLower n ≤ 1 / Real.Gamma (4/3) ^ 3 ∧
      1 / Real.Gamma (4/3) ^ 3 ≤ gammaThirdUpper n := by
  refine ⟨?_, gammaThirdUpper_antitone.le_of_tendsto gammaThirdUpper_tendsto n⟩
  have hm : Monotone (fun m => gammaThirdLower (m + 1)) := by
    apply monotone_nat_of_le_succ
    intro m
    exact gammaThirdLower_step (m+1) (by omega)
  have ht := gammaThirdLower_tendsto.comp (tendsto_add_atTop_nat 1)
  simpa only [Nat.sub_add_cancel hn] using hm.ge_of_tendsto ht (n-1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem gammaThird_lower_numeric :
    (167976 / 100000 : ℚ) ^ 3 <
      (27 : ℚ) / 8 * gammaThirdProduct 320 ^ 3 / (320 + 2/3 + 1/(9*320)) := by
  norm_num [gammaThirdProduct]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem gammaThird_upper_numeric :
    (27 : ℚ) / 8 * gammaThirdProduct 320 ^ 3 / (320 + 2/3) <
      (167977 / 100000 : ℚ) ^ 3 := by
  norm_num [gammaThirdProduct]

/-- The rigorous numerical enclosure in Remark 6.2. -/
theorem gamma_growth_coefficient_bounds :
    (1.67976 : ℝ) < 3 / (2 * Real.Gamma (4/3)) ∧
      3 / (2 * Real.Gamma (4/3)) < (1.67977 : ℝ) := by
  have hbr := gammaThird_bracket 320 (by norm_num)
  have hc : (3 / (2 * Real.Gamma (4/3))) ^ 3 =
      (27 : ℝ) / 8 * (1 / Real.Gamma (4/3) ^ 3) := by ring
  have hpos : (0 : ℝ) ≤ 3 / (2 * Real.Gamma (4/3)) := by positivity
  have hlo : (1.67976 : ℝ) ^ 3 < (27 : ℝ) / 8 * gammaThirdLower 320 := by
    unfold gammaThirdLower
    rw [← mul_div_assoc]
    have h : (167976 / 100000 : ℝ) ^ 3 <
        (27 : ℝ) / 8 * (gammaThirdProduct 320 : ℝ) ^ 3 /
          (320 + 2/3 + 1/(9*320)) := by
      have h := (Rat.cast_lt (K := ℝ)).2 gammaThird_lower_numeric
      push_cast at h
      exact h
    convert h using 1
    norm_num
  have hhi : (27 : ℝ) / 8 * gammaThirdUpper 320 < (1.67977 : ℝ) ^ 3 := by
    unfold gammaThirdUpper
    rw [← mul_div_assoc]
    have h : (27 : ℝ) / 8 * (gammaThirdProduct 320 : ℝ) ^ 3 / (320 + 2/3) <
        (167977 / 100000 : ℝ) ^ 3 := by
      have h := (Rat.cast_lt (K := ℝ)).2 gammaThird_upper_numeric
      push_cast at h
      exact h
    convert h using 1
    norm_num
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 1.67976) hpos (by omega : 3 ≠ 0)).mp
    rw [hc]
    exact hlo.trans_le (mul_le_mul_of_nonneg_left hbr.1 (by norm_num))
  · apply (pow_lt_pow_iff_left₀ hpos (by norm_num : (0:ℝ) ≤ 1.67977) (by omega : 3 ≠ 0)).mp
    rw [hc]
    exact (mul_le_mul_of_nonneg_left hbr.2 (by norm_num : (0:ℝ) ≤ 27/8)).trans_lt hhi

end MatrixMultiplication
