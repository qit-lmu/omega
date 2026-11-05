module

public import Omega.Analysis.Entropy
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Entropy as the exponential growth rate of multinomial coefficients

Stirling's formula implies that the normalized logarithm of a multinomial
coefficient tends to the entropy of its proportions. Counts equal to zero
are allowed throughout.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication

open Filter
open scoped Topology BigOperators

private def factorialLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log n + n

private theorem factorialLogError_div_tendsto_zero :
    Tendsto (fun n : ℕ => factorialLogError n / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hn
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have h := hs.add ((hc.add hl).const_mul (1 / 2 : ℝ))
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) hn', Real.log_div hn' (Real.exp_ne_zero _),
    Real.log_exp] at he
  dsimp only [factorialLogError]
  dsimp only [Function.id_def, Function.comp_def]
  rw [he]
  ring

private theorem factorialLogError_mul_div_tendsto_zero (c : ℕ) :
    Tendsto (fun n : ℕ => factorialLogError (n * c) / n) atTop (𝓝 0) := by
  by_cases hc : c = 0
  · simp [hc, factorialLogError]
  have hc' : 0 < c := Nat.pos_of_ne_zero hc
  have ht : Tendsto (fun n : ℕ => n * c) atTop atTop :=
    tendsto_id.atTop_mul_const' hc'
  have h := (factorialLogError_div_tendsto_zero.comp ht).mul_const (c : ℝ)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc'' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  dsimp only [Function.comp_def]
  simp only [Nat.cast_mul]
  field_simp

private theorem log_factorial_mul_regularized_tendsto (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((n * c).factorial : ℝ) / n -
      (c : ℝ) * Real.log n) atTop (𝓝 ((c : ℝ) * Real.log c - c)) := by
  by_cases hc : c = 0
  · simp [hc]
  have h := (factorialLogError_mul_div_tendsto_zero c).add_const
    ((c : ℝ) * Real.log c - c)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  dsimp only [factorialLogError]
  rw [Nat.cast_mul, Real.log_mul hn' hc']
  field_simp
  ring

private theorem log_multinomial_eq {H : Type*} [Fintype H] (c : H → ℕ) :
    Real.log (Nat.multinomial Finset.univ c : ℝ) =
      Real.log ((∑ h, c h).factorial : ℝ) - ∑ h, Real.log ((c h).factorial : ℝ) := by
  classical
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ))
    (Nat.multinomial_spec Finset.univ c)
  simp only [Nat.cast_mul, Nat.cast_prod] at h
  rw [Real.log_mul (by positivity) (by
    exact_mod_cast (Nat.multinomial_pos (s := Finset.univ) (f := c)).ne'), Real.log_prod (by
    intro h _
    positivity)] at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h)

/-- The natural logarithmic growth rate of multinomial coefficients with
fixed integer proportions. Zero counts are included. -/
theorem multinomial_log_div_tendsto {H : Type*} [Fintype H] (c : H → ℕ) :
    Tendsto (fun n : ℕ => Real.log
      (Nat.multinomial Finset.univ (fun h => n * c h) : ℝ) / n)
      atTop (𝓝 (((∑ h, c h : ℕ) : ℝ) * Real.log (∑ h, c h : ℕ) -
        ∑ h, (c h : ℝ) * Real.log (c h))) := by
  classical
  have hsum := tendsto_finsetSum Finset.univ
    (fun h _ => log_factorial_mul_regularized_tendsto (c h))
  have ht := (log_factorial_mul_regularized_tendsto (∑ h, c h)).sub hsum
  convert ht using 1
  · funext n
    rw [log_multinomial_eq, ← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul,
      ← Nat.cast_sum]
    ring
  · congr 1
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum]
    ring

/-- The natural logarithmic form of the entropy of normalized integer counts. -/
theorem log_two_mul_entropy_natCounts {H : Type*} [Fintype H]
    (c : H → ℕ) (hc : 0 < ∑ h, c h) :
    Real.log 2 * entropy (fun h => (c h : ℝ) / (∑ h, c h : ℕ)) =
      (((∑ h, c h : ℕ) : ℝ) * Real.log (∑ h, c h : ℕ) -
        ∑ h, (c h : ℝ) * Real.log (c h)) / (∑ h, c h : ℕ) := by
  classical
  let K := ∑ h, c h
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hterm (h : H) : (c h : ℝ) / K * Real.log ((c h : ℝ) / K) =
      ((c h : ℝ) * Real.log (c h) - (c h : ℝ) * Real.log K) / K := by
    by_cases hz : c h = 0
    · simp [hz]
    have hz' : (c h : ℝ) ≠ 0 := by exact_mod_cast hz
    rw [Real.log_div hz' hK]
    ring
  change Real.log 2 * (-(∑ h, (c h : ℝ) / K *
      Real.log ((c h : ℝ) / K)) / Real.log 2) = _
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum]
  change Real.log 2 * (-(((∑ h, (c h : ℝ) * Real.log (c h)) -
      (K : ℝ) * Real.log K) / K) / Real.log 2) = _
  field_simp
  ring

/-- The multinomial entropy limit, including zero symbol counts. If `K` is
the positive sum of the counts, the `(n*K)`th root converges to two raised
to the entropy of the proportions `c/K`. -/
theorem multinomial_root_tendsto_entropy {H : Type*} [Fintype H]
    (c : H → ℕ) (hc : 0 < ∑ h, c h) :
    Tendsto (fun n : ℕ =>
      (Nat.multinomial Finset.univ (fun h => n * c h) : ℝ) ^
        (1 / ((n : ℝ) * (∑ h, c h : ℕ))))
      atTop (𝓝 ((2 : ℝ) ^ entropy (fun h => (c h : ℝ) / (∑ h, c h : ℕ)))) := by
  classical
  have h := ((multinomial_log_div_tendsto c).div_const
    ((∑ h, c h : ℕ) : ℝ)).rexp
  rw [← log_two_mul_entropy_natCounts c hc] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  convert h using 1
  funext n
  have hm : (0 : ℝ) < Nat.multinomial Finset.univ (fun h => n * c h) := by
    exact_mod_cast Nat.multinomial_pos Finset.univ (fun h => n * c h)
  rw [Real.rpow_def_of_pos hm]
  congr 1
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

end MatrixMultiplication
