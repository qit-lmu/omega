module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monotone functions that preserve natural powers

Comparing powers of two integer bases using the ceiling logarithm shows that
a monotone function preserving powers must itself be a real power function
on the positive integers.
-/

@[expose] public section

namespace MatrixMultiplication

private theorem le_of_nat_mul_le_add {x y c : ℝ}
    (h : ∀ k : ℕ, k * x ≤ k * y + c) : x ≤ y := by
  by_contra hxy
  have hpos : 0 < x - y := sub_pos.mpr (lt_of_not_ge hxy)
  obtain ⟨k, hk⟩ := exists_nat_gt (c / (x - y))
  have hk' := (div_lt_iff₀ hpos).mp hk
  have := h k
  nlinarith

/-- Comparing rounded powers bounds the logarithmic growth between two bases. -/
theorem log_le_logb_mul_of_monotone_pow (f : ℕ → ℝ)
    (hmono : Monotone f) (hone : f 1 = 1)
    (hpow : ∀ a k : ℕ, f (a ^ k) = f a ^ k)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 < b) :
    Real.log (f a) ≤ Real.logb b a * Real.log (f b) := by
  have hfa : 0 < f a := lt_of_lt_of_le zero_lt_one (hone ▸ hmono ha)
  have hfb : 1 ≤ f b := hone ▸ hmono (Nat.le_of_lt hb)
  have hbr : (1 : ℝ) < b := by exact_mod_cast hb
  apply le_of_nat_mul_le_add (c := Real.log (f b))
  intro k
  have hcompare := hmono (Nat.le_pow_clog hb (a ^ k))
  rw [hpow, hpow] at hcompare
  have hlog := Real.log_le_log (pow_pos hfa k) hcompare
  simp only [Real.log_pow] at hlog
  have hceil : (Nat.clog b (a ^ k) : ℝ) ≤ k * Real.logb b a + 1 := by
    rw [← Real.natCeil_logb_natCast]
    have hnonneg : 0 ≤ Real.logb (b : ℝ) ((a ^ k : ℕ) : ℝ) :=
      Real.logb_nonneg hbr (by exact_mod_cast Nat.one_le_pow k a ha)
    have h := (Nat.ceil_lt_add_one hnonneg).le
    simpa only [Nat.cast_pow, Real.logb_pow] using h
  have hmul := mul_le_mul_of_nonneg_right hceil (Real.log_nonneg hfb)
  nlinarith

/-- Every monotone, unit-preserving function on natural numbers that preserves
powers equals a real power function at every positive integer. -/
theorem eq_rpow_logb_of_monotone_pow (f : ℕ → ℝ)
    (hmono : Monotone f) (hone : f 1 = 1)
    (hpow : ∀ a k : ℕ, f (a ^ k) = f a ^ k)
    (n : ℕ) (hn : 1 ≤ n) :
    f n = (n : ℝ) ^ Real.logb 2 (f 2) := by
  rcases eq_or_lt_of_le hn with hn | hn
  · subst n
    simpa using hone
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans hnreal
  have hfn : 0 < f n := lt_of_lt_of_le zero_lt_one (hone ▸ hmono hn.le)
  have hlogn : 0 < Real.log n := Real.log_pos hnreal
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu := log_le_logb_mul_of_monotone_pow f hmono hone hpow hn.le (by decide : 1 < 2)
  have hl := log_le_logb_mul_of_monotone_pow f hmono hone hpow (by decide : 1 ≤ 2) hn
  norm_num only [Nat.cast_ofNat] at hu hl
  rw [Real.logb, div_mul_eq_mul_div] at hu hl
  have hu' := (le_div_iff₀ hlogtwo).mp hu
  have hl' := (le_div_iff₀ hlogn).mp hl
  have heq : Real.log (f n) = Real.logb 2 (f 2) * Real.log n := by
    rw [Real.logb, div_mul_eq_mul_div, eq_div_iff hlogtwo.ne']
    nlinarith
  apply Real.log_injOn_pos hfn (Real.rpow_pos_of_pos hnpos _)
  rw [Real.log_rpow hnpos]
  exact heq

end MatrixMultiplication
