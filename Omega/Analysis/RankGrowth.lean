module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity

/-!
# Polynomial overhead in asymptotic rank

A polynomial factor does not change the exponential growth rate of a
nonnegative submultiplicative sequence. This is the analytic step in the
coefficient-extraction proof of degeneration monotonicity.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped Topology

/-- The nth root of a positive affine function of n tends to one. -/
theorem affine_root_tendsto_one (d : ℕ) :
    Tendsto (fun n : ℕ => ((d : ℝ) * n + 1) ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
  by_cases hd : d = 0
  · simp [hd]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hlin : Tendsto (fun n : ℕ => (d : ℝ) * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop.const_mul_atTop hdpos)
  have h := (tendsto_rpow_div_mul_add (d : ℝ) 1 (-1) zero_ne_one).comp hlin
  convert h using 1
  funext n
  congr 1
  simp only [one_mul, add_neg_cancel_right]
  rw [div_mul_eq_div_div, div_self (ne_of_gt hdpos), one_div]

/-- Any fixed polynomial overhead of the form `(d*n+1)^k` disappears
after taking nth roots. -/
theorem polynomial_overhead_root_tendsto_one (d k : ℕ) :
    Tendsto (fun n : ℕ => (((d : ℝ) * n + 1) ^ k) ^ (n : ℝ)⁻¹)
      atTop (𝓝 1) := by
  have h := (affine_root_tendsto_one d).pow k
  simp only [one_pow] at h
  convert h using 1
  funext n
  rw [← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  exact mul_comm _ _

/-- Polynomial overhead cannot increase the limit of nth roots of
nonnegative submultiplicative sequences. -/
theorem submultiplicative_limit_le_of_polynomial_bound
    {u v : ℕ → ℝ} (hu : Submultiplicative u) (hv : Submultiplicative v)
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (d k : ℕ)
    (hbound : ∀ n : ℕ, 1 ≤ n → v n ≤ ((d : ℝ) * n + 1) ^ k * u n) :
    hv.lim ≤ hu.lim := by
  have hupper := (polynomial_overhead_root_tendsto_one d k).mul (hu.tendsto_lim hu0)
  simp only [one_mul] at hupper
  apply le_of_tendsto_of_tendsto (hv.tendsto_lim hv0) hupper
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := Real.rpow_le_rpow (hv0 n) (hbound n hn)
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.mul_rpow (by positivity) (hu0 n)] at h

end MatrixMultiplication
