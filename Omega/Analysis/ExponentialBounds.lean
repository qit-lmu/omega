module

public import Omega.Analysis.RankGrowth
import Mathlib.Tactic.Linarith

/-!
# Uniform exponential bounds from root limits

A rate strictly larger than the limit of the nth roots bounds the entire
sequence after multiplication by one fixed positive constant. Conversely,
a fixed positive factor does not affect an exponential upper bound.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped Topology

/-- A nonnegative sequence whose roots converge admits a uniform exponential
bound at every positive rate strictly larger than its root limit. -/
theorem exists_pos_exponential_bound {u : ℕ → ℝ} {L r : ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto (fun n : ℕ => u n ^ (n : ℝ)⁻¹) atTop (𝓝 L))
    (hr : 0 < r) (hL : L < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, u n ≤ C * r ^ n := by
  have hevent : ∀ᶠ n : ℕ in atTop, u n ≤ r ^ n := by
    filter_upwards [hlim.eventually (gt_mem_nhds hL), eventually_ge_atTop (1 : ℕ)]
      with n hn hnpos
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (hu n) _) hn.le n
    rwa [Real.rpow_inv_natCast_pow (hu n) (by omega : n ≠ 0)] at hpow
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, u i / r ^ i
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, u i / r ^ i :=
    Finset.sum_nonneg fun i _ => div_nonneg (hu i) (pow_nonneg hr.le i)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_nonneg hr.le n) hC)
  · have hs : u n / r ^ n ≤ ∑ i ∈ Finset.range N, u i / r ^ i :=
      Finset.single_le_sum (fun i _ => div_nonneg (hu i) (pow_nonneg hr.le i))
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hr n)).mp
    dsimp [C]
    linarith

/-- A constant factor in an exponential bound disappears under nth roots. -/
theorem root_limit_le_of_exponential_bound {u : ℕ → ℝ} {L C r : ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto (fun n : ℕ => u n ^ (n : ℝ)⁻¹) atTop (𝓝 L))
    (hC : 0 < C) (hr : 0 ≤ r)
    (hbound : ∀ n, u n ≤ C * r ^ n) : L ≤ r := by
  have hconst : Tendsto (fun n : ℕ => C ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow (a := C) (b := 0) hC.ne').tendsto.comp
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hupper := hconst.mul_const r
  simp only [one_mul] at hupper
  apply le_of_tendsto_of_tendsto hlim hupper
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := Real.rpow_le_rpow (hu n) (hbound n)
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.mul_rpow hC.le (pow_nonneg hr n),
    Real.pow_rpow_inv_natCast hr (by omega : n ≠ 0)] at h

end MatrixMultiplication
