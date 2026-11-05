module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Ring

/-!
# Exponential capacity and root growth

If ranks with root growth `q > 1` fit into capacities `a ^ m`, and every such
fit forces `q ^ n ≤ p ^ m`, then the growth per capacity unit satisfies `a ≤ p`.
The proof rounds logarithms to natural exponents, keeping every size integral.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped Topology

/-- Comparing integer capacities with a sequence's root growth gives a lower
bound on the capacity rate. The rounded logarithm contributes an error that
vanishes after division by the sequence index. -/
theorem le_of_root_limit_capacity {r : ℕ → ℕ} {a : ℕ} {q p : ℝ}
    (ha : 1 < a) (hq : 1 < q) (hp : 1 ≤ p)
    (hr : ∀ n, 1 ≤ r n)
    (hlim : Tendsto (fun n : ℕ => (r n : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 q))
    (hcapacity : ∀ n m : ℕ, r n ≤ a ^ m → q ^ n ≤ p ^ m) :
    (a : ℝ) ≤ p := by
  have har : (1 : ℝ) < a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := zero_lt_one.trans har
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hppos : 0 < p := zero_lt_one.trans_le hp
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos har
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper := ((hlim.log hqpos.ne').div_const (Real.log (a : ℝ))).add hinv
  have hupper := hupper.mul_const (Real.log p)
  simp only [add_zero] at hupper
  have hlimbound : Real.log q ≤ Real.log q / Real.log (a : ℝ) * Real.log p := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hupper
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hrpos : 0 < (r n : ℝ) := by exact_mod_cast hr n
    have hcompare := hcapacity n (Nat.clog a (r n)) (Nat.le_pow_clog ha (r n))
    have hlog := Real.log_le_log (pow_pos hqpos n) hcompare
    simp only [Real.log_pow] at hlog
    have hceil : (Nat.clog a (r n) : ℝ) ≤ Real.logb a (r n) + 1 := by
      rw [← Real.natCeil_logb_natCast]
      exact (Nat.ceil_lt_add_one
        (Real.logb_nonneg har (by exact_mod_cast hr n))).le
    have hmul := mul_le_mul_of_nonneg_right hceil (Real.log_nonneg hp)
    have hscaled := mul_le_mul_of_nonneg_left (hlog.trans hmul) (inv_nonneg.mpr hnpos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul] at hscaled
    calc
      Real.log q ≤ (n : ℝ)⁻¹ * ((Real.logb a (r n) + 1) * Real.log p) := hscaled
      _ = (Real.log ((r n : ℝ) ^ (n : ℝ)⁻¹) / Real.log (a : ℝ) +
          (n : ℝ)⁻¹) * Real.log p := by
        rw [Real.log_rpow hrpos, Real.logb]
        ring
  have hmul := mul_le_mul_of_nonneg_right hlimbound hloga.le
  rw [mul_right_comm (Real.log q / Real.log (a : ℝ)) (Real.log p),
    div_mul_cancel₀ _ hloga.ne'] at hmul
  have hlogs : Real.log (a : ℝ) ≤ Real.log p := (mul_le_mul_iff_right₀ hlogq).mp hmul
  exact (Real.log_le_log_iff hapos hppos).mp hlogs

end MatrixMultiplication
