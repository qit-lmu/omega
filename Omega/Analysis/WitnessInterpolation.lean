module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds for intermediate fractional-value witnesses

After division by the positive denominator, a witness ratio is a positive
constant times `(b / d) ^ t`. It is monotone in `t`, in one direction or the
other according to whether `b / d` is above or below one. Thus its endpoint
bounds control every intermediate exponent, including a degenerate interval.
-/

@[expose] public section

namespace MatrixMultiplication

private theorem witness_ratio_eq {a b c d t : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (a * b ^ t) / (c * d ^ t) = (a / c) * (b / d) ^ t := by
  rw [Real.div_rpow hb.le hd.le, div_mul_div_comm]

/-- A ratio of positive exponential functions is bounded by its endpoint
bounds on every closed exponent interval. -/
theorem witness_ratio_le_of_endpoint_bounds {a b c d l t u X : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hlt : l ≤ t) (htu : t ≤ u)
    (hl : a * b ^ l ≤ c * d ^ l * X)
    (hu : a * b ^ u ≤ c * d ^ u * X) :
    (a * b ^ t) / (c * d ^ t) ≤ X := by
  have hl' : (a * b ^ l) / (c * d ^ l) ≤ X := by
    apply (div_le_iff₀ (mul_pos hc (Real.rpow_pos_of_pos hd l))).mpr
    simpa only [mul_comm] using hl
  have hu' : (a * b ^ u) / (c * d ^ u) ≤ X := by
    apply (div_le_iff₀ (mul_pos hc (Real.rpow_pos_of_pos hd u))).mpr
    simpa only [mul_comm] using hu
  rw [witness_ratio_eq hb hd] at hl' hu' ⊢
  rcases le_total b d with hbd | hdb
  · have hpow := Real.rpow_le_rpow_of_exponent_ge (div_pos hb hd)
      ((div_le_one hd).mpr hbd) hlt
    exact (mul_le_mul_of_nonneg_left hpow (div_nonneg ha.le hc.le)).trans hl'
  · have hpow := Real.rpow_le_rpow_of_exponent_le ((one_le_div hd).mpr hdb) htu
    exact (mul_le_mul_of_nonneg_left hpow (div_nonneg ha.le hc.le)).trans hu'

/-- A multiplicative witness bound gives the corresponding root bound. No
strict positivity of the right-hand rate is needed. -/
theorem witness_root_le_of_bound {a b c d t R : ℝ} {k : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 < k) (hR : 0 ≤ R)
    (hbound : a * b ^ t ≤ c * d ^ t * R ^ k) :
    ((a * b ^ t) / (c * d ^ t)) ^ (k : ℝ)⁻¹ ≤ R := by
  have hden := mul_pos hc (Real.rpow_pos_of_pos hd t)
  have hratio : (a * b ^ t) / (c * d ^ t) ≤ R ^ k := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hbound
  have hroot := Real.rpow_le_rpow
    (div_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hb.le t)) hden.le)
    hratio (inv_nonneg.mpr (Nat.cast_nonneg k))
  rwa [Real.pow_rpow_inv_natCast hR (Nat.ne_of_gt hk)] at hroot

/-- The quadratic and exponent-`w` witness bounds control every exponent
between two and `w`, after taking the positive natural root. -/
theorem witness_root_le_of_endpoint_bounds {a b c d w t R : ℝ} {k : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 < k) (hR : 0 ≤ R) (ht : 2 ≤ t) (htw : t ≤ w)
    (h₂ : a * b ^ (2 : ℕ) ≤ c * d ^ (2 : ℕ) * R ^ k)
    (hw : a * b ^ w ≤ c * d ^ w * R ^ k) :
    ((a * b ^ t) / (c * d ^ t)) ^ (k : ℝ)⁻¹ ≤ R := by
  have hratio := witness_ratio_le_of_endpoint_bounds ha hb hc hd ht htw
    (by simpa only [Real.rpow_two] using h₂) hw
  have hroot := Real.rpow_le_rpow
    (div_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hb.le t))
      (mul_nonneg hc.le (Real.rpow_nonneg hd.le t)))
    hratio (inv_nonneg.mpr (Nat.cast_nonneg k))
  rwa [Real.pow_rpow_inv_natCast hR (Nat.ne_of_gt hk)] at hroot

end MatrixMultiplication
