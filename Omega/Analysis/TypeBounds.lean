module

public import Omega.Analysis.RankGrowth
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Positivity

/-!
# From finite-type bounds to a sum bound

The multinomial expansion and a polynomial bound on the number of types turn
uniform bounds for every type into a bound on the sum of the weights. No
positivity of individual weights or approximation of probability vectors is
needed.
-/

@[expose] public section

namespace MatrixMultiplication

open Filter
open scoped BigOperators Topology

/-- Fixed polynomial and positive constant factors do not affect comparison
of exponential growth rates. -/
theorem le_of_pow_le_polynomial_mul_pow {a b C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 < C) (d k : ℕ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      a ^ n ≤ ((d : ℝ) * n + 1) ^ k * C * b ^ n) : a ≤ b := by
  have hconst : Tendsto (fun n : ℕ => C ^ (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow (a := C) (b := 0) hC.ne').tendsto.comp
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hupper := ((polynomial_overhead_root_tendsto_one d k).mul hconst).mul_const b
  simp only [one_mul] at hupper
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hupper
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h := Real.rpow_le_rpow (pow_nonneg ha n) (hbound n hn)
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.mul_rpow (by positivity) (pow_nonneg hb n),
    Real.mul_rpow (by positivity) hC.le,
    Real.pow_rpow_inv_natCast ha hn0, Real.pow_rpow_inv_natCast hb hn0] at h

/-- A type of words of length `n` is determined by at most `card H` counts,
each between zero and `n`. -/
theorem card_piAntidiag_univ_le {H : Type*} [Fintype H] [DecidableEq H] (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset H) n).card ≤
      (n + 1) ^ Fintype.card H := by
  let f : (Finset.piAntidiag (Finset.univ : Finset H) n) → H → Fin (n + 1) :=
    fun k i => ⟨k.val i, Nat.lt_succ_of_le (by
      calc
        k.val i ≤ ∑ j, k.val j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
        _ = n := (Finset.mem_piAntidiag.mp k.property).1)⟩
  have hf : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  simpa using Fintype.card_le_of_injective f hf

/-- Uniform bounds on every multinomial term imply a bound on the sum of its
nonnegative weights, including when some weights or the entire family vanish. -/
theorem sum_le_of_multinomial_bounds {H : Type*} [Fintype H] [DecidableEq H]
    (a : H → ℝ) {B C : ℝ} (ha : ∀ h, 0 ≤ a h) (hB : 0 ≤ B) (hC : 0 < C)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ k : H → ℕ, (∑ h, k h) = N →
      (Nat.multinomial Finset.univ k : ℝ) * ∏ h, a h ^ k h ≤ C * B ^ N) :
    ∑ h, a h ≤ B := by
  apply le_of_pow_le_polynomial_mul_pow
    (Finset.sum_nonneg fun h _ => ha h) hB hC 1 (Fintype.card H)
  intro N hN
  simp only [Nat.cast_one, one_mul]
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  calc
    ∑ k ∈ Finset.piAntidiag Finset.univ N,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ h, a h ^ k h
      ≤ ∑ _k ∈ Finset.piAntidiag (Finset.univ : Finset H) N, C * B ^ N := by
        apply Finset.sum_le_sum
        intro k hk
        exact hbound N hN k (Finset.mem_piAntidiag.mp hk).1
    _ = ((Finset.piAntidiag (Finset.univ : Finset H) N).card : ℝ) * (C * B ^ N) := by
      simp
    _ ≤ ((N : ℝ) + 1) ^ Fintype.card H * (C * B ^ N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_piAntidiag_univ_le (H := H) N
    _ = ((N : ℝ) + 1) ^ Fintype.card H * C * B ^ N := by
      simp [mul_assoc]

end MatrixMultiplication
