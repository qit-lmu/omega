module

public import Omega.ValueScore
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Scores after scaling matrix-block parameters

Multiplying the numerator or denominator parameters by `r^N` and `q^N`
changes the score by the factor `r^(1/6) * q^(tau/2)`. These numerical
identities are independent of how the corresponding witnesses are built.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

private theorem log_nat_mul_pow {a r : ℕ} (ha : 1 ≤ a) (hr : 1 ≤ r) (N : ℕ) :
    Real.log ((a * r ^ N : ℕ) : ℝ) =
      Real.log (a : ℝ) + (N : ℝ) * Real.log (r : ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp ha)
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hr)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul ha' (pow_ne_zero _ hr'), Real.log_pow]

/-- Scaling the denominator block parameters divides a witness score by the
sixth-root block count and the corresponding matrix-size power. -/
theorem ValueWitness.score_mul_of_denominator_scale
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness T) (v : ValueWitness S) (r q : ℕ)
    (hr : 1 ≤ r) (hq : 1 ≤ q)
    (ha : v.a = w.a) (hb : v.b = w.b)
    (hc : v.c = w.c * r ^ w.N) (hd : v.d = w.d * q ^ w.N) (hN : v.N = w.N)
    (τ : ℝ) :
    v.score τ * ((r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2)) = w.score τ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hr
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hq
  have hfactor := mul_pos (Real.rpow_pos_of_pos hrpos (1 / 6 : ℝ))
    (Real.rpow_pos_of_pos hqpos (τ / 2))
  apply Real.log_injOn_pos (mul_pos (v.score_pos τ) hfactor) (w.score_pos τ)
  rw [Real.log_mul (v.score_pos τ).ne' hfactor.ne',
    Real.log_mul (Real.rpow_pos_of_pos hrpos (1 / 6 : ℝ)).ne'
      (Real.rpow_pos_of_pos hqpos (τ / 2)).ne',
    Real.log_rpow hrpos, Real.log_rpow hqpos]
  simp only [ValueWitness.log_score, ha, hb, hc, hd, hN]
  rw [log_nat_mul_pow w.hc hr, log_nat_mul_pow w.hd hq]
  have hN' : (w.N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp w.hN)
  field_simp
  ring

/-- Scaling the numerator block parameters multiplies a witness score by the
sixth-root block count and the corresponding matrix-size power. -/
theorem ValueWitness.score_of_numerator_scale
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness T) (v : ValueWitness S) (r q : ℕ)
    (hr : 1 ≤ r) (hq : 1 ≤ q)
    (ha : v.a = w.a * r ^ w.N) (hb : v.b = w.b * q ^ w.N)
    (hc : v.c = w.c) (hd : v.d = w.d) (hN : v.N = w.N)
    (τ : ℝ) :
    v.score τ = ((r : ℝ) ^ (1 / 6 : ℝ) * (q : ℝ) ^ (τ / 2)) * w.score τ := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hr
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hq
  have hfactor := mul_pos (Real.rpow_pos_of_pos hrpos (1 / 6 : ℝ))
    (Real.rpow_pos_of_pos hqpos (τ / 2))
  apply Real.log_injOn_pos (v.score_pos τ) (mul_pos hfactor (w.score_pos τ))
  rw [Real.log_mul hfactor.ne' (w.score_pos τ).ne',
    Real.log_mul (Real.rpow_pos_of_pos hrpos (1 / 6 : ℝ)).ne'
      (Real.rpow_pos_of_pos hqpos (τ / 2)).ne',
    Real.log_rpow hrpos, Real.log_rpow hqpos]
  simp only [ValueWitness.log_score, ha, hb, hc, hd, hN]
  rw [log_nat_mul_pow w.ha hr, log_nat_mul_pow w.hb hq]
  have hN' : (w.N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp w.hN)
  field_simp
  ring

end MatrixMultiplication.Tensor
