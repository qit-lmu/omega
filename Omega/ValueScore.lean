module

public import Omega.FractionalValue
import Mathlib.Tactic.Ring

/-!
# Logarithms of fractional-value witness scores

All witness parameters are positive. Taking logarithms turns their scores
into a linear expression in the parameter logarithms, divided by `6*N`.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K I J L : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]

/-- The logarithm of a witness score is its normalized logarithmic ratio. -/
theorem ValueWitness.log_score {T : Tensor K I J L} (w : ValueWitness T) (τ : ℝ) :
    Real.log (w.score τ) =
      (Real.log (w.a : ℝ) + (3 * τ) * Real.log (w.b : ℝ) -
        (Real.log (w.c : ℝ) + (3 * τ) * Real.log (w.d : ℝ))) /
        (6 * (w.N : ℝ)) := by
  have ha : 0 < (w.a : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp w.ha
  have hb : 0 < (w.b : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp w.hb
  have hc : 0 < (w.c : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp w.hc
  have hd : 0 < (w.d : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp w.hd
  have hnum := mul_pos ha (Real.rpow_pos_of_pos hb (3 * τ))
  have hden := mul_pos hc (Real.rpow_pos_of_pos hd (3 * τ))
  unfold ValueWitness.score
  rw [Real.log_rpow (div_pos hnum hden), Real.log_div hnum.ne' hden.ne',
    Real.log_mul ha.ne' (Real.rpow_pos_of_pos hb (3 * τ)).ne',
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hd (3 * τ)).ne',
    Real.log_rpow hb, Real.log_rpow hd]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

end MatrixMultiplication.Tensor
