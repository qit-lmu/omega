module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The size of the sharp square matrix multiplication subrank construction

The natural-number formula used to count the construction agrees with the
ceiling in the manuscript, including the zero-dimensional case.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The integral size of the sharp construction equals its real ceiling formula. -/
theorem sharpSubrankSize_eq_natCeil (n : ℕ) :
    (3 * n ^ 2 + 3) / 4 = ⌈(3 : ℝ) * (n : ℝ) ^ 2 / 4⌉₊ := by
  apply Nat.le_antisymm
  · have h := Nat.le_ceil ((3 : ℝ) * (n : ℝ) ^ 2 / 4)
    have h' : 3 * n ^ 2 ≤ ⌈(3 : ℝ) * (n : ℝ) ^ 2 / 4⌉₊ * 4 := by
      exact_mod_cast (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h
    omega
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have h : 3 * n ^ 2 ≤ (3 * n ^ 2 + 3) / 4 * 4 := by omega
    exact_mod_cast h

/-- Removing the two complementary triangles gives the sharp subrank size. -/
theorem square_sub_half_mul_half_eq_sharpSubrankSize (n : ℕ) :
    n ^ 2 - (n / 2) * ((n + 1) / 2) = (3 * n ^ 2 + 3) / 4 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h₁ : (k + k) / 2 = k := by omega
    have h₂ : (k + k + 1) / 2 = k := by omega
    rw [h₁, h₂]
    ring_nf
    omega
  · have h₁ : (2 * k + 1) / 2 = k := by omega
    have h₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h₁, h₂]
    ring_nf
    omega

end MatrixMultiplication
