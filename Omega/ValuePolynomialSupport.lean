module

public import Omega.ValuePartialSum
public import Omega.ValueScaling
public import Omega.Tensor.PolynomialOperations
import Mathlib.Tactic.Linarith

/-!
# Value identities for polynomial-multiplication degenerations

These lemmas express binary partial-sum superadditivity and rectangular
matrix scaling in the real-root form used by the numerical growth argument.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

universe u v

/-- Exchanging the last two factors preserves fractional value. -/
theorem fractionalValue_swapLastTwo {K : Type v} [Field K] {I J L : Type u}
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor K I J L) (τ : ℝ) :
    fractionalValue (swapLastTwo T) τ = fractionalValue T τ :=
  fractionalValue_permute .cycleTransposition T τ

/-- Polynomial multiplication has symmetric input-size dependence. -/
theorem polynomialMul_value_swap (K : Type*) [Field K] (a b : ℕ) (τ : ℝ) :
    fractionalValue (polynomialMul K a b) τ = fractionalValue (polynomialMul K b a) τ := by
  have he := equivalent_of_reindex _ _ _ (polynomialMul_swapFirstTwo (R := K) a b)
  rw [← fractionalValue_eq_of_equivalent he τ]
  exact (fractionalValue_permute .transposition (polynomialMul K a b) τ).symm

private theorem kronecker_comm_equivalent {K A B C D E F : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    (T : Tensor K A B C) (S : Tensor K D E F) :
    Equivalent (kronecker T S) (kronecker S T) := by
  apply equivalent_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  funext i j k
  simp [reindex, kronecker, mul_comm]

/-- Repeating polynomial multiplication in its two unshared factors scales
the root of value by the number of repetitions. -/
theorem polynomialMulCopies_value_root (K : Type*) [Field K] (a b r : ℕ) (hr : 1 ≤ r)
    {τ : ℝ} (hτ : (2 : ℝ) / 3 ≤ τ) (_hτω : τ ≤ omega K / 3) :
    (fractionalValue (polynomialMulCopies K a b r) τ).toReal ^ τ⁻¹ =
      (r : ℝ) * (fractionalValue (polynomialMul K a b) τ).toReal ^ τ⁻¹ := by
  have hτne : τ ≠ 0 := by linarith
  have he := (polynomialMulCopies_equivalent (R := K) a b r).trans
    (kronecker_comm_equivalent _ _)
  rw [fractionalValue_eq_of_equivalent he τ,
    fractionalValue_matrixMul_kronecker _ 1 1 r le_rfl le_rfl hr τ]
  simp only [one_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (Nat.cast_nonneg r)]
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg r) τ) ENNReal.toReal_nonneg,
    Real.rpow_rpow_inv (Nat.cast_nonneg r) hτne]

end MatrixMultiplication.Tensor
