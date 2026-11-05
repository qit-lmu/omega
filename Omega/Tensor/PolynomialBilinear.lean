module

public import Omega.Tensor.Examples
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Polynomial multiplication as a coefficient tensor

The finite coefficient-vector formula for `polynomialMul` computes the
coefficients of ordinary polynomial multiplication.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

open Polynomial

/-- Convert a finite coefficient vector to a polynomial of bounded degree. -/
noncomputable def coefficientPolynomial {R : Type*} [Semiring R] {n : ℕ} (x : Fin n → R) : R[X] :=
  ∑ i, monomial i.val (x i)

/-- The tensor coefficients compute multiplication of coefficient polynomials. -/
theorem polynomialMul_bilinear {R : Type*} [CommSemiring R] {a b : ℕ}
    (x : Fin a → R) (y : Fin b → R) (k : Fin (a + b - 1)) :
    (coefficientPolynomial x * coefficientPolynomial y).coeff k.val =
      ∑ i, ∑ j, x i * y j * polynomialMul R a b i j k := by
  simp [coefficientPolynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.finsetSum_coeff, Polynomial.monomial_mul_monomial,
    Polynomial.coeff_monomial, polynomialMul, mul_ite]
  exact Finset.sum_comm

end MatrixMultiplication.Tensor
