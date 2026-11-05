module

public import Omega.Tensor.RationalDegeneration
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial multiplication is a degeneration of a diagonal tensor

Evaluation and Lagrange interpolation give a restriction from a diagonal
tensor whenever there are enough distinct interpolation nodes. Over the
rational function field, distinct powers of the formal parameter provide
such nodes over every base field. The output is the constant polynomial
multiplication tensor, so the rational restriction is a degeneration over
the original field.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

/-- Evaluation at distinct nodes and coefficient extraction from their
Lagrange basis polynomials compute polynomial multiplication. -/
theorem diagonal_restricts_polynomialMul_of_nodes
    {F : Type*} [Field F] (a b : ℕ)
    (v : Fin (a + b - 1) → F) (hv : Function.Injective v) :
    Restricts (diagonal F (a + b - 1)) (polynomialMul F a b) := by
  classical
  refine ⟨Matrix.of (fun i t => v t ^ i.val), Matrix.of (fun j t => v t ^ j.val),
    Matrix.of (fun k t => (Lagrange.basis Finset.univ v t).coeff k.val), ?_⟩
  rw [map_diagonal]
  funext i j k
  have hdeg : (X ^ (i.val + j.val) : F[X]).degree <
      (Finset.univ : Finset (Fin (a + b - 1))).card := by
    have hij : i.val + j.val < a + b - 1 := by omega
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hij
  have hi := Lagrange.eq_interpolate (s := Finset.univ)
    (f := (X ^ (i.val + j.val) : F[X])) (fun _ _ _ _ h => hv h) hdeg
  have hc := congrArg (fun p : F[X] => p.coeff k.val) hi
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow] at hc
  simpa only [Matrix.of_apply, pow_add, polynomialMul, eq_comm] using hc.symm

private theorem rational_parameter_powers_injective (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (fun i : Fin n =>
      algebraMap K[X] (RatFunc K) ((X : K[X]) ^ i.val)) := by
  intro i j h
  apply Fin.ext
  have hp := (RatFunc.algebraMap_injective K) h
  simpa only [Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree hp

/-- Polynomial multiplication with output size `a+b-1` is a degeneration
of the diagonal of that size, uniformly over every field. Empty input
coordinate sets are included as well. -/
theorem diagonal_degenerates_polynomialMul (K : Type*) [Field K] (a b : ℕ) :
    Degenerates (diagonal K (a + b - 1)) (polynomialMul K a b) := by
  apply RationalDegenerates.degenerates
  obtain ⟨A, B, D, h⟩ := diagonal_restricts_polynomialMul_of_nodes a b
    (fun i => algebraMap K[X] (RatFunc K) ((X : K[X]) ^ i.val))
    (rational_parameter_powers_injective K _)
  refine ⟨A, B, D, ?_⟩
  have hlift : liftRational (diagonal K (a + b - 1)) =
      diagonal (RatFunc K) (a + b - 1) := by
    funext i j k
    simp [liftRational, diagonal]
  intro i j k
  rw [hlift, h]
  by_cases hij : i.val + j.val = k.val <;>
    simp [polynomialMul, RegularAtZeroValue, hij]

end MatrixMultiplication.Tensor
