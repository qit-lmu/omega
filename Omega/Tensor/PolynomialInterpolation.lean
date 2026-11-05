module

public import Omega.Tensor.PolynomialRank
public import Omega.Tensor.RankOperations
public import Mathlib.Data.Fintype.BigOperators

/-!
# Polynomial multiplication by interpolation at infinity

For positive input sizes, `a+b-2` distinct finite nodes together with the
leading coefficient (evaluation at infinity) give `a+b-1` pure summands.
This establishes the sharp field-size threshold in Lemma 2.6.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {K : Type*} [Field K]

private theorem pow_eq_interpolate_add_top (d : ℕ) (v : Fin d → K)
    (hv : Function.Injective v) (n : ℕ) (hn : n ≤ d) :
    (X ^ n : K[X]) = Lagrange.interpolate Finset.univ v (fun t => v t ^ n) +
      if n = d then X ^ d - Lagrange.interpolate Finset.univ v (fun t => v t ^ d)
        else 0 := by
  by_cases hnd : n = d
  · subst n
    simp
  · rw [ite_eq_right hnd, add_zero]
    have hdeg : (X ^ n : K[X]).degree <
        (Finset.univ : Finset (Fin d)).card := by
      rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast (lt_of_le_of_ne hn hnd)
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      Lagrange.eq_interpolate (s := Finset.univ) (v := v)
        (f := (X ^ n : K[X])) (fun _ _ _ _ h => hv h) hdeg

/-- The sharp interpolation upper bound uses one extra summand for the
leading coefficient, in addition to the `a+b-2` finite evaluations. -/
theorem rank_polynomialMul_le_of_nodes_atInfinity (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (v : Fin (a + b - 2) → K) (hv : Function.Injective v) :
    rank (polynomialMul K a b) ≤ a + b - 1 := by
  classical
  let d := a + b - 2
  let P : K[X] := X ^ d - Lagrange.interpolate Finset.univ v (fun t => v t ^ d)
  let x : Option (Fin d) → Fin a → K
    | none, i => if i.val = a - 1 then 1 else 0
    | some t, i => v t ^ i.val
  let y : Option (Fin d) → Fin b → K
    | none, j => if j.val = b - 1 then 1 else 0
    | some t, j => v t ^ j.val
  let z : Option (Fin d) → Fin (a + b - 1) → K
    | none, k => P.coeff k.val
    | some t, k => (Lagrange.basis Finset.univ v t).coeff k.val
  have hdecomp : polynomialMul K a b = ∑ t, pure (x t) (y t) (z t) := by
    funext i j k
    have hn : i.val + j.val ≤ d := by dsimp [d]; omega
    have hi := congrArg (fun f : K[X] => f.coeff k.val)
      (pow_eq_interpolate_add_top d v hv (i.val + j.val) hn)
    have hend : i.val + j.val = d ↔ i.val = a - 1 ∧ j.val = b - 1 := by
      dsimp [d]
      omega
    simp only [Finset.sum_apply, Fintype.sum_option, pure, x, y, z]
    change (if i.val + j.val = k.val then 1 else 0) = _
    by_cases htop : i.val + j.val = d
    · rw [ite_eq_left htop] at hi
      obtain ⟨hi', hj'⟩ := hend.mp htop
      rw [ite_eq_left hi', ite_eq_left hj', one_mul, one_mul]
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow] at hi
      simpa only [
        Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        P, pow_add, eq_comm, add_comm] using hi
    · rw [ite_eq_right htop, add_zero] at hi
      have hzero : ((if i.val = a - 1 then 1 else 0) *
          (if j.val = b - 1 then 1 else 0) : K) = 0 := by
        by_cases hi' : i.val = a - 1
        · have hj' : j.val ≠ b - 1 := fun hj' => htop (hend.mpr ⟨hi', hj'⟩)
          simp [hi', hj']
        · simp [hi']
      rw [hzero, zero_mul, zero_add]
      simp only [Polynomial.coeff_X_pow] at hi
      simpa only [Lagrange.interpolate_apply,
        Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, pow_add, eq_comm] using hi
  rw [hdecomp]
  have h := rank_le_of_sum_pure x y z
  simpa only [Fintype.card_option, Fintype.card_fin,
    show d + 1 = a + b - 1 by dsimp [d]; omega] using h

/-- Ordinary polynomial-multiplication rank with enough finite nodes,
including the additional evaluation at infinity. -/
theorem rank_polynomialMul_of_nodes_atInfinity (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (v : Fin (a + b - 2) → K) (hv : Function.Injective v) :
    rank (polynomialMul K a b) = a + b - 1 :=
  le_antisymm (rank_polynomialMul_le_of_nodes_atInfinity a b ha hb v hv)
    (add_sub_one_le_rank_polynomialMul a b ha hb)

/-- The ordinary-rank identity over any field with at least `a+b-2`
elements, expressed without assuming that the field is finite. -/
theorem rank_polynomialMul_of_card (K : Type*) [Field K] (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hcard : Nonempty (Fin (a + b - 2) ↪ K)) :
    rank (polynomialMul K a b) = a + b - 1 := by
  obtain ⟨v⟩ := hcard
  exact rank_polynomialMul_of_nodes_atInfinity a b ha hb v v.injective

end MatrixMultiplication.Tensor
