module

public import Omega.Tensor.PolynomialInterpolation
public import Omega.Tensor.ScalarExtensionRank
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Ordinary rank of polynomial multiplication over finite fields

A finite extension of degree `max 1 (Nat.clog q (a+b-2))` has enough
elements for interpolation at the finite nodes and at infinity. Rank descent
then gives the square-degree overhead in the polynomial-multiplication rank
lemma. The natural ceiling of
the real logarithm is proved equal to this discrete ceiling logarithm.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K] [Finite K]

/-- The finite-field rank bound, using the discrete ceiling logarithm. -/
theorem rank_polynomialMul_finiteField_le_clog (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    rank (polynomialMul K a b) ≤
      (a + b - 1) * (max 1 (Nat.clog (Nat.card K) (a + b - 2))) ^ 2 := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  let : CharP K p := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let d : ℕ := max 1 (Nat.clog (Nat.card K) (a + b - 2))
  let : NeZero d := ⟨by dsimp [d]; omega⟩
  let E := FiniteField.Extension K p d
  let : Fintype E := Fintype.ofFinite E
  have hcard : a + b - 2 ≤ Fintype.card E := by
    rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
    exact (Nat.clog_le_iff_le_pow (show 1 < Nat.card K from Finite.one_lt_card)).mp
      (le_max_right 1 _)
  have hemb : Nonempty (Fin (a + b - 2) ↪ E) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  have he := rank_polynomialMul_of_card (K := E) a b ha hb hemb
  have h := rank_le_extension_degree_sq_mul (K := K) E (polynomialMul K a b)
  rw [scalarExtension_polynomialMul, he, FiniteField.finrank_extension] at h
  simpa only [d, Nat.mul_comm] using h

/-- The ordinary-rank bound for polynomial multiplication, with the real logarithm
and ceiling. It holds for all finite fields, including those already large
enough for direct interpolation. -/
theorem rank_polynomialMul_finiteField_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    rank (polynomialMul K a b) ≤
      (a + b - 1) *
        (max 1 ⌈Real.logb (Nat.card K) ((a + b - 2 : ℕ) : ℝ)⌉₊) ^ 2 := by
  rw [Real.natCeil_logb_natCast]
  exact rank_polynomialMul_finiteField_le_clog a b ha hb

/-- The manuscript's bound over a field too small for direct interpolation.
Here the ceiling logarithm is positive, so the uniform bound needs no maximum. -/
theorem rank_polynomialMul_smallFiniteField_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsmall : Nat.card K < a + b - 2) :
    rank (polynomialMul K a b) ≤
      (a + b - 1) * ⌈Real.logb (Nat.card K) ((a + b - 2 : ℕ) : ℝ)⌉₊ ^ 2 := by
  rw [Real.natCeil_logb_natCast]
  have hcard : 1 < Nat.card K := Finite.one_lt_card
  have hclog : 1 ≤ Nat.clog (Nat.card K) (a + b - 2) :=
    Nat.succ_le_of_lt (Nat.clog_pos hcard (lt_trans hcard hsmall))
  simpa only [max_eq_right hclog] using
    rank_polynomialMul_finiteField_le_clog (K := K) a b ha hb

end MatrixMultiplication.Tensor
