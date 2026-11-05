module

public import Omega.Tensor.Basic
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Polynomial witnesses for tensor degeneration

A witness consists of three polynomial factor maps whose image has the target
tensor as the coefficient of `X ^ order`, with all lower coefficients zero.
This definition is algebraic and does not require a topology or an infinite
base field. Composition, tensor powers, products, and direct sums are proved in
`DegenerationOperations`. Equivalence to the manuscript's rational-function
definition is proved in `RationalDegeneration` over every field.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Regard a coefficient tensor as a tensor of constant polynomials. -/
def liftPolynomial [Semiring R] (T : Tensor R I J L) : Tensor R[X] I J L :=
  fun i j k => C (T i j k)

/-- Extract one coefficient from each entry of a polynomial tensor. -/
def coefficient [Semiring R] (T : Tensor R[X] I J L) (n : ℕ) : Tensor R I J L :=
  fun i j k => (T i j k).coeff n

@[simp]
theorem coefficient_zero [Semiring R] (n : ℕ) :
    coefficient (0 : Tensor R[X] I J L) n = 0 := by
  funext i j k
  simp [coefficient]

@[simp]
theorem coefficient_liftPolynomial_zero [Semiring R] (T : Tensor R I J L) :
    coefficient (liftPolynomial T) 0 = T := by
  funext i j k
  simp [coefficient, liftPolynomial]

@[simp]
theorem liftPolynomial_zero [Semiring R] :
    liftPolynomial (0 : Tensor R I J L) = 0 := by
  funext i j k
  simp [liftPolynomial]

/-- Constant-polynomial extension commutes with the action on the three factors. -/
theorem liftPolynomial_map [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (T : Tensor R I J L) :
    liftPolynomial (map A B D T) =
      map (A.map C) (B.map C) (D.map C) (liftPolynomial T) := by
  funext i j k
  simp [liftPolynomial, map, Matrix.map_apply, map_mul]

/-- Explicit algebraic data witnessing a degeneration.  The exponent is a
nonnegative integer, and the remainder is polynomial in each coordinate. -/
structure DegenerationWitness [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (S : Tensor R I' J' L') where
  order : ℕ
  firstMap : Matrix I' I R[X]
  secondMap : Matrix J' J R[X]
  thirdMap : Matrix L' L R[X]
  remainder : Tensor R[X] I' J' L'
  equation : ∀ i j k,
    map firstMap secondMap thirdMap (liftPolynomial T) i j k =
      X ^ order * C (S i j k) + X ^ (order + 1) * remainder i j k

/-- `Degenerates T S` denotes `T ▷ S` in the manuscript: polynomial factor maps
recover `S` as their first possibly nonzero coefficient. -/
def Degenerates [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (S : Tensor R I' J' L') : Prop :=
  Nonempty (DegenerationWitness T S)

/-- An ordinary restriction is a degeneration of order zero. -/
theorem Restricts.degenerates [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Restricts T S) : Degenerates T S := by
  obtain ⟨A, B, D, h⟩ := h
  refine ⟨{
    order := 0
    firstMap := A.map C
    secondMap := B.map C
    thirdMap := D.map C
    remainder := 0
    equation := ?_
  }⟩
  intro i j k
  rw [← liftPolynomial_map, h]
  simp [liftPolynomial]

theorem Degenerates.refl [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : Degenerates T T :=
  (Restricts.refl T).degenerates

/-- The witness equation recovers the target coefficient exactly. -/
theorem DegenerationWitness.leadingCoefficient [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) :
    coefficient (map w.firstMap w.secondMap w.thirdMap (liftPolynomial T)) w.order = S := by
  funext i j k
  simp only [coefficient, w.equation, coeff_add]
  simp [coeff_X_pow_mul']

/-- Every coefficient below the witness order vanishes. -/
theorem DegenerationWitness.lowerCoefficient [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) {n : ℕ} (hn : n < w.order) :
    coefficient (map w.firstMap w.secondMap w.thirdMap (liftPolynomial T)) n = 0 := by
  funext i j k
  simp only [coefficient, w.equation, coeff_add]
  simp [coeff_X_pow_mul', Nat.ne_of_lt hn,
    Nat.not_le_of_lt (Nat.lt_trans hn (Nat.lt_succ_self w.order))]

/-- Every tensor degenerates to the zero tensor in any target dimensions. -/
theorem degenerates_zero [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : Degenerates T (0 : Tensor R I' J' L') := by
  apply Restricts.degenerates
  refine ⟨0, 0, 0, ?_⟩
  funext i j k
  simp [map]

/-- The zero tensor cannot degenerate to a nonzero tensor. -/
@[simp]
theorem zero_degenerates_iff [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (S : Tensor R I' J' L') :
    Degenerates (0 : Tensor R I J L) S ↔ S = 0 := by
  constructor
  · rintro ⟨w⟩
    simpa using w.leadingCoefficient.symm
  · rintro rfl
    exact degenerates_zero _

end MatrixMultiplication.Tensor
