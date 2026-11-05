module

public import Omega.Tensor.Degeneration

/-!
# Degeneration by nonnegative monomial weights

A coordinate pullback followed by diagonal monomial maps retains precisely
the coefficients of the least allowed total weight.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {R I J L I' J' L' : Type*} [CommSemiring R]
variable [Fintype I] [Fintype J] [Fintype L]

/-- A weighted coordinate pullback gives a degeneration when all nonzero
coefficients have weight at least `d`. -/
theorem degenerates_of_monomial_pullback
    (T : Tensor R I J L) (S : Tensor R I' J' L')
    (f : I' → I) (g : J' → J) (h : L' → L)
    (a : I' → ℕ) (b : J' → ℕ) (c : L' → ℕ) (d : ℕ)
    (hlow : ∀ i j k, a i + b j + c k < d → T (f i) (g j) (h k) = 0)
    (hlead : ∀ i j k, S i j k =
      if a i + b j + c k = d then T (f i) (g j) (h k) else 0) :
    Degenerates T S := by
  classical
  let A : Matrix I' I R[X] := fun i x => if f i = x then X ^ a i else 0
  let B : Matrix J' J R[X] := fun j y => if g j = y then X ^ b j else 0
  let C' : Matrix L' L R[X] := fun k z => if h k = z then X ^ c k else 0
  have hm : ∀ i j k, map A B C' (liftPolynomial T) i j k =
      X ^ (a i + b j + c k) * C (T (f i) (g j) (h k)) := by
    intro i j k
    simp [map, A, B, C', liftPolynomial, ← pow_add]
  refine ⟨{
    order := d
    firstMap := A
    secondMap := B
    thirdMap := C'
    remainder := fun i j k => if d < a i + b j + c k then
      X ^ (a i + b j + c k - (d + 1)) * C (T (f i) (g j) (h k)) else 0
    equation := ?_ }⟩
  intro i j k
  rw [hm, hlead]
  rcases lt_trichotomy (a i + b j + c k) d with hlt | heq | hgt
  · simp [hlt.ne, hlow i j k hlt, not_lt_of_ge hlt.le]
  · simp [heq]
  · have he : d + 1 + (a i + b j + c k - (d + 1)) = a i + b j + c k := by omega
    simp only [ne_of_gt hgt, ↓reduceIte, Polynomial.C_0, mul_zero, zero_add,
      hgt, ← mul_assoc, ← pow_add, he]

end MatrixMultiplication.Tensor
