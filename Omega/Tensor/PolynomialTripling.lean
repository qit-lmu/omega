module

public import Omega.Tensor.MonomialDegeneration
public import Omega.Tensor.PolynomialOperations

/-!
# Three-block degeneration of polynomial multiplication

The surviving middle block exchanges the second and third tensor factors.
All three coordinate embeddings fix the common first factor. Nonnegative
weights on the other factors give a polynomial witness of order one.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- Coordinate form of the three-block polynomial-multiplication degeneration.
The middle summand has its last two factors exchanged. -/
theorem polynomialMul_threeBlock_degeneration_coordinates
    (R : Type*) [CommSemiring R] (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Degenerates (polynomialMul R a (a + b + c + d - 1))
      (partialSum (partialSum (polynomialMul R a b)
        (fun i j k => polynomialMul R a c i k j)) (polynomialMul R a d)) := by
  let g : (Fin b ⊕ Fin (a + c - 1)) ⊕ Fin d → Fin (a + b + c + d - 1)
    | .inl (.inl j) => ⟨j.val, by have hj := j.isLt; omega⟩
    | .inl (.inr j) => ⟨a + b + c - 2 - j.val, by have hj := j.isLt; omega⟩
    | .inr j => ⟨a + b + c - 1 + j.val, by have hj := j.isLt; omega⟩
  let h : (Fin (a + b - 1) ⊕ Fin c) ⊕ Fin (a + d - 1) →
      Fin (a + (a + b + c + d - 1) - 1)
    | .inl (.inl k) => ⟨k.val, by have hk := k.isLt; omega⟩
    | .inl (.inr k) => ⟨a + b + c - 2 - k.val, by have hk := k.isLt; omega⟩
    | .inr k => ⟨a + b + c - 1 + k.val, by have hk := k.isLt; omega⟩
  let v : (Fin b ⊕ Fin (a + c - 1)) ⊕ Fin d → ℕ
    | .inl (.inr _) => 1
    | _ => 0
  let w : (Fin (a + b - 1) ⊕ Fin c) ⊕ Fin (a + d - 1) → ℕ
    | .inl (.inr _) => 0
    | _ => 1
  apply degenerates_of_monomial_pullback (f := id) (g := g) (h := h)
    (a := fun _ => 0) (b := v) (c := w) (d := 1)
  · intro i j k hlow
    have hi := i.isLt
    rcases j with (j | j) | j <;> rcases k with (k | k) | k <;>
      have hj := j.isLt <;> have hk := k.isLt <;>
      simp only [v, w, zero_add] at hlow
    all_goals first
      | omega
      | (simp only [polynomialMul, id_eq, g, h]; split_ifs <;> first | rfl | omega)
  · intro i j k
    have hi := i.isLt
    rcases j with (j | j) | j <;> rcases k with (k | k) | k <;>
      have hj := j.isLt <;> have hk := k.isLt <;>
      simp only [v, w, zero_add, partialSum, polynomialMul, id_eq, g, h]
    all_goals split_ifs <;> first | rfl | omega

/-- Polynomial multiplication degenerates to the three partially direct
blocks of `lem:pm-tripling-degeneration`. The same first-coordinate identity
is used in every block, including the reversed middle block. -/
theorem polynomialMul_threeBlock_degeneration
    (R : Type*) [CommSemiring R] (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Degenerates (polynomialMul R a (a + b + c + d - 1))
      (partialSum (partialSum (polynomialMul R a b)
        (swapLastTwo (polynomialMul R a c))) (polynomialMul R a d)) :=
  polynomialMul_threeBlock_degeneration_coordinates R a b c d ha hb hc hd

end MatrixMultiplication.Tensor
