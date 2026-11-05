module

public import Omega.Tensor.FlatteningExamples

/-!
# Strassen's partial direct sum tensor

The partial sum of the shapes `⟨n,1,1⟩` and `⟨1,n,1⟩` has border and
asymptotic rank `n+1` for positive `n`, over every field. An explicit
first-order degeneration supplies the upper bound, while an identity
submatrix of the second flattening supplies the lower bound.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

/-- The `⟨n,1,1⟩` block in Strassen's tensor. -/
def strassenLeft (R : Type*) [Zero R] [One R] (n : ℕ) :
    Tensor R (Fin n) (Fin 1) (Fin n) :=
  fun i _ k => if i = k then 1 else 0

/-- The `⟨1,n,1⟩` block in Strassen's tensor. -/
def strassenRight (R : Type*) [Zero R] [One R] (n : ℕ) :
    Tensor R (Fin n) (Fin n) (Fin 1) :=
  fun i j _ => if i = j then 1 else 0

/-- Strassen's tensor, with its first coordinate shared by the two blocks. -/
def strassenTensor (R : Type*) [Zero R] [One R] (n : ℕ) :
    Tensor R (Fin n) (Fin 1 ⊕ Fin n) (Fin n ⊕ Fin 1) :=
  partialSum (strassenLeft R n) (strassenRight R n)

/-- The first-order part of
`∑ i, xᵢ (y₀ + X yᵢ) (z₀ + X zᵢ) - (∑ i, xᵢ) y₀ z₀`
is Strassen's tensor. This uses `n+1` pure tensors in every characteristic. -/
theorem diagonal_degenerates_strassenTensor (R : Type*) [CommRing R] (n : ℕ) :
    Degenerates (diagonal R (n + 1)) (strassenTensor R n) := by
  classical
  let A : Matrix (Fin n) (Fin (n + 1)) R[X] :=
    fun i => Fin.cases (-1) (fun t => if i = t then 1 else 0)
  let B : Matrix (Fin 1 ⊕ Fin n) (Fin (n + 1)) R[X] := fun j =>
    match j with
    | .inl _ => fun _ => 1
    | .inr j => Fin.cases 0 (fun t => if j = t then X else 0)
  let D : Matrix (Fin n ⊕ Fin 1) (Fin (n + 1)) R[X] := fun k =>
    match k with
    | .inl k => Fin.cases 0 (fun t => if k = t then X else 0)
    | .inr _ => fun _ => 1
  let remainder : Tensor R[X] (Fin n) (Fin 1 ⊕ Fin n) (Fin n ⊕ Fin 1) :=
    fun i j k => match j, k with
    | .inr j, .inl k => if i = j ∧ i = k then 1 else 0
    | _, _ => 0
  refine ⟨{
    order := 1
    firstMap := A
    secondMap := B
    thirdMap := D
    remainder := remainder
    equation := ?_
  }⟩
  have hlift : liftPolynomial (diagonal R (n + 1)) =
      diagonal R[X] (n + 1) := by
    funext i j k
    simp [liftPolynomial, diagonal]
  intro i j k
  rw [hlift, map_diagonal]
  dsimp only
  rw [Fin.sum_univ_succ]
  cases j with
  | inl j =>
    cases k with
    | inl k =>
      simp [A, B, D, remainder, strassenTensor, partialSum, strassenLeft,
        ite_mul]
    | inr k =>
      simp [A, B, D, remainder, strassenTensor, partialSum]
  | inr j =>
    cases k with
    | inl k =>
      simp [A, B, D, remainder, strassenTensor, partialSum, ite_mul]
      split_ifs <;> simp_all [pow_two, eq_comm]
      aesop
    | inr k =>
      simp [A, B, D, remainder, strassenTensor, partialSum, strassenRight,
        ite_mul]

/-- For positive `n`, the second flattening of Strassen's tensor has full
column rank `n+1`. -/
@[simp]
theorem flatteningSecond_rank_strassenTensor (K : Type*) [Field K]
    (n : ℕ) (hn : 1 ≤ n) :
    (flatteningSecond (strassenTensor K n)).rank = n + 1 := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  let row : Fin 1 ⊕ Fin n → Fin n × (Fin n ⊕ Fin 1)
    | .inl _ => (i₀, .inl i₀)
    | .inr j => (j, .inr 0)
  have hidentity : (flatteningSecond (strassenTensor K n)).submatrix row id =
      (1 : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) K) := by
    ext j k
    cases j <;> cases k <;>
      simp [Matrix.submatrix, flatteningSecond, strassenTensor, partialSum,
        strassenLeft, strassenRight, row, Matrix.one_apply]
    exact Subsingleton.elim _ _
  apply le_antisymm
  · simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_comm] using
      (flatteningSecond (strassenTensor K n)).rank_le_card_width
  · simpa only [hidentity, Matrix.rank_one, Fintype.card_sum, Fintype.card_fin,
      Nat.add_comm] using
      Matrix.rank_submatrix_le (flatteningSecond (strassenTensor K n)) row id

/-- The second component of the flattening-rank API for Strassen's tensor. -/
@[simp]
theorem flatteningRank_strassenTensor_one (K : Type*) [Field K]
    (n : ℕ) (hn : 1 ≤ n) :
    flatteningRank (strassenTensor K n) 1 = n + 1 :=
  flatteningSecond_rank_strassenTensor K n hn

/-- Strassen's tensor has border rank `n+1` over every field. -/
@[simp]
theorem borderRank_strassenTensor (K : Type*) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    borderRank (strassenTensor K n) = n + 1 := by
  apply le_antisymm
  · exact borderRank_le_of_diagonal_degenerates (diagonal_degenerates_strassenTensor K n)
  · simpa only [flatteningRank_strassenTensor_one K n hn] using
      flatteningRank_le_borderRank (strassenTensor K n) 1

/-- Strassen's tensor has asymptotic rank `n+1` over every field. -/
@[simp]
theorem asymptoticRank_strassenTensor (K : Type*) [Field K]
    (n : ℕ) (hn : 1 ≤ n) :
    asymptoticRank (strassenTensor K n) = ((n + 1 : ℕ) : ℝ) := by
  apply le_antisymm
  · simpa only [borderRank_strassenTensor K n hn] using
      asymptoticRank_le_borderRank (strassenTensor K n)
  · simpa only [flatteningRank_strassenTensor_one K n hn] using
      flatteningRank_le_asymptoticRank (strassenTensor K n) 1

end MatrixMultiplication.Tensor
