module

public import Omega.Tensor.MatrixTensor
public import Omega.Tensor.DegenerationOperations
import Mathlib.Tactic.FinCases

/-!
# Flattening ranks cannot increase under polynomial degeneration

Grouping two factors turns each flattening into a matrix tensor. Polynomial
factor maps induce a degeneration of these matrix tensors. Their asymptotic
ranks equal matrix ranks, so asymptotic-rank monotonicity gives the result.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Grouping the last two factors commutes with their Kronecker factor maps. -/
theorem map_flatteningFirst [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) :
    map A (Matrix.kronecker B C) (1 : Matrix Unit Unit R)
      (matrixTensor (flatteningFirst T)) = matrixTensor (flatteningFirst (map A B C T)) := by
  funext i jk u
  simp [map, matrixTensor, flatteningFirst, Matrix.kronecker, Matrix.kroneckerMap,
    Fintype.sum_prod_type, mul_assoc]

/-- Grouping the first and last factors commutes with their Kronecker factor maps. -/
theorem map_flatteningSecond [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) :
    map B (Matrix.kronecker A C) (1 : Matrix Unit Unit R)
      (matrixTensor (flatteningSecond T)) = matrixTensor (flatteningSecond (map A B C T)) := by
  funext j ik u
  simp only [map, matrixTensor, flatteningSecond, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, ite_true, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Grouping the first two factors commutes with their Kronecker factor maps. -/
theorem map_flatteningThird [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) :
    map C (Matrix.kronecker A B) (1 : Matrix Unit Unit R)
      (matrixTensor (flatteningThird T)) = matrixTensor (flatteningThird (map A B C T)) := by
  funext k ij u
  simp only [map, matrixTensor, flatteningThird, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, ite_true, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Grouping the last two factors transports a polynomial degeneration witness. -/
def DegenerationWitness.flatteningFirst [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (w : DegenerationWitness T S) :
    DegenerationWitness (matrixTensor (Tensor.flatteningFirst T))
      (matrixTensor (Tensor.flatteningFirst S)) where
  order := w.order
  firstMap := w.firstMap
  secondMap := Matrix.kronecker w.secondMap w.thirdMap
  thirdMap := 1
  remainder := matrixTensor (Tensor.flatteningFirst w.remainder)
  equation := by
    intro i jk u
    change map w.firstMap (Matrix.kronecker w.secondMap w.thirdMap) 1
      (matrixTensor (Tensor.flatteningFirst (liftPolynomial T))) i jk u = _
    rw [map_flatteningFirst]
    exact w.equation i jk.1 jk.2

/-- Grouping the first and last factors transports a polynomial degeneration witness. -/
def DegenerationWitness.flatteningSecond [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (w : DegenerationWitness T S) :
    DegenerationWitness (matrixTensor (Tensor.flatteningSecond T))
      (matrixTensor (Tensor.flatteningSecond S)) where
  order := w.order
  firstMap := w.secondMap
  secondMap := Matrix.kronecker w.firstMap w.thirdMap
  thirdMap := 1
  remainder := matrixTensor (Tensor.flatteningSecond w.remainder)
  equation := by
    intro j ik u
    change map w.secondMap (Matrix.kronecker w.firstMap w.thirdMap) 1
      (matrixTensor (Tensor.flatteningSecond (liftPolynomial T))) j ik u = _
    rw [map_flatteningSecond]
    exact w.equation ik.1 j ik.2

/-- Grouping the first two factors transports a polynomial degeneration witness. -/
def DegenerationWitness.flatteningThird [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (w : DegenerationWitness T S) :
    DegenerationWitness (matrixTensor (Tensor.flatteningThird T))
      (matrixTensor (Tensor.flatteningThird S)) where
  order := w.order
  firstMap := w.thirdMap
  secondMap := Matrix.kronecker w.firstMap w.secondMap
  thirdMap := 1
  remainder := matrixTensor (Tensor.flatteningThird w.remainder)
  equation := by
    intro k ij u
    change map w.thirdMap (Matrix.kronecker w.firstMap w.secondMap) 1
      (matrixTensor (Tensor.flatteningThird (liftPolynomial T))) k ij u = _
    rw [map_flatteningThird]
    exact w.equation ij.1 ij.2 k

/-- Every flattening rank is monotone under polynomial degeneration, over every field. -/
theorem flatteningRank_mono_degeneration [Field R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Degenerates T S) (a : Fin 3) :
    flatteningRank S a ≤ flatteningRank T a := by
  obtain ⟨w⟩ := h
  fin_cases a
  · change (Tensor.flatteningFirst S).rank ≤ (Tensor.flatteningFirst T).rank
    have hm := asymptoticRank_mono_degeneration ⟨w.flatteningFirst⟩
    rw [asymptoticRank_matrixTensor, asymptoticRank_matrixTensor] at hm
    exact_mod_cast hm
  · change (Tensor.flatteningSecond S).rank ≤ (Tensor.flatteningSecond T).rank
    have hm := asymptoticRank_mono_degeneration ⟨w.flatteningSecond⟩
    rw [asymptoticRank_matrixTensor, asymptoticRank_matrixTensor] at hm
    exact_mod_cast hm
  · change (Tensor.flatteningThird S).rank ≤ (Tensor.flatteningThird T).rank
    have hm := asymptoticRank_mono_degeneration ⟨w.flatteningThird⟩
    rw [asymptoticRank_matrixTensor, asymptoticRank_matrixTensor] at hm
    exact_mod_cast hm

/-- Ordinary restriction is a special case of flattening-rank monotonicity. -/
theorem flatteningRank_mono [Field R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Restricts T S) (a : Fin 3) :
    flatteningRank S a ≤ flatteningRank T a :=
  flatteningRank_mono_degeneration h.degenerates a

/-- Equivalent tensors have identical flattening ranks. -/
theorem flatteningRank_eq_of_equivalent [Field R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Equivalent T S) (a : Fin 3) :
    flatteningRank T a = flatteningRank S a :=
  le_antisymm (flatteningRank_mono h.2 a) (flatteningRank_mono h.1 a)

end MatrixMultiplication.Tensor
