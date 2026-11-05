module

public import Omega.Tensor.FlatteningBounds
import Mathlib.Tactic.FinCases

/-!
# Flattening ranks of diagonal and matrix-multiplication tensors

Identity submatrices establish these ranks over every field, including finite
fields. In particular, the three notions of rank agree on diagonal tensors.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]

private theorem matrix_rank_eq_card_of_identity_submatrix
    {A B : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix B A K) (row : A → B)
    (h : M.submatrix row id = (1 : Matrix A A K)) :
    M.rank = Fintype.card A := by
  apply le_antisymm M.rank_le_card_width
  simpa only [h, Matrix.rank_one] using Matrix.rank_submatrix_le M row id

/-- The first flattening of a diagonal tensor has full column rank. -/
@[simp]
theorem flatteningFirst_rank_diagonal (r : ℕ) :
    (flatteningFirst (diagonal K r)).rank = r := by
  classical
  have h := matrix_rank_eq_card_of_identity_submatrix
    (flatteningFirst (diagonal K r)) (fun i => (i, i)) (by
      ext i j
      simp [flatteningFirst, Matrix.submatrix, diagonal, Matrix.one_apply, eq_comm])
  simpa only [Fintype.card_fin] using h

/-- The second flattening of a diagonal tensor has full column rank. -/
@[simp]
theorem flatteningSecond_rank_diagonal (r : ℕ) :
    (flatteningSecond (diagonal K r)).rank = r := by
  classical
  have h := matrix_rank_eq_card_of_identity_submatrix
    (flatteningSecond (diagonal K r)) (fun i => (i, i)) (by
      ext i j
      simp [flatteningSecond, Matrix.submatrix, diagonal, Matrix.one_apply, eq_comm])
  simpa only [Fintype.card_fin] using h

/-- The third flattening of a diagonal tensor has full column rank. -/
@[simp]
theorem flatteningThird_rank_diagonal (r : ℕ) :
    (flatteningThird (diagonal K r)).rank = r := by
  classical
  have h := matrix_rank_eq_card_of_identity_submatrix
    (flatteningThird (diagonal K r)) (fun i => (i, i)) (by
      ext i j
      simp [flatteningThird, Matrix.submatrix, diagonal, Matrix.one_apply])
  simpa only [Fintype.card_fin] using h

/-- All three flattening ranks of a diagonal tensor equal its size. -/
@[simp]
theorem flatteningRank_diagonal (r : ℕ) (a : Fin 3) :
    flatteningRank (diagonal K r) a = r := by
  fin_cases a <;> simp

/-- A diagonal tensor has rank exactly its size over any field. -/
@[simp]
theorem rank_diagonal (r : ℕ) : rank (diagonal K r) = r := by
  apply le_antisymm (rank_diagonal_le r)
  simpa using flatteningRank_le_rank (diagonal K r) 0

/-- A diagonal tensor has border rank exactly its size over any field. -/
@[simp]
theorem borderRank_diagonal (r : ℕ) : borderRank (diagonal K r) = r := by
  apply le_antisymm
  · simpa using borderRank_le_rank (diagonal K r)
  · simpa using flatteningRank_le_borderRank (diagonal K r) 0

/-- A diagonal tensor has asymptotic rank exactly its size over any field. -/
@[simp]
theorem asymptoticRank_diagonal (r : ℕ) : asymptoticRank (diagonal K r) = r := by
  apply le_antisymm
  · simpa using asymptoticRank_le_rank (diagonal K r)
  · simpa using flatteningRank_le_asymptoticRank (diagonal K r) 0

/-- A nonempty contracted dimension makes the first flattening of matrix
multiplication have full column rank. -/
@[simp]
theorem flatteningFirst_rank_matrixMul (l m n : ℕ) (hn : 0 < n) :
    (flatteningFirst (matrixMul K l m n)).rank = l * m := by
  classical
  let row : (Fin l × Fin m) → (Fin m × Fin n) × (Fin l × Fin n) :=
    fun ij => ((ij.2, ⟨0, hn⟩), (ij.1, ⟨0, hn⟩))
  have h := matrix_rank_eq_card_of_identity_submatrix
    (flatteningFirst (matrixMul K l m n)) row (by
      ext i j
      simp [row, flatteningFirst, Matrix.submatrix, matrixMul,
        Matrix.one_apply, Prod.ext_iff, eq_comm])
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

/-- The first matrix-multiplication flattening rank in the three-entry API. -/
@[simp]
theorem flatteningRank_matrixMul_zero (l m n : ℕ) (hn : 0 < n) :
    flatteningRank (matrixMul K l m n) 0 = l * m :=
  flatteningFirst_rank_matrixMul l m n hn

end MatrixMultiplication.Tensor
