module

public import Omega.Tensor.PolynomialDegeneration
public import Omega.Tensor.FlatteningExamples

/-!
# Exact border and asymptotic ranks of polynomial multiplication

For positive input sizes, the third flattening contains an identity matrix
of size `a+b-1`. This gives the lower bound over every field. The uniform
diagonal degeneration gives the matching border-rank upper bound.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]

/-- Every output coefficient of polynomial multiplication has its own
identity row in the third flattening. -/
@[simp]
theorem flatteningThird_rank_polynomialMul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (flatteningThird (polynomialMul K a b)).rank = a + b - 1 := by
  let row : Fin (a + b - 1) → Fin a × Fin b := fun k =>
    (⟨min k.val (a - 1), by omega⟩,
      ⟨k.val - min k.val (a - 1), by have hk := k.isLt; omega⟩)
  have hsum (k : Fin (a + b - 1)) : (row k).1.val + (row k).2.val = k.val := by
    dsimp only [row]
    omega
  have hidentity : (flatteningThird (polynomialMul K a b)).submatrix row id =
      (1 : Matrix (Fin (a + b - 1)) (Fin (a + b - 1)) K) := by
    ext k l
    simp [Matrix.submatrix, flatteningThird, polynomialMul, hsum,
      Matrix.one_apply, Fin.val_inj]
  apply le_antisymm
  · simpa only [Fintype.card_fin] using
      (flatteningThird (polynomialMul K a b)).rank_le_card_width
  · simpa only [hidentity, Matrix.rank_one, Fintype.card_fin] using
      Matrix.rank_submatrix_le (flatteningThird (polynomialMul K a b)) row id

/-- The third component of the flattening-rank API for polynomial multiplication. -/
@[simp]
theorem flatteningRank_polynomialMul_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    flatteningRank (polynomialMul K a b) 2 = a + b - 1 :=
  flatteningThird_rank_polynomialMul a b ha hb

/-- Polynomial multiplication has ordinary tensor rank at least its output size. -/
theorem add_sub_one_le_rank_polynomialMul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b - 1 ≤ rank (polynomialMul K a b) := by
  simpa only [flatteningRank_polynomialMul_two a b ha hb] using
    flatteningRank_le_rank (polynomialMul K a b) 2

/-- Polynomial multiplication has border rank `a+b-1` over every field. -/
@[simp]
theorem borderRank_polynomialMul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    borderRank (polynomialMul K a b) = a + b - 1 := by
  apply le_antisymm
  · exact borderRank_le_of_diagonal_degenerates (diagonal_degenerates_polynomialMul K a b)
  · simpa only [flatteningRank_polynomialMul_two a b ha hb] using
      flatteningRank_le_borderRank (polynomialMul K a b) 2

/-- Polynomial multiplication has asymptotic rank `a+b-1` over every field. -/
@[simp]
theorem asymptoticRank_polynomialMul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    asymptoticRank (polynomialMul K a b) = ((a + b - 1 : ℕ) : ℝ) := by
  apply le_antisymm
  · simpa only [borderRank_polynomialMul a b ha hb] using
      asymptoticRank_le_borderRank (polynomialMul K a b)
  · simpa only [flatteningRank_polynomialMul_two a b ha hb] using
      flatteningRank_le_asymptoticRank (polynomialMul K a b) 2

end MatrixMultiplication.Tensor
