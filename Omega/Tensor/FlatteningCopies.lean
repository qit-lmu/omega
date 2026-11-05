module

public import Omega.Tensor.DirectSumCopies

/-!
# Flattening ranks of repeated blocks

Ordinary copies multiply each flattening rank by the number of blocks.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- Repeating a tensor in independent blocks multiplies every flattening rank. -/
theorem flatteningRank_directSumCopies {K I J L : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (a : ℕ) (i : Fin 3) :
    flatteningRank (directSumCopies T a) i = a * flatteningRank T i := by
  rw [directSumCopies, flatteningRank_kronecker, flatteningRank_diagonal]

/-- The first flattening of repeated positive square matrix-multiplication blocks. -/
theorem flatteningRank_directSumCopies_matrixMul_zero (K : Type*) [Field K]
    (a b : ℕ) (hb : 1 ≤ b) :
    flatteningRank (directSumCopies (matrixMul K b b b) a) 0 = a * b ^ 2 := by
  rw [flatteningRank_directSumCopies, flatteningRank_matrixMul_zero b b b (by omega), pow_two]

end MatrixMultiplication.Tensor
