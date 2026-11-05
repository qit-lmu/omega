module

public import Omega.Tensor.MatrixSubrank
public import Omega.Combinatorics.CentralBand

/-!
# The sharp matrix-multiplication border-subrank lower bound

The central band `n/2 ≤ i+j < n/2+n` contains `ceil(3n²/4)` pairs.
The sum-band monomial degeneration retains precisely their diagonal terms.
All weights are nonnegative integers and all leading coefficients are one,
so the construction works over every commutative semiring. In particular,
the manuscript's cited border-subrank lower bound holds over every field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- The central band gives the sharp integral number of diagonal terms. -/
theorem matrixMul_degenerates_diagonal_sharp_nat (R : Type*) [CommSemiring R] (n : ℕ) :
    Degenerates (matrixMul R n n n) (diagonal R ((3 * n ^ 2 + 3) / 4)) := by
  have h := matrixMul_degenerates_diagonal_of_sumBand R n (n / 2)
  change Degenerates (matrixMul R n n n) (diagonal R (Fintype.card (centralBand n))) at h
  rwa [card_centralBand] at h

/-- The sharp diagonal degeneration, in the manuscript's ceiling notation.
The zero-dimensional case is included. -/
theorem matrixMul_degenerates_diagonal_sharp (R : Type*) [CommSemiring R] (n : ℕ) :
    Degenerates (matrixMul R n n n) (diagonal R ⌈(3 : ℝ) * (n : ℝ) ^ 2 / 4⌉₊) := by
  rw [← sharpSubrankSize_eq_natCeil]
  exact matrixMul_degenerates_diagonal_sharp_nat R n

/-- The sharp cited border-subrank lower bound, over every field. -/
theorem matrixMul_borderSubrank_lower_bound (K : Type*) [Field K] (n : ℕ) :
    ⌈(3 : ℝ) * (n : ℝ) ^ 2 / 4⌉₊ ≤ borderSubrank (matrixMul K n n n) :=
  le_borderSubrank_of_degenerates_diagonal (matrixMul_degenerates_diagonal_sharp K n)

end MatrixMultiplication.Tensor
