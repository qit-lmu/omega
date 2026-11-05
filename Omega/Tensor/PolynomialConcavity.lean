module

public import Omega.Tensor.BivariateGrid
public import Omega.Tensor.PolynomialOperations
public import Omega.Tensor.SplitDegeneration

/-!
# The polynomial-multiplication concavity degeneration

Multiplication by `x-y`, a boundary section of specialization `y=x`, and
diagonal-tail coefficient maps give the three compatible split identities.
The generic split degeneration then separates the two prescribed blocks.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]

/-- The output coefficient occupied by one input monomial pair. -/
def polynomialMulOutputIndex {a b r : ℕ} (i : Fin a) (j : Fin b × Fin r) :
    Fin (a + b - 1) × Fin r :=
  (⟨i.val + j.1.val, by have := i.isLt; have := j.1.isLt; omega⟩, j.2)

private theorem polynomialMulCopies_delta {a b r : ℕ}
    (i : Fin a) (j : Fin b × Fin r) (k : Fin (a + b - 1) × Fin r) :
    polynomialMulCopies K a b r i j k =
      if k = polynomialMulOutputIndex i j then 1 else 0 := by
  simp [polynomialMulCopies, polynomialMul, polynomialMulOutputIndex,
    Prod.ext_iff, Fin.ext_iff, ← ite_and, eq_comm, and_comm]

private theorem map_polynomialMulCopies {a b r : ℕ} {Y Z : Type*}
    (B : Matrix Y (Fin b × Fin r) K) (C : Matrix Z (Fin (a + b - 1) × Fin r) K)
    (i : Fin a) (y : Y) (z : Z) :
    map (1 : Matrix (Fin a) (Fin a) K) B C (polynomialMulCopies K a b r) i y z =
      ∑ j, B y j * C z (polynomialMulOutputIndex i j) := by
  classical
  simp [map, Matrix.one_apply, polynomialMulCopies_delta, mul_ite]

/-- Output map recovering the coefficients before multiplication by `x-y`. -/
def concavityTailMap (a b p : ℕ) :
    Matrix (Fin (a + (b - 1) - 1) × Fin p)
      (Fin (a + b - 1) × Fin (p + 1)) K :=
  fun k v => gridTailCoefficient k.1.val k.2.val v.1.val v.2.val

/-- Output map specializing `y` to `x`. -/
def concavityDiagonalMap (a b p : ℕ) :
    Matrix (Fin (a + (b + p) - 1))
      (Fin (a + b - 1) × Fin (p + 1)) K :=
  fun k v => gridDiagonalCoefficient k.val v.1.val v.2.val

/-- The edge input and diagonal-tail output recover the smaller repeated
polynomial-multiplication tensor. -/
theorem concavity_edge_tail (a b p : ℕ) :
    map (1 : Matrix (Fin a) (Fin a) K) (gridEdgeMap b p) (concavityTailMap a b p)
      (polynomialMulCopies K a b (p + 1)) = polynomialMulCopies K a (b - 1) p := by
  funext i j k
  rw [map_polynomialMulCopies, sum_gridEdgeMap_mul]
  change gridTailCoefficient k.1.val k.2.val (i.val + (j.1.val + 1)) j.2.val -
    gridTailCoefficient k.1.val k.2.val (i.val + j.1.val) (j.2.val + 1) = _
  rw [← Nat.add_assoc i.val j.1.val 1, gridTailCoefficient_edge]
  simp [polynomialMulCopies, polynomialMul, Fin.ext_iff]

/-- The edge input vanishes under specialization `y=x`. -/
theorem concavity_edge_diagonal (a b p : ℕ) :
    map (1 : Matrix (Fin a) (Fin a) K) (gridEdgeMap b p) (concavityDiagonalMap a b p)
      (polynomialMulCopies K a b (p + 1)) = 0 := by
  funext i j k
  rw [map_polynomialMulCopies, sum_gridEdgeMap_mul]
  change gridDiagonalCoefficient k.val (i.val + (j.1.val + 1)) j.2.val -
    gridDiagonalCoefficient k.val (i.val + j.1.val) (j.2.val + 1) = 0
  rw [← Nat.add_assoc i.val j.1.val 1, gridDiagonalCoefficient_edge]

/-- The boundary section and specialization recover multiplication of the
full univariate coefficient range. -/
theorem concavity_section_diagonal (a b p : ℕ) (hb : 1 ≤ b) :
    map (1 : Matrix (Fin a) (Fin a) K) (gridSectionMap b p hb)
      (concavityDiagonalMap a b p) (polynomialMulCopies K a b (p + 1)) =
      polynomialMul K a (b + p) := by
  funext i s k
  rw [map_polynomialMulCopies, sum_gridSectionMap_mul]
  change (if (i.val + (gridSection b p hb s).1.val) +
      (gridSection b p hb s).2.val = k.val then (1 : K) else 0) = _
  rw [Nat.add_assoc, gridSection_degree]
  rfl

/-- The concavity degeneration in coordinates with a literal common first
factor. It is valid over every field, and also includes the empty smaller
block when `b=1` or `p=0`. -/
theorem polynomialMul_concavity_degeneration (K : Type*) [Field K]
    (a b p : ℕ) (hb : 1 ≤ b) :
    Degenerates (polynomialMulCopies K a b (p + 1))
      (partialSum (polynomialMulCopies K a (b - 1) p) (polynomialMul K a (b + p))) :=
  degenerates_partialSum_of_split_maps _ _ _ (gridEdgeMap b p) (gridSectionMap b p hb)
    (concavityTailMap a b p) (concavityDiagonalMap a b p)
    (concavity_edge_tail a b p) (concavity_edge_diagonal a b p)
    (concavity_section_diagonal a b p hb)

end MatrixMultiplication.Tensor
