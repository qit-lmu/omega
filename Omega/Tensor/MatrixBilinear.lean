module

public import Omega.Tensor.ExactSequenceDegeneration
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Matrix multiplication as a coefficient tensor

Contracting the first two coordinates of `matrixMul` with two input matrices
computes their product. In the standard matrix bases, it is exactly the
structure tensor of the bilinear multiplication map. All dimensions may be zero.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

/-- The tensor coefficients compute every entry of ordinary matrix
multiplication, with the input coordinate order used in the manuscript. -/
theorem matrixMul_bilinear {R : Type*} [Semiring R] {l m n : ℕ}
    (X : Matrix (Fin l) (Fin m) R) (Y : Matrix (Fin m) (Fin n) R)
    (k : Fin l × Fin n) :
    (X * Y) k.1 k.2 = ∑ i, ∑ j, X i.1 i.2 * Y j.1 j.2 * matrixMul R l m n i j k := by
  simp [matrixMul, Fintype.sum_prod_type, Matrix.mul_apply, mul_ite,
    ite_and, Finset.sum_ite_irrel]

private theorem matrix_stdBasis_repr {R : Type*} [Semiring R]
    {l n : ℕ} (X : Matrix (Fin l) (Fin n) R) (k : Fin l × Fin n) :
    (Matrix.stdBasis R (Fin l) (Fin n)).repr X k = X k.1 k.2 := by
  have h := congrArg (fun M : Matrix (Fin l) (Fin n) R => M k.1 k.2)
    ((Matrix.stdBasis R (Fin l) (Fin n)).sum_repr X)
  simpa only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.stdBasis_eq_single,
    Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero] using h

/-- In standard matrix bases the multiplication tensor is literally the
structure tensor of the bilinear map `(X,Y) ↦ X*Y`. -/
@[simp]
theorem structureTensor_matrixMul (K : Type*) [Field K] (l m n : ℕ) :
    structureTensor (Matrix.stdBasis K (Fin l) (Fin m))
      (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin l) (Fin n))
      (_root_.mulLinearMap K) = matrixMul K l m n := by
  funext i j k
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  rcases k with ⟨k₁, k₂⟩
  simp [structureTensor, matrix_stdBasis_repr, Matrix.stdBasis_eq_single,
    _root_.mulLinearMap, _root_.mulLeftLinearMap, Matrix.mul_apply,
    Matrix.single_apply, matrixMul, ite_and]
  split_ifs <;> rfl

end MatrixMultiplication.Tensor
