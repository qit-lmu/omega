module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic

/-!
# Matrix rank and Kronecker products

The image of a tensor product of linear maps is the tensor product of their
images. Over a field, dimensions therefore multiply, including for rectangular
matrices.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication

open Module TensorProduct

variable {K : Type*} [Field K]

private def tensorPiEquiv (m p : Type*) [Fintype p] [DecidableEq p] :
    ((m → K) ⊗[K] (p → K)) ≃ₗ[K] (m × p → K) :=
  (TensorProduct.piScalarRight K K (m → K) p).trans
    { toFun := fun f i => f i.2 i.1
      invFun := fun f j i => f (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem tensorPiEquiv_tmul {m p : Type*} [Fintype p] [DecidableEq p]
    (x : m → K) (y : p → K) (i : m × p) :
    tensorPiEquiv m p (x ⊗ₜ[K] y) i = x i.1 * y i.2 := by
  simp [tensorPiEquiv, mul_comm]

private theorem finrank_range_tensor_map
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q]
    [Module K M] [Module K N] [Module K P] [Module K Q]
    (f : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    finrank K (LinearMap.range (TensorProduct.map f g)) =
      finrank K (LinearMap.range f) * finrank K (LinearMap.range g) := by
  rw [TensorProduct.range_map, ← TensorProduct.range_mapIncl]
  rw [LinearMap.finrank_range_of_inj
    (TensorProduct.map_injective_of_flat_flat _ _
      (LinearMap.range f).subtype_injective (LinearMap.range g).subtype_injective)]
  exact Module.finrank_tensorProduct

/-- The rank of a Kronecker product is the product of the two matrix ranks,
over every field and for arbitrary finite rectangular shapes. -/
theorem matrix_rank_kronecker {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    Matrix.rank (Matrix.kronecker A B) = Matrix.rank A * Matrix.rank B := by
  classical
  have hmap : (Matrix.kronecker A B).mulVecLin.comp
      (tensorPiEquiv n q).toLinearMap =
      (tensorPiEquiv m p).toLinearMap.comp
        (TensorProduct.map A.mulVecLin B.mulVecLin) := by
    apply TensorProduct.ext'
    intro x y
    apply funext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.map_tmul, tensorPiEquiv_tmul,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ac_rfl
  have hrank := congrArg (fun f => finrank K (LinearMap.range f)) hmap
  change finrank K (LinearMap.range ((Matrix.kronecker A B).mulVecLin.comp
      (tensorPiEquiv n q).toLinearMap)) =
    finrank K (LinearMap.range ((tensorPiEquiv m p).toLinearMap.comp
      (TensorProduct.map A.mulVecLin B.mulVecLin))) at hrank
  rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq] at hrank
  exact hrank.trans (finrank_range_tensor_map A.mulVecLin B.mulVecLin)

end MatrixMultiplication
