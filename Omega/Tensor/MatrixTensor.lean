module

public import Omega.Tensor.FlatteningBounds

/-!
# Matrices as tensors with a one-dimensional third factor

The ordinary and asymptotic ranks of these tensors equal matrix rank.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {K I J : Type*}

/-- A matrix as a three-factor tensor whose last index is a singleton. -/
def matrixTensor (A : Matrix J I K) : Tensor K I J Unit := fun i j _ => A j i

/-- A matrix has a decomposition into as many outer products as its rank. -/
theorem exists_matrix_rank_decomposition [Field K] [Fintype I]
    (A : Matrix J I K) :
    ∃ (x : Fin A.rank → I → K) (y : Fin A.rank → J → K),
      ∀ j i, A j i = ∑ a, x a i * y a j := by
  classical
  let b : Module.Basis (Fin A.rank) K (LinearMap.range A.mulVecLin) :=
    Module.finBasis K (LinearMap.range A.mulVecLin)
  let v (i : I) := A.mulVecLin.rangeRestrict (Pi.single i 1)
  refine ⟨(fun a i => b.repr (v i) a), (fun a j => (b a).val j), ?_⟩
  intro j i
  have h := congrArg (fun w : LinearMap.range A.mulVecLin => w.val j) (b.sum_repr (v i))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at h
  change (∑ a, b.repr (v i) a * (b a).val j) =
    (A.mulVecLin (Pi.single i 1)) j at h
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h
  exact h.symm

/-- The tensor representation of a matrix has no larger rank than the matrix. -/
theorem rank_matrixTensor_le [Field K] [Fintype I] [Fintype J]
    (A : Matrix J I K) : rank (matrixTensor A) ≤ A.rank := by
  obtain ⟨x, y, h⟩ := exists_matrix_rank_decomposition A
  have he : matrixTensor A = ∑ a, pure (x a) (y a) (fun _ : Unit => 1) := by
    funext i j u
    simpa [matrixTensor, pure] using h j i
  have hr := rank_le_of_sum_pure x y (fun (_ : Fin A.rank) (_ : Unit) => (1 : K))
  simpa only [← he, Fintype.card_fin] using hr

/-- Flattening the matrix tensor recovers its original matrix rank. -/
theorem flatteningRank_matrixTensor_zero [Field K] [Fintype I] [Fintype J]
    (A : Matrix J I K) : flatteningRank (matrixTensor A) 0 = A.rank := by
  change (flatteningFirst (matrixTensor A)).rank = A.rank
  have he : flatteningFirst (matrixTensor A) =
      A.reindex (Equiv.prodUnique J Unit).symm (Equiv.refl I) := rfl
  rw [he]
  exact Matrix.rank_reindex _ _ A

/-- The ordinary tensor rank of a matrix tensor equals matrix rank. -/
theorem rank_matrixTensor [Field K] [Fintype I] [Fintype J]
    (A : Matrix J I K) : rank (matrixTensor A) = A.rank := by
  apply le_antisymm (rank_matrixTensor_le A)
  simpa only [flatteningRank_matrixTensor_zero] using flatteningRank_le_rank (matrixTensor A) 0

/-- The asymptotic rank of a matrix tensor equals matrix rank. -/
theorem asymptoticRank_matrixTensor [Field K] [Fintype I] [Fintype J]
    (A : Matrix J I K) : asymptoticRank (matrixTensor A) = A.rank := by
  apply le_antisymm
  · exact (asymptoticRank_le_rank _).trans (Nat.cast_le.mpr (rank_matrixTensor_le A))
  · simpa only [flatteningRank_matrixTensor_zero] using
      flatteningRank_le_asymptoticRank (matrixTensor A) 0

end MatrixMultiplication.Tensor
