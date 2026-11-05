module

public import Omega.FractionalValue
public import Omega.Tensor.SymmetrizationOperations
public import Omega.Tensor.MatrixCapacity

/-!
# A unit witness for every nonzero tensor

Taking all five integer parameters equal to one gives a witness of score one.
This establishes nonemptiness and the lower bound on value independently of
any value identities or supremum manipulations.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]

/-- Every nonzero tensor has the witness with all integer parameters equal to one. -/
def unitValueWitness (T : Tensor K I J L) (hT : T ≠ 0) : ValueWitness T := by
  refine ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
  let U := directSumCopies (matrixMul K 1 1 1) 1
  have hU : U ≠ 0 := by
    intro h
    have hc := congrFun (congrFun (congrFun h (0, (0, 0))) (0, (0, 0))) (0, (0, 0))
    simp [U, directSumCopies, kronecker, diagonal, matrixMul] at hc
  have hsource := kronecker_ne_zero hU (kroneckerPower_ne_zero (symmetrize_ne_zero hT) 1)
  have hr : rank U ≤ 1 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, one_mul] using rank_le_card U
  exact ((restricts_diagonal_one_of_ne_zero _ hsource).trans
    (diagonal_restricts_of_rank_le U hr)).degenerates

@[simp]
theorem unitValueWitness_score (T : Tensor K I J L) (hT : T ≠ 0) (τ : ℝ) :
    (unitValueWitness T hT).score τ = 1 := by
  simp [ValueWitness.score, unitValueWitness]

/-- The defining witness type is nonempty for every nonzero tensor. -/
theorem valueWitness_nonempty (T : Tensor K I J L) (hT : T ≠ 0) :
    Nonempty (ValueWitness T) := ⟨unitValueWitness T hT⟩

/-- The value of a nonzero tensor is at least one, even outside the admissible interval. -/
theorem one_le_fractionalValue (T : Tensor K I J L) (hT : T ≠ 0) (τ : ℝ) :
    1 ≤ fractionalValue T τ := by
  simpa only [unitValueWitness_score, ENNReal.ofReal_one] using
    (unitValueWitness T hT).score_le_fractionalValue τ

end MatrixMultiplication.Tensor
