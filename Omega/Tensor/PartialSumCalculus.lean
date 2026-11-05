module

public import Omega.Tensor.PartialSumPowers
public import Omega.Tensor.ScalingOperations

/-!
# Elementary calculus for partially direct sums

All reindexings leave the common first factor consistent. Repeated copies in
the second and third factors give the rectangular matrix tensor `⟨1,1,r⟩`.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R I J L J' L' J'' L'' A B C : Type*} [CommSemiring R]
variable [Fintype I] [Fintype J] [Fintype L] [Fintype J'] [Fintype L']
variable [Fintype J''] [Fintype L''] [Fintype A] [Fintype B] [Fintype C]

/-- Projecting to one block leaves the common first factor unchanged. -/
theorem partialSum_restricts_summand {H : Type*} [Fintype H] [DecidableEq H]
    {J L : H → Type*} [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R I (J h) (L h)) (h : H) :
    Restricts (partialSumFamily T) (T h) := by
  simpa only [partialSumFamily_same, id_eq] using
    restricts_pullback (partialSumFamily T) id (Sigma.mk h) (Sigma.mk h)

/-- Swapping the two separate block labels preserves a partial sum. -/
theorem partialSum_comm (T : Tensor R I J L) (S : Tensor R I J' L') :
    Equivalent (partialSum T S) (partialSum S T) := by
  apply equivalent_of_reindex (Equiv.refl _) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  funext i j k
  cases j <;> cases k <;> rfl

/-- Reassociating separate block labels preserves a partial sum. -/
theorem partialSum_assoc (T : Tensor R I J L) (S : Tensor R I J' L')
    (U : Tensor R I J'' L'') :
    Equivalent (partialSum (partialSum T S) U) (partialSum T (partialSum S U)) := by
  apply equivalent_of_reindex (Equiv.refl _) (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _)
  funext i j k
  rcases j with j | j | j <;> rcases k with k | k | k <;> rfl

/-- Kronecker multiplication distributes over a partial sum on the right. -/
theorem kronecker_partialSum (S : Tensor R A B C) (T : Tensor R I J L)
    (U : Tensor R I J' L') :
    Equivalent (kronecker S (partialSum T U))
      (partialSum (kronecker S T) (kronecker S U)) := by
  apply equivalent_of_reindex (Equiv.refl _) (Equiv.prodSumDistrib _ _ _)
    (Equiv.prodSumDistrib _ _ _)
  funext i j k
  cases j <;> cases k <;> simp [reindex, kronecker, partialSum]

/-- Kronecker multiplication distributes over a partial sum on the left. -/
theorem partialSum_kronecker (T : Tensor R I J L) (U : Tensor R I J' L')
    (S : Tensor R A B C) :
    Equivalent (kronecker (partialSum T U) S)
      (partialSum (kronecker T S) (kronecker U S)) := by
  apply equivalent_of_reindex (Equiv.refl _) (Equiv.sumProdDistrib _ _ _)
    (Equiv.sumProdDistrib _ _ _)
  funext i j k
  cases j <;> cases k <;> simp [reindex, kronecker, partialSum]

/-- Repeated partially direct copies of a tensor. -/
def partialSumCopies (T : Tensor R I J L) (r : ℕ) :
    Tensor R I (Σ _ : Fin r, J) (Σ _ : Fin r, L) := partialSumFamily (fun _ => T)

private def partialCopyEquiv (J : Type*) (r : ℕ) :
    (Σ _ : Fin r, J) ≃ J × (Fin 1 × Fin r) where
  toFun j := (j.2, 0, j.1)
  invFun j := ⟨j.2.2, j.1⟩
  left_inv j := by cases j; rfl
  right_inv j := by
    rcases j with ⟨j, i, h⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

/-- Repeated partial copies give exactly a matrix-multiplication factor. -/
theorem partialPower_equiv_matrixMul (T : Tensor R I J L) (r : ℕ) :
    Equivalent (partialSumCopies T r) (kronecker T (matrixMul R 1 1 r)) := by
  let : Unique (Fin 1 × Fin 1) :=
    ⟨⟨(0, 0)⟩, fun x => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  apply equivalent_of_reindex (Equiv.prodUnique I (Fin 1 × Fin 1)).symm
    (partialCopyEquiv J r) (partialCopyEquiv L r)
  funext i j k
  rcases j with ⟨j, j0, a⟩
  rcases k with ⟨k, k0, b⟩
  have hi : i.2.1 = k0 := Subsingleton.elim _ _
  have hj : i.2.2 = j0 := Subsingleton.elim _ _
  by_cases hab : a = b
  · subst b
    simp [reindex, partialCopyEquiv, partialSumCopies, partialSumFamily,
      kronecker, matrixMul, Equiv.prodUnique, hi, hj]
  · simp [reindex, partialCopyEquiv, partialSumCopies, partialSumFamily,
      kronecker, matrixMul, hi, hj, hab]

/-- The repeated partial sum of the unit is the corresponding matrix tensor. -/
theorem partialPower_unit_equiv_matrixMul (r : ℕ) :
    Equivalent (partialSumCopies (diagonal R 1) r) (matrixMul R 1 1 r) :=
  (partialPower_equiv_matrixMul (diagonal R 1) r).trans
    (directSumCopies_one_equivalent _)

end MatrixMultiplication.Tensor
