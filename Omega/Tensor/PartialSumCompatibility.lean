module

public import Omega.Tensor.PartialSumOperations
public import Omega.Tensor.FlatteningDegeneration

/-!
# Compatible maps and the partial-direct-sum caveat

A partial direct sum permits independent maps on the last two factors, but
the map on the first factor must be shared. Remark 3.3 is witnessed by two
scalar blocks supported at the same first-factor basis vector versus blocks
supported at two different basis vectors. Their first flattenings have ranks
one and two over every field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

section CompatibleMaps

variable {R I I' J₀ L₀ J₁ L₁ J₀' L₀' J₁' L₁' : Type*} [CommSemiring R]
variable [Fintype I] [Fintype J₀] [Fintype L₀] [Fintype J₁] [Fintype L₁]

/-- The common first-factor map and block-diagonal maps on the other factors
commute with partial direct sum. -/
theorem map_partialSum (A : Matrix I' I R)
    (B₀ : Matrix J₀' J₀ R) (C₀ : Matrix L₀' L₀ R)
    (B₁ : Matrix J₁' J₁ R) (C₁ : Matrix L₁' L₁ R)
    (T : Tensor R I J₀ L₀) (S : Tensor R I J₁ L₁) :
    map A (Matrix.fromBlocks B₀ 0 0 B₁) (Matrix.fromBlocks C₀ 0 0 C₁)
      (partialSum T S) = partialSum (map A B₀ C₀ T) (map A B₁ C₁ S) := by
  funext i j k
  cases j <;> cases k <;>
    simp [map, partialSum, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- Block restrictions assemble whenever their first-factor map is shared. -/
theorem partialSum_restricts_fixedFirst (A : Matrix I' I R)
    {T : Tensor R I J₀ L₀} {S : Tensor R I J₁ L₁}
    {T' : Tensor R I' J₀' L₀'} {S' : Tensor R I' J₁' L₁'}
    (hT : ∃ B C, map A B C T = T') (hS : ∃ B C, map A B C S = S') :
    Restricts (partialSum T S) (partialSum T' S') := by
  obtain ⟨B₀, C₀, hT⟩ := hT
  obtain ⟨B₁, C₁, hS⟩ := hS
  refine ⟨A, Matrix.fromBlocks B₀ 0 0 B₁, Matrix.fromBlocks C₀ 0 0 C₁, ?_⟩
  rw [map_partialSum, hT, hS]

/-- Compatible block equivalences assemble when each direction uses a common
first-factor map. Taking these maps to be identities fixes the first factor. -/
theorem partialSum_congr_fixedFirst
    [Fintype I'] [Fintype J₀'] [Fintype L₀'] [Fintype J₁'] [Fintype L₁']
    (A : Matrix I' I R) (A' : Matrix I I' R)
    {T : Tensor R I J₀ L₀} {S : Tensor R I J₁ L₁}
    {T' : Tensor R I' J₀' L₀'} {S' : Tensor R I' J₁' L₁'}
    (hT : ∃ B C, map A B C T = T') (hS : ∃ B C, map A B C S = S')
    (hT' : ∃ B C, map A' B C T' = T) (hS' : ∃ B C, map A' B C S' = S) :
    Equivalent (partialSum T S) (partialSum T' S') :=
  ⟨partialSum_restricts_fixedFirst A hT hS, partialSum_restricts_fixedFirst A' hT' hS'⟩

end CompatibleMaps

section Counterexample

variable (K : Type*) [Field K]

/-- A scalar block supported at one of two first-factor basis vectors. -/
def partialSumCounterexampleBlock (b : Bool) : Tensor K Bool Unit Unit :=
  fun i _ _ => if i = b then 1 else 0

/-- Moving the scalar block from the first basis vector to the second is a
tensor equivalence. -/
theorem partialSumCounterexampleBlock_equivalent :
    Equivalent (partialSumCounterexampleBlock K false) (partialSumCounterexampleBlock K true) := by
  apply equivalent_of_reindex (Equiv.swap false true) (Equiv.refl _) (Equiv.refl _)
  funext i j k
  cases i <;> simp [reindex, partialSumCounterexampleBlock]

/-- Two blocks sharing their first-factor vector have first-flattening rank one. -/
theorem partialSumCounterexample_source_rank :
    flatteningRank (partialSum (partialSumCounterexampleBlock K false)
      (partialSumCounterexampleBlock K false)) 0 = 1 := by
  let M := flatteningFirst (partialSum (partialSumCounterexampleBlock K false)
    (partialSumCounterexampleBlock K false))
  change M.rank = 1
  apply le_antisymm
  · have hM : M = Matrix.vecMulVec
        (fun p : (Unit ⊕ Unit) × (Unit ⊕ Unit) => if p.1 = p.2 then (1 : K) else 0)
        (fun i : Bool => if i = false then (1 : K) else 0) := by
      ext ⟨j, k⟩ i
      cases j with
      | inl j => cases k <;> cases i <;> simp [M, flatteningFirst, partialSum,
          partialSumCounterexampleBlock, Matrix.vecMulVec]
      | inr j => cases k <;> cases i <;> simp [M, flatteningFirst, partialSum,
          partialSumCounterexampleBlock, Matrix.vecMulVec]
    rw [hM]
    exact Matrix.rank_vecMulVec_le _ _
  · have hM : M.submatrix (fun _ : Unit => (Sum.inl (), Sum.inl ()))
        (fun _ : Unit => false) = (1 : Matrix Unit Unit K) := by
      ext i j
      simp [M, Matrix.submatrix, flatteningFirst, partialSumCounterexampleBlock]
    have h := Matrix.rank_submatrix_le M (fun _ : Unit => (Sum.inl (), Sum.inl ()))
      (fun _ : Unit => false)
    simpa only [hM, Matrix.rank_one, Fintype.card_unit] using h

/-- Blocks with independent first-factor vectors have first-flattening rank two. -/
theorem partialSumCounterexample_target_rank :
    flatteningRank (partialSum (partialSumCounterexampleBlock K false)
      (partialSumCounterexampleBlock K true)) 0 = 2 := by
  let M := flatteningFirst (partialSum (partialSumCounterexampleBlock K false)
    (partialSumCounterexampleBlock K true))
  let row : Bool → (Unit ⊕ Unit) × (Unit ⊕ Unit) :=
    fun b => if b then (Sum.inr (), Sum.inr ()) else (Sum.inl (), Sum.inl ())
  change M.rank = 2
  apply le_antisymm
  · simpa only [Fintype.card_bool] using M.rank_le_card_width
  · have hM : M.submatrix row id = (1 : Matrix Bool Bool K) := by
      ext i j
      cases i <;> cases j <;>
        simp [M, row, Matrix.submatrix, flatteningFirst, partialSumCounterexampleBlock]
    have h := Matrix.rank_submatrix_le M row id
    simpa only [hM, Matrix.rank_one, Fintype.card_bool] using h

/-- The first-flattening rank prevents the shared-vector partial sum from
restricting to the independent-vector partial sum. -/
theorem partialSumCounterexample_not_restricts :
    ¬ Restricts (partialSum (partialSumCounterexampleBlock K false)
        (partialSumCounterexampleBlock K false))
      (partialSum (partialSumCounterexampleBlock K false)
        (partialSumCounterexampleBlock K true)) := by
  intro h
  have hr := flatteningRank_mono h 0
  rw [partialSumCounterexample_source_rank, partialSumCounterexample_target_rank] at hr
  exact (by decide : ¬ (2 ≤ 1)) hr

/-- Remark 3.3: independent equivalences of blocks need not preserve partial
direct sum, over any field. -/
theorem partialSum_equivalence_counterexample :
    ∃ S₁ S₂ T₁ T₂ : Tensor K Bool Unit Unit,
      Equivalent S₁ T₁ ∧ Equivalent S₂ T₂ ∧
        ¬ Equivalent (partialSum S₁ S₂) (partialSum T₁ T₂) := by
  refine ⟨partialSumCounterexampleBlock K false, partialSumCounterexampleBlock K false,
    partialSumCounterexampleBlock K false, partialSumCounterexampleBlock K true,
    Equivalent.refl _, partialSumCounterexampleBlock_equivalent K, ?_⟩
  exact fun h => partialSumCounterexample_not_restricts K h.1

/-- Remark 3.3: independent restrictions of blocks need not preserve partial
direct sum, over any field. -/
theorem partialSum_restriction_counterexample :
    ∃ S₁ S₂ T₁ T₂ : Tensor K Bool Unit Unit,
      Restricts S₁ T₁ ∧ Restricts S₂ T₂ ∧
        ¬ Restricts (partialSum S₁ S₂) (partialSum T₁ T₂) := by
  refine ⟨partialSumCounterexampleBlock K false, partialSumCounterexampleBlock K false,
    partialSumCounterexampleBlock K false, partialSumCounterexampleBlock K true,
    Restricts.refl _, (partialSumCounterexampleBlock_equivalent K).1,
    partialSumCounterexample_not_restricts K⟩

end Counterexample

end MatrixMultiplication.Tensor
