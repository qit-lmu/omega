module

public import Omega.Tensor.AsymptoticDegeneration

/-!
# Permuting tensor factors

A cyclic rotation and the transposition of the first two factors generate all
six permutations. These operations preserve tensor rank and asymptotic rank.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L : Type*}

/-- Rotate the three factors to the order second, third, first. -/
def rotate (T : Tensor R I J L) : Tensor R J L I := fun j k i => T i j k

/-- Transpose the first two factors. -/
def swapFirstTwo (T : Tensor R I J L) : Tensor R J I L := fun j i k => T i j k

@[simp]
theorem rotate_three (T : Tensor R I J L) : rotate (rotate (rotate T)) = T := rfl

@[simp]
theorem swapFirstTwo_twice (T : Tensor R I J L) : swapFirstTwo (swapFirstTwo T) = T := rfl

private theorem rank_rotate_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank (rotate T) ≤ rank T := by
  classical
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  have he : rotate T = ∑ a, pure (y a) (z a) (x a) := by
    funext j k i
    simp [rotate, hT, pure, mul_comm, mul_left_comm]
  rw [he]
  simpa only [Fintype.card_fin] using rank_le_of_sum_pure y z x

/-- Rotating factors preserves tensor rank. -/
@[simp]
theorem rank_rotate [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : rank (rotate T) = rank T := by
  apply le_antisymm (rank_rotate_le T)
  exact (rank_rotate_le (rotate (rotate T))).trans (rank_rotate_le (rotate T))

private theorem rank_swapFirstTwo_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank (swapFirstTwo T) ≤ rank T := by
  classical
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  have he : swapFirstTwo T = ∑ a, pure (y a) (x a) (z a) := by
    funext j i k
    simp [swapFirstTwo, hT, pure, mul_comm]
  rw [he]
  simpa only [Fintype.card_fin] using rank_le_of_sum_pure y x z

/-- Transposing the first two factors preserves tensor rank. -/
@[simp]
theorem rank_swapFirstTwo [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : rank (swapFirstTwo T) = rank T :=
  le_antisymm (rank_swapFirstTwo_le T) (rank_swapFirstTwo_le (swapFirstTwo T))

@[simp]
theorem kroneckerPower_rotate [CommMonoid R] (T : Tensor R I J L) (n : ℕ) :
    kroneckerPower (rotate T) n = rotate (kroneckerPower T n) := rfl

@[simp]
theorem kroneckerPower_swapFirstTwo [CommMonoid R] (T : Tensor R I J L) (n : ℕ) :
    kroneckerPower (swapFirstTwo T) n = swapFirstTwo (kroneckerPower T n) := rfl

/-- Rotating factors preserves asymptotic rank. -/
@[simp]
theorem asymptoticRank_rotate [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank (rotate T) = asymptoticRank T := by
  simp [asymptoticRank, rankRootValues]

/-- Transposing the first two factors preserves asymptotic rank. -/
@[simp]
theorem asymptoticRank_swapFirstTwo [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank (swapFirstTwo T) = asymptoticRank T := by
  simp [asymptoticRank, rankRootValues]

/-- A coefficient reindexing supplies mutual restrictions. -/
theorem equivalent_of_reindex [CommSemiring R]
    {I' J' L' : Type*} [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    (h : reindex eI eJ eL T = S) : Equivalent T S := by
  subst S
  refine ⟨restricts_reindex _ _ _ _, ?_⟩
  simpa only [reindex_symm] using restricts_reindex eI.symm eJ.symm eL.symm
    (reindex eI eJ eL T)

/-- Equivalence is compatible with Kronecker products. -/
theorem Equivalent.kronecker [CommSemiring R]
    {I' J' L' I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    [Fintype I₁] [Fintype J₁] [Fintype L₁] [Fintype I₂] [Fintype J₂] [Fintype L₂]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (hT : Equivalent T T') (hS : Equivalent S S') :
    Equivalent (kronecker T S) (kronecker T' S') :=
  ⟨hT.1.kronecker hS.1, hT.2.kronecker hS.2⟩

end MatrixMultiplication.Tensor
