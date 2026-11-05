module

public import Omega.Tensor.Examples

/-!
# Tensor rank

Rank is the smallest dimension of a diagonal tensor that restricts to the
given tensor, as in the manuscript. The minimum exists because the expansion
in coordinates supplies an explicit finite restriction witness.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Relabel the three chosen bases by equivalences. -/
def reindex (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor R I J L) :
    Tensor R I' J' L' :=
  fun i j k => T (eI.symm i) (eJ.symm j) (eL.symm k)

@[simp]
theorem reindex_symm (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    (T : Tensor R I J L) :
    reindex eI.symm eJ.symm eL.symm (reindex eI eJ eL T) = T := by
  funext i j k
  simp [reindex]

/-- Relabelling bases is a tensor restriction. -/
theorem restricts_reindex [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor R I J L) :
    Restricts T (reindex eI eJ eL T) := by
  classical
  refine ⟨Matrix.of (fun i' i => if i = eI.symm i' then 1 else 0),
    Matrix.of (fun j' j => if j = eJ.symm j' then 1 else 0),
    Matrix.of (fun k' k => if k = eL.symm k' then 1 else 0), ?_⟩
  funext i j k
  simp [map, reindex]

/-- Applying maps to a diagonal tensor gives a sum of pure tensors. -/
theorem map_diagonal [CommSemiring R] (r : ℕ)
    (A : Matrix I (Fin r) R) (B : Matrix J (Fin r) R) (C : Matrix L (Fin r) R) :
    map A B C (diagonal R r) = fun i j k => ∑ p, A i p * B j p * C k p := by
  funext i j k
  simp [map, diagonal, ite_and]

/-- Every finite coefficient tensor is a restriction of a finite diagonal
tensor. The witness uses one pure summand for each triple of basis indices. -/
theorem diagonal_restricts_coordinates [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Restricts (diagonal R (Fintype.card (I × J × L))) T := by
  classical
  let e := (Fintype.equivFin (I × J × L)).symm
  refine ⟨Matrix.of (fun i p => if i = (e p).1 then T (e p).1 (e p).2.1 (e p).2.2 else 0),
    Matrix.of (fun j p => if j = (e p).2.1 then 1 else 0),
    Matrix.of (fun k p => if k = (e p).2.2 then 1 else 0), ?_⟩
  rw [map_diagonal]
  funext i j k
  calc
    _ = ∑ p : I × J × L,
        (if i = p.1 then T p.1 p.2.1 p.2.2 else 0) *
        (if j = p.2.1 then 1 else 0) * (if k = p.2.2 then 1 else 0) :=
      e.sum_comp _
    _ = T i j k := by
      simp [Fintype.sum_prod_type, mul_ite]

/-- The admissible ranks form a nonempty set. -/
theorem exists_diagonal_restricts [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    ∃ r : ℕ, Restricts (diagonal R r) T :=
  ⟨_, diagonal_restricts_coordinates T⟩

/-- Tensor rank, defined as the least rank of a diagonal restriction source. -/
noncomputable def rank [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) : ℕ := by
  classical
  exact Nat.find (exists_diagonal_restricts T)

/-- The minimum in the definition of rank is attained. -/
theorem diagonal_restricts_of_rank [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Restricts (diagonal R (rank T)) T := by
  classical
  exact Nat.find_spec (exists_diagonal_restricts T)

/-- Any diagonal restriction gives an upper bound on rank. -/
theorem rank_le_of_diagonal_restricts [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] {T : Tensor R I J L} {r : ℕ}
    (h : Restricts (diagonal R r) T) : rank T ≤ r := by
  classical
  exact Nat.find_min' (exists_diagonal_restricts T) h

/-- Rank is bounded by the number of coefficients. -/
theorem rank_le_card [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank T ≤ Fintype.card (I × J × L) :=
  rank_le_of_diagonal_restricts (diagonal_restricts_coordinates T)

/-- Rank is monotone under restriction. -/
theorem rank_mono [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Restricts T S) :
    rank S ≤ rank T :=
  rank_le_of_diagonal_restricts ((diagonal_restricts_of_rank T).trans h)

/-- Equivalent tensors have equal rank. -/
theorem rank_eq_of_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Equivalent T S) :
    rank T = rank S :=
  le_antisymm (rank_mono h.2) (rank_mono h.1)

/-- Rank is invariant under a change of basis labels. -/
theorem rank_reindex [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor R I J L) :
    rank (reindex eI eJ eL T) = rank T := by
  apply rank_eq_of_equivalent
  constructor
  · simpa only [reindex_symm] using
      restricts_reindex eI.symm eJ.symm eL.symm (reindex eI eJ eL T)
  · exact restricts_reindex eI eJ eL T

@[simp]
theorem rank_zero [CommSemiring R] [Fintype I] [Fintype J] [Fintype L] :
    rank (0 : Tensor R I J L) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply rank_le_of_diagonal_restricts
  refine ⟨0, 0, 0, ?_⟩
  funext i j k
  simp [map]

/-- A tensor has rank zero exactly when it is zero. -/
theorem rank_eq_zero_iff [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr := diagonal_restricts_of_rank T
    rw [h] at hr
    obtain ⟨A, B, C, hmap⟩ := hr
    rw [← hmap]
    funext i j k
    simp [map]
  · rintro rfl
    exact rank_zero

/-- Every pure tensor has rank at most one. -/
theorem rank_pure_le_one [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (x : I → R) (y : J → R) (z : L → R) : rank (pure x y z) ≤ 1 := by
  apply rank_le_of_diagonal_restricts
  refine ⟨Matrix.of (fun i _ => x i), Matrix.of (fun j _ => y j),
    Matrix.of (fun k _ => z k), ?_⟩
  rw [map_diagonal]
  funext i j k
  simp [pure]

/-- A diagonal tensor is its own restriction witness. -/
theorem rank_diagonal_le [CommSemiring R] (r : ℕ) : rank (diagonal R r) ≤ r :=
  rank_le_of_diagonal_restricts (Restricts.refl _)

end MatrixMultiplication.Tensor
