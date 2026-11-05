module

public import Omega.Tensor.PartialSum
public import Omega.Tensor.DirectSumCopies
public import Omega.Tensor.FactorPermutations
public import Mathlib.Data.Matrix.Block

/-!
# Coordinate operations on finite direct sums

Independent maps in every block induce block-diagonal maps on the ordinary
direct sum. In particular, a family of equivalent blocks is equivalent to
the corresponding number of copies of any one representative.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R H : Type*} [CommSemiring R] [Fintype H] [DecidableEq H]
variable {I J L I' J' L' : H → Type*}
variable [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]

set_option backward.isDefEq.respectTransparency false in
/-- Mapping each block separately commutes with an ordinary direct sum. -/
theorem map_directSumFamily
    (A : ∀ h, Matrix (I' h) (I h) R) (B : ∀ h, Matrix (J' h) (J h) R)
    (C : ∀ h, Matrix (L' h) (L h) R) (T : ∀ h, Tensor R (I h) (J h) (L h)) :
    map (Matrix.blockDiagonal' A) (Matrix.blockDiagonal' B) (Matrix.blockDiagonal' C)
      (directSumFamily T) = directSumFamily (fun h => map (A h) (B h) (C h) (T h)) := by
  classical
  funext ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩
  simp only [map, Fintype.sum_sigma, Matrix.blockDiagonal'_apply',
    dite_mul, mul_dite, zero_mul, mul_zero, Finset.sum_dite_irrel,
    Finset.sum_const_zero, Finset.sum_dite_eq, Finset.mem_univ]
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [directSumFamily, map]
    · simp [directSumFamily, hac]
  · simp [directSumFamily, hab]

/-- Ordinary direct sums preserve an independent restriction in every block. -/
theorem Restricts.directSumFamily
    {T : ∀ h, Tensor R (I h) (J h) (L h)}
    {S : ∀ h, Tensor R (I' h) (J' h) (L' h)}
    (h : ∀ a, Restricts (T a) (S a)) :
    Restricts (directSumFamily T) (directSumFamily S) := by
  classical
  choose A B C hmaps using h
  refine ⟨Matrix.blockDiagonal' A, Matrix.blockDiagonal' B, Matrix.blockDiagonal' C, ?_⟩
  rw [map_directSumFamily]
  congr 1
  funext a
  exact hmaps a

/-- Ordinary direct sums preserve an independent equivalence in every block. -/
theorem Equivalent.directSumFamily
    [∀ h, Fintype (I' h)] [∀ h, Fintype (J' h)] [∀ h, Fintype (L' h)]
    {T : ∀ h, Tensor R (I h) (J h) (L h)}
    {S : ∀ h, Tensor R (I' h) (J' h) (L' h)}
    (h : ∀ a, Equivalent (T a) (S a)) :
    Equivalent (directSumFamily T) (directSumFamily S) :=
  ⟨Restricts.directSumFamily (fun a => (h a).1),
    Restricts.directSumFamily (fun a => (h a).2)⟩

omit [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)] in
/-- A constant family is the usual repeated direct sum. -/
theorem directSumFamily_const_equivalent_copies
    {I J L : Type*} [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (directSumFamily (fun _ : H => T)) (directSumCopies T (Fintype.card H)) := by
  classical
  let eI := (Equiv.sigmaEquivProd H I).trans ((Fintype.equivFin H).prodCongr (Equiv.refl I))
  let eJ := (Equiv.sigmaEquivProd H J).trans ((Fintype.equivFin H).prodCongr (Equiv.refl J))
  let eL := (Equiv.sigmaEquivProd H L).trans ((Fintype.equivFin H).prodCongr (Equiv.refl L))
  apply equivalent_of_reindex eI eJ eL
  funext ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [reindex, eI, eJ, eL, directSumFamily, directSumCopies, kronecker, diagonal]
    · simp [reindex, eI, eJ, eL, directSumFamily, directSumCopies, kronecker, diagonal, hac]
  · simp [reindex, eI, eJ, directSumFamily, directSumCopies, kronecker, diagonal, hab]

/-- Equivalent blocks can be replaced by repeated copies of one tensor. -/
theorem directSumFamily_equivalent_copies
    {I' J' L' : Type*} [Fintype I'] [Fintype J'] [Fintype L']
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (S : Tensor R I' J' L')
    (h : ∀ a, Equivalent (T a) S) :
    Equivalent (directSumFamily T) (directSumCopies S (Fintype.card H)) :=
  (Equivalent.directSumFamily h).trans (directSumFamily_const_equivalent_copies S)

end MatrixMultiplication.Tensor
