module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Extending a rank-preserving matrix action

If a square matrix preserves the rank of a rectangular matrix when acting
on the left, its action on that matrix can be realized by an invertible
matrix. The proof extends the induced isomorphism of column spaces to an
automorphism of the ambient vector space. No field-size assumption is needed.
-/

@[expose] public section

namespace MatrixMultiplication

open Module
open scoped Matrix

/-- An endomorphism preserving the dimension of an image can be replaced by
an automorphism with the same action on that image. -/
theorem exists_linearEquiv_comp_eq_of_finrank_range_eq
    {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] V) (g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f.comp g)) = finrank K (LinearMap.range g)) :
    ∃ e : V ≃ₗ[K] V, ∀ w, e (g w) = f (g w) := by
  let p := LinearMap.range g
  let q := LinearMap.range (f.comp g)
  let f' : p →ₗ[K] q := LinearMap.codRestrict q (f.comp p.subtype) (by
    rintro ⟨v, w, rfl⟩
    exact ⟨w, rfl⟩)
  have hsurj : Function.Surjective f' := by
    rintro ⟨v, w, rfl⟩
    exact ⟨⟨g w, ⟨w, rfl⟩⟩, rfl⟩
  have hinj : Function.Injective f' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).mpr hsurj
  let e := LinearEquiv.ofBijective f' ⟨hinj, hsurj⟩
  obtain ⟨e', he'⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨e', fun w => ?_⟩
  exact (he' ⟨g w, ⟨w, rfl⟩⟩).symm

/-- A square matrix that preserves the rank of `M` can be replaced by a
unit matrix with exactly the same product with `M`. Empty shapes are allowed. -/
theorem matrix_exists_unit_mul_eq_of_rank_eq
    {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I]
    (A : Matrix I I K) (M : Matrix I J K) (h : (A * M).rank = M.rank) :
    ∃ U : (Matrix I I K)ˣ, (U : Matrix I I K) * M = A * M := by
  obtain ⟨e, he⟩ := exists_linearEquiv_comp_eq_of_finrank_range_eq
    A.mulVecLin M.mulVecLin (by
      change finrank K (LinearMap.range (A * M).mulVecLin) =
        finrank K (LinearMap.range M.mulVecLin) at h
      rwa [Matrix.mulVecLin_mul] at h)
  let U : (Matrix I I K)ˣ := {
    val := LinearMap.toMatrix' e.toLinearMap
    inv := LinearMap.toMatrix' e.symm.toLinearMap
    val_inv := by rw [← LinearMap.toMatrix'_comp]; simp
    inv_val := by rw [← LinearMap.toMatrix'_comp]; simp }
  refine ⟨U, ?_⟩
  apply Matrix.mulVec_injective
  funext v
  change (LinearMap.toMatrix' e.toLinearMap * M) *ᵥ v = (A * M) *ᵥ v
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, ← Matrix.mulVec_mulVec]
  exact he v

end MatrixMultiplication
