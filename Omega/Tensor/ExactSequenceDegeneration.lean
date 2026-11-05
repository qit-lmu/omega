module

public import Omega.Tensor.SplitDegeneration
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degeneration from compatible linear maps and quotient bilinear maps

Structure tensors of bilinear maps are written in arbitrary finite bases.
An input section and an output retraction supply the three block identities
needed for the split-map degeneration. These maps are constructed from
surjectivity and injectivity, rather than assumed as additional data.
The quotient case constructs the induced bilinear map, proves its uniqueness,
and specializes the degeneration to the actual quotients by the two ranges.
-/

@[expose] public section

open Module

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]
variable {U V W V' W' : Type*}
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup V'] [Module K V']
variable [AddCommGroup W'] [Module K W']
variable {I J L J' L' : Type*}

/-- Coefficients of a bilinear map in three chosen bases. The first two
coordinates are dual coordinates; the third is an output coordinate. -/
noncomputable def structureTensor (bU : Basis I K U) (bV : Basis J K V)
    (bW : Basis L K W) (φ : U →ₗ[K] V →ₗ[K] W) : Tensor K I J L :=
  fun i j k => bW.repr (φ (bU i) (bV j)) k

private theorem sum_repr_linearMap [Fintype L]
    (bW : Basis L K W) (bW' : Basis L' K W') (C : W →ₗ[K] W')
    (w : W) (k' : L') :
    (∑ k, bW.repr w k * bW'.repr (C (bW k)) k') = bW'.repr (C w) k' := by
  have h := congrArg (fun x : W => bW'.repr (C x) k') (bW.sum_repr w)
  simpa only [_root_.map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul] using h

/-- Input precomposition acts on dual coordinates; output postcomposition
acts on output coordinates. The common first factor is unchanged. -/
theorem map_structureTensor [Fintype I] [Fintype J] [Fintype L] [DecidableEq I]
    (bU : Basis I K U) (bV : Basis J K V) (bW : Basis L K W)
    (bV' : Basis J' K V') (bW' : Basis L' K W')
    (φ : U →ₗ[K] V →ₗ[K] W) (B : V' →ₗ[K] V) (C : W →ₗ[K] W') :
    map (1 : Matrix I I K)
      (fun j' j => bV.repr (B (bV' j')) j)
      (fun k' k => bW'.repr (C (bW k)) k')
      (structureTensor bU bV bW φ) =
      fun i j k => bW'.repr (C (φ (bU i) (B (bV' j)))) k := by
  classical
  funext i j' k'
  simp only [map, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, structureTensor]
  calc
    _ = ∑ j, bV.repr (B (bV' j')) j *
        bW'.repr (C (φ (bU i) (bV j))) k' := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_repr_linearMap bW bW' C]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = bW'.repr (C (φ (bU i) (B (bV' j')))) k' := by
      have h := congrArg (fun v : V => bW'.repr (C (φ (bU i) v)) k')
        (bV.sum_repr (B (bV' j')))
      simpa only [_root_.map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        smul_eq_mul] using h

section CompatibleMaps

variable {V₀ V₁ W₀ W₁ : Type*}
variable [AddCommGroup V₀] [Module K V₀] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup W₀] [Module K W₀] [AddCommGroup W₁] [Module K W₁]
variable {J₀ J₁ L₀ L₁ : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype J₀] [Fintype J₁] [Fintype L₀] [Fintype L₁]

/-- Manuscript Lemma 5.1: only an injective
output inclusion, a surjective input quotient, and the zero composite on the
output side are needed, together with compatibility of the bilinear maps. -/
theorem degenerates_partialSum_of_compatible_maps
    (bU : Basis I K U) (bV : Basis J K V) (bW : Basis L K W)
    (bV₀ : Basis J₀ K V₀) (bV₁ : Basis J₁ K V₁)
    (bW₀ : Basis L₀ K W₀) (bW₁ : Basis L₁ K W₁)
    (ιV : V₀ →ₗ[K] V) (πV : V →ₗ[K] V₁)
    (ιW : W₀ →ₗ[K] W) (πW : W →ₗ[K] W₁)
    (hιW : Function.Injective ιW) (hπV : Function.Surjective πV)
    (hW : ∀ w, πW (ιW w) = 0)
    (φ : U →ₗ[K] V →ₗ[K] W)
    (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀) (φ₁ : U →ₗ[K] V₁ →ₗ[K] W₁)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v))
    (h₁ : ∀ u v, φ₁ u (πV v) = πW (φ u v)) :
    Degenerates (structureTensor bU bV bW φ)
      (partialSum (structureTensor bU bV₀ bW₀ φ₀)
        (structureTensor bU bV₁ bW₁ φ₁)) := by
  classical
  obtain ⟨r, hr⟩ := ιW.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hιW)
  obtain ⟨s, hs⟩ := πV.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπV)
  have hr' : ∀ w, r (ιW w) = w := fun w => LinearMap.congr_fun hr w
  have hs' : ∀ v, πV (s v) = v := fun v => LinearMap.congr_fun hs v
  apply degenerates_partialSum_of_split_maps _ _ _
    (fun j₀ j => bV.repr (ιV (bV₀ j₀)) j)
    (fun j₁ j => bV.repr (s (bV₁ j₁)) j)
    (fun k₀ k => bW₀.repr (r (bW k)) k₀)
    (fun k₁ k => bW₁.repr (πW (bW k)) k₁)
  · rw [map_structureTensor]
    funext i j k
    simp only [structureTensor, h₀, hr']
  · rw [map_structureTensor]
    funext i j k
    simp only [h₀, hW, _root_.map_zero, Finsupp.zero_apply, Pi.zero_apply]
  · rw [map_structureTensor]
    funext i j k
    simp only [structureTensor, ← h₁, hs']

/-- The short-exact-sequence specialization of Lemma 5.1 yields a degeneration to the
partially direct sum of the subobject and quotient structure tensors.
The bases are arbitrary, and the same basis of `U` is used in both blocks. -/
theorem degenerates_partialSum_of_exact
    (bU : Basis I K U) (bV : Basis J K V) (bW : Basis L K W)
    (bV₀ : Basis J₀ K V₀) (bV₁ : Basis J₁ K V₁)
    (bW₀ : Basis L₀ K W₀) (bW₁ : Basis L₁ K W₁)
    (ιV : V₀ →ₗ[K] V) (πV : V →ₗ[K] V₁)
    (ιW : W₀ →ₗ[K] W) (πW : W →ₗ[K] W₁)
    (_hιV : Function.Injective ιV) (_hV : Function.Exact ιV πV)
    (hπV : Function.Surjective πV)
    (hιW : Function.Injective ιW) (hW : Function.Exact ιW πW)
    (_hπW : Function.Surjective πW)
    (φ : U →ₗ[K] V →ₗ[K] W)
    (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀) (φ₁ : U →ₗ[K] V₁ →ₗ[K] W₁)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v))
    (h₁ : ∀ u v, φ₁ u (πV v) = πW (φ u v)) :
    Degenerates (structureTensor bU bV bW φ)
      (partialSum (structureTensor bU bV₀ bW₀ φ₀)
        (structureTensor bU bV₁ bW₁ φ₁)) := by
  apply degenerates_partialSum_of_compatible_maps bU bV bW bV₀ bV₁ bW₀ bW₁
    ιV πV ιW πW hιW hπV (fun w => congrFun hW.comp_eq_zero w) φ φ₀ φ₁ h₀ h₁

end CompatibleMaps

section QuotientMaps

variable {V₀ W₀ : Type*}
variable [AddCommGroup V₀] [Module K V₀] [AddCommGroup W₀] [Module K W₀]

/-- The bilinear map on the quotients by the input and output ranges.
The first compatibility identity makes the representative formula well defined. -/
noncomputable def quotientBilinearMap
    (ιV : V₀ →ₗ[K] V) (ιW : W₀ →ₗ[K] W)
    (φ : U →ₗ[K] V →ₗ[K] W) (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v)) :
    U →ₗ[K] (V ⧸ LinearMap.range ιV) →ₗ[K] (W ⧸ LinearMap.range ιW) where
  toFun u := (LinearMap.range ιV).mapQ (LinearMap.range ιW) (φ u) (by
    rintro _ ⟨v, rfl⟩
    exact ⟨φ₀ u v, (h₀ u v).symm⟩)
  map_add' u u' := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (LinearMap.range ιV).mkQ_surjective q
    change (LinearMap.range ιW).mkQ (φ (u + u') v) =
      (LinearMap.range ιW).mkQ (φ u v) + (LinearMap.range ιW).mkQ (φ u' v)
    rw [_root_.map_add, LinearMap.add_apply, _root_.map_add]
  map_smul' a u := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (LinearMap.range ιV).mkQ_surjective q
    change (LinearMap.range ιW).mkQ (φ (a • u) v) =
      a • (LinearMap.range ιW).mkQ (φ u v)
    simp only [_root_.map_smul, LinearMap.smul_apply]

/-- The induced quotient map sends `(u, [v])` to `[φ u v]`. -/
@[simp]
theorem quotientBilinearMap_mkQ
    (ιV : V₀ →ₗ[K] V) (ιW : W₀ →ₗ[K] W)
    (φ : U →ₗ[K] V →ₗ[K] W) (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v)) (u : U) (v : V) :
    quotientBilinearMap ιV ιW φ φ₀ h₀ u ((LinearMap.range ιV).mkQ v) =
      (LinearMap.range ιW).mkQ (φ u v) := rfl

/-- The second compatibility identity uniquely determines the quotient bilinear map. -/
theorem quotientBilinearMap_unique
    (ιV : V₀ →ₗ[K] V) (ιW : W₀ →ₗ[K] W)
    (φ : U →ₗ[K] V →ₗ[K] W) (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v))
    (ψ : U →ₗ[K] (V ⧸ LinearMap.range ιV) →ₗ[K] (W ⧸ LinearMap.range ιW))
    (hψ : ∀ u v, ψ u ((LinearMap.range ιV).mkQ v) =
      (LinearMap.range ιW).mkQ (φ u v)) :
    ψ = quotientBilinearMap ιV ιW φ φ₀ h₀ := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := (LinearMap.range ιV).mkQ_surjective q
  exact hψ u v

/-- Existence and uniqueness of the quotient map in manuscript Remark 5.2. -/
theorem existsUnique_quotientBilinearMap
    (ιV : V₀ →ₗ[K] V) (ιW : W₀ →ₗ[K] W)
    (φ : U →ₗ[K] V →ₗ[K] W) (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v)) :
    ∃! ψ : U →ₗ[K] (V ⧸ LinearMap.range ιV) →ₗ[K] (W ⧸ LinearMap.range ιW),
      ∀ u v, ψ u ((LinearMap.range ιV).mkQ v) =
        (LinearMap.range ιW).mkQ (φ u v) :=
  ⟨quotientBilinearMap ιV ιW φ φ₀ h₀, quotientBilinearMap_mkQ ιV ιW φ φ₀ h₀,
    fun ψ hψ => quotientBilinearMap_unique ιV ιW φ φ₀ h₀ ψ hψ⟩

/-- Remark 5.2: compatible subobject maps give a degeneration to their
structure tensor and the induced quotient structure tensor. -/
theorem degenerates_partialSum_quotient
    {J₀ J₁ L₀ L₁ : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype J₀] [Fintype J₁] [Fintype L₀] [Fintype L₁]
    (ιV : V₀ →ₗ[K] V) (ιW : W₀ →ₗ[K] W) (hιW : Function.Injective ιW)
    (bU : Basis I K U) (bV : Basis J K V) (bW : Basis L K W)
    (bV₀ : Basis J₀ K V₀) (bV₁ : Basis J₁ K (V ⧸ LinearMap.range ιV))
    (bW₀ : Basis L₀ K W₀) (bW₁ : Basis L₁ K (W ⧸ LinearMap.range ιW))
    (φ : U →ₗ[K] V →ₗ[K] W) (φ₀ : U →ₗ[K] V₀ →ₗ[K] W₀)
    (h₀ : ∀ u v, φ u (ιV v) = ιW (φ₀ u v)) :
    Degenerates (structureTensor bU bV bW φ)
      (partialSum (structureTensor bU bV₀ bW₀ φ₀)
        (structureTensor bU bV₁ bW₁ (quotientBilinearMap ιV ιW φ φ₀ h₀))) := by
  apply degenerates_partialSum_of_compatible_maps bU bV bW bV₀ bV₁ bW₀ bW₁
    ιV (LinearMap.range ιV).mkQ ιW (LinearMap.range ιW).mkQ hιW
    (LinearMap.range ιV).mkQ_surjective
    (fun w => LinearMap.congr_fun (LinearMap.range_mkQ_comp ιW) w)
    φ φ₀ (quotientBilinearMap ιV ιW φ φ₀ h₀) h₀
    (quotientBilinearMap_mkQ ιV ιW φ φ₀ h₀)

end QuotientMaps

end MatrixMultiplication.Tensor
