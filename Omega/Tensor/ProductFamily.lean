module

public import Omega.Tensor.ValueOperations
public import Omega.ValueMultiplicativity
public import Omega.ValueMonotonicity
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Products of a finite family of tensors

The coordinate types may depend on the factor. Reindexing the factors gives
coordinate equivalences, and fractional value is supermultiplicative for such
finite products, including the empty product in the admissible interval.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R H G : Type*} {I J L : H → Type*} {I' J' L' : G → Type*}

/-- The Kronecker product of a finite dependent family, with coordinates grouped. -/
def tensorProductFamily [CommMonoid R] [Fintype H]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) :
    Tensor R (∀ h, I h) (∀ h, J h) (∀ h, L h) :=
  fun i j k => ∏ h, T h (i h) (j h) (k h)

/-- Reordering the factors and changing bases in each factor preserves the product. -/
theorem tensorProductFamily_reindex [CommMonoid R] [Fintype H] [Fintype G]
    (e : H ≃ G) (ei : ∀ h, I h ≃ I' (e h))
    (ej : ∀ h, J h ≃ J' (e h)) (el : ∀ h, L h ≃ L' (e h))
    (T : ∀ h, Tensor R (I h) (J h) (L h))
    (S : ∀ g, Tensor R (I' g) (J' g) (L' g))
    (h : ∀ a i j k, T a i j k = S (e a) (ei a i) (ej a j) (el a k)) :
    reindex (e.piCongr ei) (e.piCongr ej) (e.piCongr el) (tensorProductFamily T) =
      tensorProductFamily S := by
  funext i j k
  simp only [reindex, tensorProductFamily, Equiv.piCongr_symm_apply]
  apply Fintype.prod_equiv e
  intro a
  simp [h]

/-- A factor reindexing is a tensor equivalence. -/
theorem tensorProductFamily_comp_equivalent [CommSemiring R] [Fintype H] [Fintype G]
    [DecidableEq H] [DecidableEq G]
    [∀ g, Fintype (I' g)] [∀ g, Fintype (J' g)] [∀ g, Fintype (L' g)]
    (e : H ≃ G) (T : ∀ g, Tensor R (I' g) (J' g) (L' g)) :
    Equivalent (tensorProductFamily (fun h => T (e h))) (tensorProductFamily T) := by
  apply equivalent_of_reindex (e.piCongr fun h => Equiv.refl (I' (e h)))
    (e.piCongr fun h => Equiv.refl (J' (e h)))
    (e.piCongr fun h => Equiv.refl (L' (e h)))
  exact tensorProductFamily_reindex e (fun _ => Equiv.refl _)
    (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) _ T (fun _ _ _ _ => rfl)

/-- Splitting off the first factor of a finite product. -/
theorem tensorProductFamily_fin_succ_equivalent [CommSemiring R] {n : ℕ}
    {A B C : Fin (n + 1) → Type*}
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    (T : ∀ h, Tensor R (A h) (B h) (C h)) :
    Equivalent (tensorProductFamily T)
      (kronecker (T 0) (tensorProductFamily (fun h : Fin n => T h.succ))) := by
  apply equivalent_of_reindex (Fin.consEquiv A).symm (Fin.consEquiv B).symm
    (Fin.consEquiv C).symm
  funext i j k
  simp [reindex, tensorProductFamily, kronecker, Fin.prod_univ_succ, Fin.consEquiv]

/-- The empty dependent product is the unit diagonal. -/
theorem tensorProductFamily_fin_zero_equivalent [CommSemiring R]
    {A B C : Fin 0 → Type*}
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    (T : ∀ h, Tensor R (A h) (B h) (C h)) :
    Equivalent (tensorProductFamily T) (diagonal R 1) := by
  apply equivalent_of_reindex (Equiv.ofUnique _ _) (Equiv.ofUnique _ _)
    (Equiv.ofUnique _ _)
  funext i j k
  simp [reindex, tensorProductFamily, diagonal, Subsingleton.elim i j, Subsingleton.elim j k]

open scoped ENNReal

private theorem fractionalValue_tensorProductFamily_fin_ge {K : Type*} [Field K]
    (n : ℕ) {A B C : Fin n → Type*}
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    (T : ∀ h, Tensor K (A h) (B h) (C h)) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∏ h, fractionalValue (T h) τ) ≤ fractionalValue (tensorProductFamily T) τ := by
  induction n with
  | zero =>
      rw [fractionalValue_eq_of_equivalent (tensorProductFamily_fin_zero_equivalent T) τ,
        fractionalValue_unit hτ hτω]
      simp
  | succ n ih =>
      rw [Fin.prod_univ_succ,
        fractionalValue_eq_of_equivalent (tensorProductFamily_fin_succ_equivalent T) τ]
      exact (mul_le_mul' le_rfl (ih (fun h => T h.succ))).trans
        (fractionalValue_kronecker_ge _ _ τ)

/-- Fractional value is supermultiplicative for any finite dependent tensor family. -/
theorem fractionalValue_tensorProductFamily_ge {K : Type*} [Field K] [Fintype H]
    [DecidableEq H]
    [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor K (I h) (J h) (L h)) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    (∏ h, fractionalValue (T h) τ) ≤ fractionalValue (tensorProductFamily T) τ := by
  classical
  let e := (Fintype.equivFin H).symm
  have h := fractionalValue_tensorProductFamily_fin_ge (Fintype.card H)
    (fun i => T (e i)) hτ hτω
  rw [fractionalValue_eq_of_equivalent (tensorProductFamily_comp_equivalent e T) τ] at h
  rwa [Fintype.prod_equiv e (fun i => fractionalValue (T (e i)) τ)
    (fun h => fractionalValue (T h) τ) (fun _ => rfl)] at h

end MatrixMultiplication.Tensor
