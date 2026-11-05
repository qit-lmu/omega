module

public import Omega.Combinatorics.WordTypes
public import Omega.Tensor.ProductFamily

/-!
# Grouping word-indexed tensor products by symbol counts

The coordinates belonging to each symbol are grouped into a tuple of length
equal to that symbol's count. This gives explicit coordinate equivalences,
and hence tensor equivalences, between a product along a word and the product
of the corresponding tensor powers.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {H R : Type*} {n : ℕ} {I J L : H → Type*}

/-- Enumerate the positions occupied by one symbol. -/
def wordFiberIndexEquiv (w : Fin n → H) (h : H) :
    {i // w i = h} ≃ Fin (wordCounts w h) := by
  classical
  exact Fintype.equivFin _

/-- Reindex one symbol's coordinates by its numbered occurrences. -/
def wordFiberCoordinateEquiv (A : H → Type*) (w : Fin n → H) (h : H) :
    ((i : {i // w i = h}) → A (w i.1)) ≃ (Fin (wordCounts w h) → A h) :=
  (Equiv.piCongrRight (fun i => Equiv.cast (congrArg A i.2))).trans
    (Equiv.arrowCongr (wordFiberIndexEquiv w h) (Equiv.refl _))

/-- Group the dependent coordinates of a word into one tuple per symbol. -/
def wordCoordinateEquiv (A : H → Type*) (w : Fin n → H) :
    ((i : Fin n) → A (w i)) ≃ ((h : H) → Fin (wordCounts w h) → A h) :=
  Equiv.piCongrFiberwise (wordFiberCoordinateEquiv A w)

@[simp]
theorem wordCoordinateEquiv_symm_apply (A : H → Type*) (w : Fin n → H)
    (x : (h : H) → Fin (wordCounts w h) → A h) (i : Fin n) :
    (wordCoordinateEquiv A w).symm x i =
      x (w i) (wordFiberIndexEquiv w (w i) ⟨i, rfl⟩) := rfl

/-- The explicit regrouping of coordinates turns a word product into a
product of powers with the word's symbol multiplicities. -/
theorem reindex_wordProduct [CommMonoid R] [Fintype H]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (w : Fin n → H) :
    reindex (wordCoordinateEquiv I w) (wordCoordinateEquiv J w)
      (wordCoordinateEquiv L w) (tensorProductFamily (fun i => T (w i))) =
      tensorProductFamily (fun h => kroneckerPower (T h) (wordCounts w h)) := by
  classical
  funext x y z
  simp only [reindex, tensorProductFamily, kroneckerPower, wordCoordinateEquiv_symm_apply]
  rw [← Fintype.prod_fiberwise w]
  apply Finset.prod_congr rfl
  intro h _
  apply Fintype.prod_equiv (wordFiberIndexEquiv w h)
  rintro ⟨i, hi⟩
  cases hi
  rfl

/-- A word product is equivalent to the product of its grouped tensor powers. -/
theorem wordProduct_equivalent_grouped [CommSemiring R] [Fintype H] [DecidableEq H]
    [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (w : Fin n → H) :
    Equivalent (tensorProductFamily (fun i => T (w i)))
      (tensorProductFamily (fun h => kroneckerPower (T h) (wordCounts w h))) :=
  equivalent_of_reindex (wordCoordinateEquiv I w) (wordCoordinateEquiv J w)
    (wordCoordinateEquiv L w) (reindex_wordProduct T w)

/-- The same grouping with a prescribed multiplicity function. -/
def wordCoordinateEquivOfCounts (A : H → Type*) (w : Fin n → H)
    (c : H → ℕ) (hw : wordCounts w = c) :
    ((i : Fin n) → A (w i)) ≃ ((h : H) → Fin (c h) → A h) := by
  subst c
  exact wordCoordinateEquiv A w

/-- Coordinate regrouping into any prescribed counts equal to those of the word. -/
theorem reindex_wordProduct_of_counts [CommMonoid R] [Fintype H]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (w : Fin n → H)
    (c : H → ℕ) (hw : wordCounts w = c) :
    reindex (wordCoordinateEquivOfCounts I w c hw) (wordCoordinateEquivOfCounts J w c hw)
      (wordCoordinateEquivOfCounts L w c hw) (tensorProductFamily (fun i => T (w i))) =
      tensorProductFamily (fun h => kroneckerPower (T h) (c h)) := by
  subst c
  exact reindex_wordProduct T w

/-- Tensor equivalence between a word product and powers indexed by prescribed counts. -/
theorem wordProduct_equivalent_grouped_of_counts
    [CommSemiring R] [Fintype H] [DecidableEq H]
    [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (w : Fin n → H)
    (c : H → ℕ) (hw : wordCounts w = c) :
    Equivalent (tensorProductFamily (fun i => T (w i)))
      (tensorProductFamily (fun h => kroneckerPower (T h) (c h))) :=
  equivalent_of_reindex (wordCoordinateEquivOfCounts I w c hw)
    (wordCoordinateEquivOfCounts J w c hw) (wordCoordinateEquivOfCounts L w c hw)
    (reindex_wordProduct_of_counts T w c hw)

end MatrixMultiplication.Tensor
