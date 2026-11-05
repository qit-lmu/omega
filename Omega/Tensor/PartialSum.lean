module

public import Omega.Tensor.Basic
public import Mathlib.Data.Fintype.Sigma

/-!
# Finite families of partial and ordinary direct sums

The summands may have different second and third coordinate spaces. In a
partial sum the first coordinate space is shared; in an ordinary direct sum
all three coordinate spaces are separated by the block label.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R H I : Type*} {J L : H → Type*}

/-- A family of tensors with a common first factor, with the other two factors
separated by their labels. -/
def partialSumFamily [Zero R] [DecidableEq H]
    (T : ∀ h, Tensor R I (J h) (L h)) : Tensor R I (Sigma J) (Sigma L) :=
  fun i j k => if h : j.1 = k.1 then T j.1 i j.2 (h.symm ▸ k.2) else 0

/-- The ordinary direct sum of a dependent family of coefficient tensors. -/
def directSumFamily [Zero R] [DecidableEq H] {I : H → Type*}
    (T : ∀ h, Tensor R (I h) (J h) (L h)) :
    Tensor R (Sigma I) (Sigma J) (Sigma L) :=
  fun i j k => if h : i.1 = j.1 then
    if g : i.1 = k.1 then T i.1 i.2 (h.symm ▸ j.2) (g.symm ▸ k.2) else 0
    else 0

@[simp]
theorem partialSumFamily_same [Zero R] [DecidableEq H]
    (T : ∀ h, Tensor R I (J h) (L h)) (h : H) (i : I) (j : J h) (k : L h) :
    partialSumFamily T i ⟨h, j⟩ ⟨h, k⟩ = T h i j k := by
  simp [partialSumFamily]

@[simp]
theorem partialSumFamily_ne [Zero R] [DecidableEq H]
    (T : ∀ h, Tensor R I (J h) (L h)) (i : I) (j : Sigma J) (k : Sigma L)
    (h : j.1 ≠ k.1) : partialSumFamily T i j k = 0 := by
  simp [partialSumFamily, h]

@[simp]
theorem directSumFamily_same [Zero R] [DecidableEq H] {I : H → Type*}
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (h : H)
    (i : I h) (j : J h) (k : L h) :
    directSumFamily T ⟨h, i⟩ ⟨h, j⟩ ⟨h, k⟩ = T h i j k := by
  simp [directSumFamily]

@[simp]
theorem directSumFamily_ne_first_second [Zero R] [DecidableEq H] {I : H → Type*}
    (T : ∀ h, Tensor R (I h) (J h) (L h))
    (i : Sigma I) (j : Sigma J) (k : Sigma L) (h : i.1 ≠ j.1) :
    directSumFamily T i j k = 0 := by
  simp [directSumFamily, h]

@[simp]
theorem directSumFamily_ne_first_third [Zero R] [DecidableEq H] {I : H → Type*}
    (T : ∀ h, Tensor R (I h) (J h) (L h))
    (i : Sigma I) (j : Sigma J) (k : Sigma L) (h : i.1 ≠ k.1) :
    directSumFamily T i j k = 0 := by
  simp [directSumFamily, h]

/-- Projection to one partial-sum block leaves the common first factor fixed. -/
theorem partialSumFamily_restricts_block [CommSemiring R] [Fintype H] [DecidableEq H]
    [Fintype I] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R I (J h) (L h)) (h : H) :
    Restricts (partialSumFamily T) (T h) := by
  classical
  refine ⟨1, Matrix.of (fun j y => if y = Sigma.mk h j then 1 else 0),
    Matrix.of (fun k z => if z = Sigma.mk h k then 1 else 0), ?_⟩
  funext i j k
  simp [map, Matrix.of_apply, Matrix.one_apply]

/-- Projection onto a block of an ordinary direct sum. -/
theorem directSumFamily_restricts_block [CommSemiring R] [Fintype H] [DecidableEq H]
    {I : H → Type*} [∀ h, Fintype (I h)] [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R (I h) (J h) (L h)) (h : H) :
    Restricts (directSumFamily T) (T h) := by
  classical
  refine ⟨Matrix.of (fun i x => if x = Sigma.mk h i then 1 else 0),
    Matrix.of (fun j y => if y = Sigma.mk h j then 1 else 0),
    Matrix.of (fun k z => if z = Sigma.mk h k then 1 else 0), ?_⟩
  funext i j k
  simp [map, Matrix.of_apply]

end MatrixMultiplication.Tensor
