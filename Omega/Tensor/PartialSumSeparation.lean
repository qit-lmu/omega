module

public import Omega.Tensor.PartialSum
public import Omega.Tensor.MonomialDegeneration
public import Omega.Tensor.PolynomialDegeneration
public import Omega.Tensor.DirectSumCopies
import Mathlib.Tactic.Linarith

/-!
# Separating a partial direct sum by polynomial multiplication

The monomial weights are the shifted nonnegative version of the weights in
the manuscript's partial-sum separation lemma. Their excess on a supported
coefficient is the square of the difference of its two block labels.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

private theorem separation_weight_lower
    (i h j q D : ℕ) (hbound : 2 * h * (h + q) ≤ D) (hsupport : i + j = h + q) :
    D ≤ i ^ 2 + (h ^ 2 + 2 * h * j) + (D - 2 * h * (h + q)) := by
  have hsub := Nat.sub_add_cancel hbound
  have hrel := congrArg (fun x => 2 * h * x) hsupport
  have hsq : 2 * i * h ≤ i ^ 2 + h ^ 2 := by
    have hh := sq_nonneg ((i : ℤ) - h)
    nlinarith
  nlinarith

private theorem separation_weight_eq_iff
    (i h j q D : ℕ) (hbound : 2 * h * (h + q) ≤ D) (hsupport : i + j = h + q) :
    i ^ 2 + (h ^ 2 + 2 * h * j) + (D - 2 * h * (h + q)) = D ↔ i = h := by
  have hsub := Nat.sub_add_cancel hbound
  have hrel := congrArg (fun x => 2 * h * x) hsupport
  constructor
  · intro heq
    have hh : (i : ℤ) = h := by nlinarith [sq_nonneg ((i : ℤ) - h)]
    exact_mod_cast hh
  · intro heq
    subst i
    nlinarith

/-- Polynomial multiplication separates every block of a partial sum. The
construction uses only monomial factor maps and works over any commutative
semiring; no assumption on the size or characteristic of the scalars occurs. -/
theorem partialSumFamily_kronecker_polynomialMul_degenerates
    {R H I : Type*} [CommSemiring R] [Fintype H] [DecidableEq H] [Fintype I]
    {J L : H → Type*} [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor R I (J h) (L h)) (r : ℕ) :
    Degenerates
      (kronecker (partialSumFamily T) (polynomialMul R (Fintype.card H) r))
      (kronecker (directSumFamily T) (matrixMul R 1 1 r)) := by
  classical
  let m := Fintype.card H
  let e := Fintype.equivFin H
  let D := 2 * m * (m + r)
  let outputIndex (h : H) (q : Fin r) : Fin (m + r - 1) :=
    ⟨(e h).val + q.val, by have hh := (e h).isLt; have hq := q.isLt; omega⟩
  have hb (h : H) (q : Fin r) : 2 * (e h).val * ((e h).val + q.val) ≤ D := by
    dsimp only [D]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (e h).isLt.le)
      (Nat.add_le_add (e h).isLt.le q.isLt.le)
  apply degenerates_of_monomial_pullback
    (f := fun x => (x.1.2, e x.1.1))
    (g := fun y => (y.1, y.2.2))
    (h := fun z => (z.1, outputIndex z.1.1 z.2.2))
    (a := fun x => (e x.1.1).val ^ 2)
    (b := fun y => (e y.1.1).val ^ 2 + 2 * (e y.1.1).val * y.2.2.val)
    (c := fun z => D - 2 * (e z.1.1).val * ((e z.1.1).val + z.2.2.val))
    (d := D)
  · intro x y z hlow
    by_cases htag : y.1.1 = z.1.1
    · by_cases hs : (e x.1.1).val + y.2.2.val = (e z.1.1).val + z.2.2.val
      · have hw := separation_weight_lower (e x.1.1).val (e z.1.1).val
          y.2.2.val z.2.2.val D (hb _ _) hs
        simp only [htag] at hlow
        omega
      · simp [kronecker, polynomialMul, outputIndex, hs]
    · simp [kronecker, partialSumFamily, htag]
  · intro x y z
    by_cases htag : y.1.1 = z.1.1
    · by_cases hs : (e x.1.1).val + y.2.2.val = (e z.1.1).val + z.2.2.val
      · have hw := separation_weight_eq_iff (e x.1.1).val (e z.1.1).val
          y.2.2.val z.2.2.val D (hb _ _) hs
        have hei : (e x.1.1).val = (e z.1.1).val ↔ x.1.1 = z.1.1 :=
          ⟨fun hh => e.injective (Fin.ext hh), fun hh => congrArg (fun h => (e h).val) hh⟩
        by_cases hx : x.1.1 = z.1.1
        · have hxy : x.1.1 = y.1.1 := hx.trans htag.symm
          have hjq : y.2.2 = z.2.2 := Fin.ext (by simpa [hx] using hs)
          have heq : (e x.1.1).val ^ 2 +
              ((e y.1.1).val ^ 2 + 2 * (e y.1.1).val * y.2.2.val) +
              (D - 2 * (e z.1.1).val * ((e z.1.1).val + z.2.2.val)) = D := by
            simpa only [htag] using hw.mpr (hei.mpr hx)
          have hmat : matrixMul R 1 1 r x.2 y.2 z.2 = 1 := by
            simp [matrixMul, Subsingleton.elim x.2.1 z.2.1,
              Subsingleton.elim x.2.2 y.2.1, hjq]
          have hcoeff : directSumFamily T x.1 y.1 z.1 =
              partialSumFamily T x.1.2 y.1 z.1 := by
            rcases x with ⟨⟨a, i⟩, u⟩
            rcases y with ⟨⟨b, j⟩, v⟩
            rcases z with ⟨⟨c, k⟩, w⟩
            dsimp only at hxy hx
            subst b
            subst c
            simp
          rw [ite_eq_left heq]
          simpa only [kronecker, hmat, polynomialMul, outputIndex, hs, ite_eq_left,
            mul_one] using hcoeff
        · simp [kronecker, directSumFamily, htag, hw, hei, hx]
      · have ht : kronecker (directSumFamily T) (matrixMul R 1 1 r) x y z = 0 := by
          by_cases hx : x.1.1 = z.1.1
          · have hjq : y.2.2 ≠ z.2.2 := by intro he; exact hs (by simp [hx, he])
            simp [kronecker, matrixMul, hjq]
          · simp [kronecker, directSumFamily, hx]
        rw [ht]
        simp [kronecker, polynomialMul, outputIndex, hs]
    · have ht : directSumFamily T x.1 y.1 z.1 = 0 := by
        by_cases hxy : x.1.1 = y.1.1
        · have hxz : x.1.1 ≠ z.1.1 := fun hx => htag (hxy.symm.trans hx)
          simp only [directSumFamily, dite_eq_left hxy, dite_eq_right hxz]
        · simp [directSumFamily, hxy]
      simp [kronecker, ht, partialSumFamily, htag]

/-- The partial-sum separation lemma, over every field and for every finite
dependent family. The harmless empty-family and zero auxiliary-size cases
are included. This is `lem:diamond-plus-deg` in the manuscript. -/
theorem partialSumFamily_separation
    {K H I : Type*} [Field K] [Fintype H] [DecidableEq H] [Fintype I]
    {J L : H → Type*} [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]
    (T : ∀ h, Tensor K I (J h) (L h)) (r : ℕ) :
    Degenerates (directSumCopies (partialSumFamily T) (Fintype.card H + r - 1))
      (kronecker (directSumFamily T) (matrixMul K 1 1 r)) := by
  have hreindex : reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
      (Equiv.prodComm _ _) (directSumCopies (partialSumFamily T) (Fintype.card H + r - 1)) =
      kronecker (partialSumFamily T) (diagonal K (Fintype.card H + r - 1)) := by
    funext i j k
    simp [reindex, directSumCopies, kronecker, mul_comm]
  have hswap : Restricts
      (directSumCopies (partialSumFamily T) (Fintype.card H + r - 1))
      (kronecker (partialSumFamily T) (diagonal K (Fintype.card H + r - 1))) := by
    rw [← hreindex]
    exact restricts_reindex _ _ _ _
  exact hswap.degenerates.trans
    (((Degenerates.refl (partialSumFamily T)).kronecker
      (diagonal_degenerates_polynomialMul K (Fintype.card H) r)).trans
      (partialSumFamily_kronecker_polynomialMul_degenerates T r))

end MatrixMultiplication.Tensor
