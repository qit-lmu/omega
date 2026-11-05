module

public import Omega.Tensor.PartialSumPowers
public import Omega.Tensor.PartialSumOperations
public import Omega.Tensor.PartialSumSeparation
public import Omega.Tensor.WordProducts

/-!
# Separation of a multinomial type class

Select words with the prescribed symbol counts before separating their
common first factors. Only then identify the word products with the common
grouped product. This order avoids using incompatible first-factor maps in
a partially direct sum.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K H I : Type*} [Field K] [Fintype H] [DecidableEq H] [Fintype I]
variable {J L : H → Type*} [∀ h, Fintype (J h)] [∀ h, Fintype (L h)]

/-- A type class of cardinality `Q` separates using exactly `2*Q-1` copies.
The theorem includes zero counts, the empty family, and the zeroth power. -/
theorem partialSum_type_separation (T : ∀ h, Tensor K I (J h) (L h))
    (n : ℕ) (c : H → ℕ) (hc : (∑ h, c h) = n) :
    Degenerates
      (directSumCopies (kroneckerPower (partialSumFamily T) n)
        (2 * Nat.multinomial Finset.univ c - 1))
      (kronecker
        (directSumCopies (tensorProductFamily (fun h => kroneckerPower (T h) (c h)))
          (Nat.multinomial Finset.univ c))
        (matrixMul K 1 1 (Nat.multinomial Finset.univ c))) := by
  classical
  let Q := Nat.multinomial Finset.univ c
  let W := fun w : WordType n c => tensorProductFamily (fun i => T (w.val i))
  let P := tensorProductFamily (fun h => kroneckerPower (T h) (c h))
  have hselect := kroneckerPower_partialSumFamily_restricts T n
    (fun w : WordType n c => w.val) Subtype.val_injective
  have hcopies : Restricts
      (directSumCopies (kroneckerPower (partialSumFamily T) n) (2 * Q - 1))
      (directSumCopies (partialSumFamily W) (2 * Q - 1)) :=
    (Restricts.refl (diagonal K (2 * Q - 1))).kronecker hselect
  have hsep := partialSumFamily_separation W Q
  rw [card_wordType c hc] at hsep
  have hsize : Nat.multinomial Finset.univ c + Q - 1 = 2 * Q - 1 := by
    dsimp [Q]
    omega
  rw [hsize] at hsep
  have heq := directSumFamily_equivalent_copies W P (fun w =>
    wordProduct_equivalent_grouped_of_counts T w.val c w.property)
  rw [card_wordType c hc] at heq
  exact hcopies.degenerates.trans
    (hsep.trans ((heq.1.kronecker (Restricts.refl (matrixMul K 1 1 Q))).degenerates))

end MatrixMultiplication.Tensor
