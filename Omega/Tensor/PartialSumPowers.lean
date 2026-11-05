module

public import Omega.Tensor.PartialSum
public import Omega.Tensor.ProductFamily

/-!
# Selecting words from a power of a partially direct sum

Coordinates in the second and third factors carry words of block labels.
Selecting any injectively indexed family of such words retains a partially
direct sum of the corresponding products, with the first factor still shared.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R I J L I' J' L' : Type*}

/-- Pulling back coefficients along arbitrary coordinate functions is a restriction. -/
theorem restricts_pullback [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (f : I' → I) (g : J' → J) (h : L' → L) :
    Restricts T (fun i j k => T (f i) (g j) (h k)) := by
  classical
  refine ⟨(fun i' i => if i = f i' then 1 else 0),
    (fun j' j => if j = g j' then 1 else 0),
    (fun k' k => if k = h k' then 1 else 0), ?_⟩
  funext i j k
  simp [map, ite_mul]

/-- A tensor power of a partial sum restricts to any chosen family of distinct words. -/
theorem kroneckerPower_partialSumFamily_restricts
    [CommSemiring R] {H A : Type*} {J L : H → Type*}
    [Fintype H] [DecidableEq H] [Fintype I]
    [∀ h, Fintype (J h)] [∀ h, Fintype (L h)] [DecidableEq A]
    (T : ∀ h, Tensor R I (J h) (L h)) (n : ℕ)
    (w : A → Fin n → H) (hw : Function.Injective w) :
    Restricts (kroneckerPower (partialSumFamily T) n)
      (partialSumFamily (fun a => tensorProductFamily (fun t => T (w a t)))) := by
  have h := restricts_pullback (kroneckerPower (partialSumFamily T) n) id
    (fun j : Σ a, (t : Fin n) → J (w a t) => fun t => ⟨w j.1 t, j.2 t⟩)
    (fun k : Σ a, (t : Fin n) → L (w a t) => fun t => ⟨w k.1 t, k.2 t⟩)
  convert h using 1
  funext i ⟨a, j⟩ ⟨b, k⟩
  by_cases hab : a = b
  · subst b
    simp [kroneckerPower, tensorProductFamily]
  · rw [partialSumFamily_ne _ _ _ _ hab]
    change 0 = ∏ t, partialSumFamily T (i t) ⟨w a t, j t⟩ ⟨w b t, k t⟩
    have hex : ∃ t, w a t ≠ w b t := by
      by_contra! hh
      exact hab (hw (funext hh))
    obtain ⟨t, ht⟩ := hex
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ t) (partialSumFamily_ne _ _ _ _ ht)

end MatrixMultiplication.Tensor
