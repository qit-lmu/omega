module

public import Omega.Tensor.Symmetrization
public import Omega.Tensor.DirectSumCopies
public import Omega.Tensor.Nonzero

/-!
# Structural identities for six-factor symmetrization

Rotations and transpositions permute the six terms. Products distribute
through symmetrization, and `a` identical blocks give `a^6` identical blocks.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Cyclically move the first entry of a triple to the last position. -/
def tripleRotateEquiv (A B C : Type*) : (A × B × C) ≃ (B × C × A) where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rotating the input only cyclically reorders the three cyclic factors. -/
theorem cyclicSymmetrize_rotate_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (cyclicSymmetrize (rotate T)) (cyclicSymmetrize T) := by
  apply equivalent_of_reindex (tripleRotateEquiv I J L).symm
    (tripleRotateEquiv J L I).symm (tripleRotateEquiv L I J).symm
  funext i j k
  simp only [reindex, tripleRotateEquiv, Equiv.symm_symm, Equiv.coe_fn_mk,
    cyclicSymmetrize, kronecker, rotate]
  ac_rfl

/-- The transposition generator interchanges the even and odd cyclic products. -/
theorem symmetrize_swapFirstTwo_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (symmetrize (swapFirstTwo T)) (symmetrize T) := by
  apply equivalent_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (Equiv.prodComm _ _)
  funext i j k
  change cyclicSymmetrize (swapFirstTwo T) i.2 j.2 k.2 *
      cyclicSymmetrize T i.1 j.1 k.1 =
    cyclicSymmetrize T i.1 j.1 k.1 * cyclicSymmetrize (swapFirstTwo T) i.2 j.2 k.2
  exact mul_comm _ _

/-- The rotation generator permutes factors within each cyclic product.
Together with the transposition identity this proves invariance under all of S₃. -/
theorem symmetrize_rotate_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (symmetrize (rotate T)) (symmetrize T) := by
  have h := (cyclicSymmetrize_rotate_equivalent (rotate (swapFirstTwo T))).trans
    (cyclicSymmetrize_rotate_equivalent (swapFirstTwo T))
  exact (cyclicSymmetrize_rotate_equivalent T).kronecker h

/-- Invariance for the other nonidentity even permutation. -/
theorem symmetrize_rotate_twice_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (symmetrize (rotate (rotate T))) (symmetrize T) :=
  (symmetrize_rotate_equivalent (rotate T)).trans (symmetrize_rotate_equivalent T)

/-- Invariance for the first remaining odd permutation. -/
theorem symmetrize_rotate_swap_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (symmetrize (rotate (swapFirstTwo T))) (symmetrize T) :=
  (symmetrize_rotate_equivalent (swapFirstTwo T)).trans
    (symmetrize_swapFirstTwo_equivalent T)

/-- Invariance for the last remaining odd permutation. -/
theorem symmetrize_rotate_twice_swap_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (symmetrize (rotate (rotate (swapFirstTwo T)))) (symmetrize T) :=
  (symmetrize_rotate_twice_equivalent (swapFirstTwo T)).trans
    (symmetrize_swapFirstTwo_equivalent T)

/-- Group the first and second entries of three pairs into separate triples. -/
def tripleProductEquiv (A B C A' B' C' : Type*) :
    ((A × A') × (B × B') × (C × C')) ≃ (A × B × C) × (A' × B' × C') where
  toFun x := ((x.1.1, x.2.1.1, x.2.2.1), (x.1.2, x.2.1.2, x.2.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2.1, x.2.2.1), (x.1.2.2, x.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Products distribute through the three cyclic permutations. -/
theorem cyclicSymmetrize_kronecker_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    Equivalent (cyclicSymmetrize (kronecker T S))
      (kronecker (cyclicSymmetrize T) (cyclicSymmetrize S)) := by
  apply equivalent_of_reindex (tripleProductEquiv I J L I' J' L')
    (tripleProductEquiv J L I J' L' I') (tripleProductEquiv L I J L' I' J')
  funext i j k
  simp only [reindex, tripleProductEquiv, Equiv.coe_fn_symm_mk,
    cyclicSymmetrize, kronecker, rotate]
  ac_rfl

private theorem kronecker_shuffle_equivalent [CommSemiring R]
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    [Fintype I₁] [Fintype J₁] [Fintype L₁] [Fintype I₂] [Fintype J₂] [Fintype L₂]
    (T : Tensor R I J L) (S : Tensor R I' J' L')
    (U : Tensor R I₁ J₁ L₁) (V : Tensor R I₂ J₂ L₂) :
    Equivalent (kronecker (kronecker T S) (kronecker U V))
      (kronecker (kronecker T U) (kronecker S V)) := by
  apply equivalent_of_reindex (Equiv.prodProdProdComm I I' I₁ I₂)
    (Equiv.prodProdProdComm J J' J₁ J₂) (Equiv.prodProdProdComm L L' L₁ L₂)
  funext i j k
  change (T i.1.1 j.1.1 k.1.1 * S i.2.1 j.2.1 k.2.1) *
      (U i.1.2 j.1.2 k.1.2 * V i.2.2 j.2.2 k.2.2) = _
  simp only [kronecker]
  ac_rfl

/-- Kronecker symmetrization respects Kronecker products. -/
theorem symmetrize_kronecker_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    Equivalent (symmetrize (kronecker T S))
      (kronecker (symmetrize T) (symmetrize S)) := by
  have h := (cyclicSymmetrize_kronecker_equivalent T S).kronecker
    (cyclicSymmetrize_kronecker_equivalent (swapFirstTwo T) (swapFirstTwo S))
  exact h.trans (kronecker_shuffle_equivalent _ _ _ _)

/-- Products of diagonals are diagonals of the product size. -/
theorem diagonal_kronecker_equivalent [CommSemiring R] (a b : ℕ) :
    Equivalent (kronecker (diagonal R a) (diagonal R b)) (diagonal R (a * b)) := by
  apply equivalent_of_reindex finProdFinEquiv finProdFinEquiv finProdFinEquiv
  funext i j k
  obtain ⟨i, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨k, rfl⟩ := finProdFinEquiv.surjective k
  simp only [reindex, Equiv.symm_apply_apply, kronecker, diagonal,
    Equiv.apply_eq_iff_eq, Prod.ext_iff]
  split_ifs <;> simp_all

@[simp]
theorem rotate_diagonal [Zero R] [One R] (a : ℕ) :
    rotate (diagonal R a) = diagonal R a := by
  funext i j k
  simp only [rotate, diagonal]
  by_cases hij : i = j <;> by_cases hjk : j = k <;> simp_all [eq_comm]

@[simp]
theorem swapFirstTwo_diagonal [Zero R] [One R] (a : ℕ) :
    swapFirstTwo (diagonal R a) = diagonal R a := by
  funext i j k
  simp only [swapFirstTwo, diagonal]
  by_cases hij : i = j <;> by_cases hjk : j = k <;> simp_all [eq_comm]

private theorem cyclicSymmetrize_diagonal_equivalent [CommSemiring R] (a : ℕ) :
    Equivalent (cyclicSymmetrize (diagonal R a)) (diagonal R (a * (a * a))) := by
  simp only [cyclicSymmetrize, rotate_diagonal]
  exact ((Equivalent.refl _).kronecker (diagonal_kronecker_equivalent a a)).trans
    (diagonal_kronecker_equivalent a (a * a))

/-- Six factor permutations of a diagonal give a diagonal with size `a^6`. -/
theorem symmetrize_diagonal_equivalent [CommSemiring R] (a : ℕ) :
    Equivalent (symmetrize (diagonal R a)) (diagonal R (a ^ 6)) := by
  have h := ((cyclicSymmetrize_diagonal_equivalent (R := R) a).kronecker
    (cyclicSymmetrize_diagonal_equivalent (R := R) a)).trans
      (diagonal_kronecker_equivalent (a * (a * a)) (a * (a * a)))
  rw [show a * (a * a) * (a * (a * a)) = a ^ 6 by ring] at h
  simpa only [symmetrize, swapFirstTwo_diagonal] using h

/-- Symmetrization sends `a` identical blocks to `a^6` identical blocks. -/
theorem symmetrize_directSumCopies_equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) (a : ℕ) :
    Equivalent (symmetrize (directSumCopies T a))
      (directSumCopies (symmetrize T) (a ^ 6)) :=
  (symmetrize_kronecker_equivalent (diagonal R a) T).trans
    ((symmetrize_diagonal_equivalent a).kronecker (Equivalent.refl _))

/-- All three cyclic factors of a nonzero tensor are nonzero. -/
theorem cyclicSymmetrize_ne_zero [Field R]
    {T : Tensor R I J L} (hT : T ≠ 0) : cyclicSymmetrize T ≠ 0 := by
  have hrot : rotate T ≠ 0 := fun h => hT (congrArg (fun U => rotate (rotate U)) h)
  have hrot2 : rotate (rotate T) ≠ 0 := fun h => hT (congrArg rotate h)
  exact kronecker_ne_zero hT (kronecker_ne_zero hrot hrot2)

/-- Symmetrization of a nonzero tensor is nonzero over every field. -/
theorem symmetrize_ne_zero [Field R]
    {T : Tensor R I J L} (hT : T ≠ 0) : symmetrize T ≠ 0 := by
  have hswap : swapFirstTwo T ≠ 0 := fun h => hT (congrArg swapFirstTwo h)
  exact kronecker_ne_zero (cyclicSymmetrize_ne_zero hT) (cyclicSymmetrize_ne_zero hswap)

/-- A nonzero symmetrization can supply the unit diagonal tensor. -/
theorem symmetrize_restricts_diagonal_one [Field R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (hT : T ≠ 0) :
    Restricts (symmetrize T) (diagonal R 1) :=
  restricts_diagonal_one_of_ne_zero _ (symmetrize_ne_zero hT)

end MatrixMultiplication.Tensor
