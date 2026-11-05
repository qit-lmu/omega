module

public import Omega.Tensor.SymmetrizationOperations
public import Mathlib.Data.Fintype.Perm

/-!
# The six factor permutations and symmetrization invariance

`FactorPermutation` enumerates all six orders of the three tensor factors and
is explicitly equivalent to `Equiv.Perm (Fin 3)`. Permuting a tensor changes
its coordinate types accordingly. The three coordinate types share a universe;
the coefficient type may live in a different universe.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- The six orders of three tensor factors. -/
inductive FactorPermutation
  | identity
  | cycle
  | cycleTwice
  | transposition
  | cycleTransposition
  | cycleTwiceTransposition
  deriving DecidableEq

namespace FactorPermutation

instance : Fintype FactorPermutation where
  elems := {identity, cycle, cycleTwice, transposition, cycleTransposition, cycleTwiceTransposition}
  complete p := by cases p <;> simp

/-- The three-cycle sending the slots `0,1,2` to `1,2,0`. -/
def cycleEquiv : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The permutation sends each output slot to its original input slot. -/
def toEquiv : FactorPermutation → Equiv.Perm (Fin 3)
  | identity => Equiv.refl _
  | cycle => cycleEquiv
  | cycleTwice => cycleEquiv.trans cycleEquiv
  | transposition => Equiv.swap 0 1
  | cycleTransposition => cycleEquiv.trans (Equiv.swap 0 1)
  | cycleTwiceTransposition => (cycleEquiv.trans cycleEquiv).trans (Equiv.swap 0 1)

/-- The six explicit orders give every permutation exactly once. -/
theorem toEquiv_bijective : Function.Bijective toEquiv := by decide

/-- Identify the six explicit orders with the symmetric group on three letters. -/
noncomputable def equivPerm : FactorPermutation ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective toEquiv toEquiv_bijective

universe u

/-- The first coordinate type after permuting the factors. -/
def firstFactor (p : FactorPermutation) (I J L : Type u) : Type u :=
  match p with
  | identity => I
  | cycle => J
  | cycleTwice => L
  | transposition => J
  | cycleTransposition => I
  | cycleTwiceTransposition => L

/-- The second coordinate type after permuting the factors. -/
def secondFactor (p : FactorPermutation) (I J L : Type u) : Type u :=
  match p with
  | identity => J
  | cycle => L
  | cycleTwice => I
  | transposition => I
  | cycleTransposition => L
  | cycleTwiceTransposition => J

/-- The third coordinate type after permuting the factors. -/
def thirdFactor (p : FactorPermutation) (I J L : Type u) : Type u :=
  match p with
  | identity => L
  | cycle => I
  | cycleTwice => J
  | transposition => L
  | cycleTransposition => J
  | cycleTwiceTransposition => I

/-- Coordinate types agree with the corresponding permutation of slots. -/
theorem firstFactor_eq (p : FactorPermutation) (I J L : Type u) :
    firstFactor p I J L = ![I, J, L] (toEquiv p 0) := by cases p <;> rfl

/-- Coordinate types agree with the corresponding permutation of slots. -/
theorem secondFactor_eq (p : FactorPermutation) (I J L : Type u) :
    secondFactor p I J L = ![I, J, L] (toEquiv p 1) := by cases p <;> rfl

/-- Coordinate types agree with the corresponding permutation of slots. -/
theorem thirdFactor_eq (p : FactorPermutation) (I J L : Type u) :
    thirdFactor p I J L = ![I, J, L] (toEquiv p 2) := by cases p <;> rfl

instance (p : FactorPermutation) (I J L : Type u)
    [Fintype I] [Fintype J] [Fintype L] : Fintype (firstFactor p I J L) := by
  cases p <;> dsimp [firstFactor] <;> infer_instance

instance (p : FactorPermutation) (I J L : Type u)
    [Fintype I] [Fintype J] [Fintype L] : Fintype (secondFactor p I J L) := by
  cases p <;> dsimp [secondFactor] <;> infer_instance

instance (p : FactorPermutation) (I J L : Type u)
    [Fintype I] [Fintype J] [Fintype L] : Fintype (thirdFactor p I J L) := by
  cases p <;> dsimp [thirdFactor] <;> infer_instance

end FactorPermutation

universe u v

variable {R : Type v} {I J L : Type u}

/-- Permute the three tensor factors in any of the six possible orders. -/
def permute (p : FactorPermutation) (T : Tensor R I J L) :
    Tensor R (p.firstFactor I J L) (p.secondFactor I J L) (p.thirdFactor I J L) :=
  match p with
  | .identity => T
  | .cycle => rotate T
  | .cycleTwice => rotate (rotate T)
  | .transposition => swapFirstTwo T
  | .cycleTransposition => rotate (swapFirstTwo T)
  | .cycleTwiceTransposition => rotate (rotate (swapFirstTwo T))

/-- Symmetrization is invariant under every permutation of the three factors. -/
theorem symmetrize_permute [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (p : FactorPermutation) (T : Tensor R I J L) :
    Equivalent (symmetrize (permute p T)) (symmetrize T) := by
  cases p with
  | identity => exact Equivalent.refl _
  | cycle => exact symmetrize_rotate_equivalent T
  | cycleTwice => exact symmetrize_rotate_twice_equivalent T
  | transposition => exact symmetrize_swapFirstTwo_equivalent T
  | cycleTransposition => exact symmetrize_rotate_swap_equivalent T
  | cycleTwiceTransposition => exact symmetrize_rotate_twice_swap_equivalent T

/-- Permute factors using an element of the symmetric group on three letters. -/
noncomputable def permuteS3 (σ : Equiv.Perm (Fin 3)) (T : Tensor R I J L) :
    Tensor R ((FactorPermutation.equivPerm.symm σ).firstFactor I J L)
      ((FactorPermutation.equivPerm.symm σ).secondFactor I J L)
      ((FactorPermutation.equivPerm.symm σ).thirdFactor I J L) :=
  permute (FactorPermutation.equivPerm.symm σ) T

/-- Symmetrization is invariant under every element of S₃. -/
theorem symmetrize_permuteS3 [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (σ : Equiv.Perm (Fin 3)) (T : Tensor R I J L) :
    Equivalent (symmetrize (permuteS3 σ T)) (symmetrize T) :=
  symmetrize_permute _ T

end MatrixMultiplication.Tensor
