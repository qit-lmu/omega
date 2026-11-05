module

public import Mathlib.Data.Matrix.Mul

/-!
# Coefficient tensors and restriction

The three index types describe chosen bases.  Finiteness is required only for
operations that sum over a basis.  In particular, the first factor of a partial
direct sum is literally the same index type in both blocks.

These definitions implement the coordinate conventions of the preliminaries
of `material/main.tex`.  Equivalence means mutual restriction, so zero padding
does not require an equality of ambient dimensions.
-/

@[expose] public section

namespace MatrixMultiplication

/-- A tensor in three finite based vector spaces, represented by coefficients. -/
abbrev Tensor (R : Type*) (I J L : Type*) := I → J → L → R

namespace Tensor

variable {R : Type*} {I J L I' J' L' I'' J'' L'' : Type*}

/-- The coefficient tensor of a pure tensor. -/
def pure [Mul R] (x : I → R) (y : J → R) (z : L → R) : Tensor R I J L :=
  fun i j k => x i * y j * z k

/-- Apply one matrix to each of the three factors. -/
def map [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) : Tensor R I' J' L' :=
  fun i' j' k' => ∑ i, ∑ j, ∑ k, A i' i * B j' j * C k' k * T i j k

@[simp]
theorem map_one [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L] (T : Tensor R I J L) :
    map (1 : Matrix I I R) (1 : Matrix J J R) (1 : Matrix L L R) T = T := by
  funext i j k
  simp [map, Matrix.one_apply]

private theorem sum_three_comm [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (f : I' → J' → L' → I → J → L → R) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, f a b c i j k) =
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f a b c i j k := by
  calc
    _ = ∑ p : I' × J' × L', ∑ q : I × J × L,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : I × J × L, ∑ p : I' × J' × L',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem sum_three_reverse [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype L] (f : I → J → L → R) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Applying factor maps successively is matrix composition in each factor. -/
theorem map_map [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (A' : Matrix I'' I' R) (B' : Matrix J'' J' R) (C' : Matrix L'' L' R)
    (T : Tensor R I J L) :
    map A' B' C' (map A B C T) = map (A' * A) (B' * B) (C' * C) T := by
  funext i j k
  simp only [map, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [sum_three_reverse]
  simp only [mul_left_comm, mul_comm]

@[simp]
theorem map_zero [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R) :
    map A B C (0 : Tensor R I J L) = 0 := by
  funext i j k
  simp [map]

theorem map_add [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T S : Tensor R I J L) :
    map A B C (T + S) = map A B C T + map A B C S := by
  funext i j k
  simp [map, mul_add, Finset.sum_add_distrib]

/-- Factor maps preserve pure tensors. -/
theorem map_pure [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (x : I → R) (y : J → R) (z : L → R) :
    map A B C (pure x y z) =
      pure (Matrix.mulVec A x) (Matrix.mulVec B y) (Matrix.mulVec C z) := by
  funext i j k
  simp only [map, pure, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_reverse]
  simp only [mul_left_comm, mul_comm]

/-- Applying factor maps commutes with a finite sum of tensors. -/
theorem map_sum [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    {α : Type*} (s : Finset α)
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : α → Tensor R I J L) :
    map A B C (∑ a ∈ s, T a) = ∑ a ∈ s, map A B C (T a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, map_add, ih]

/-- `Restricts T S` means that `S` is obtained by three factor maps from `T`.
This is the direction denoted by `T ≥ S` in the manuscript. -/
def Restricts [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (S : Tensor R I' J' L') : Prop :=
  ∃ (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R), map A B C T = S

theorem Restricts.refl [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : Restricts T T := by
  classical
  exact ⟨1, 1, 1, map_one T⟩

theorem Restricts.trans [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} {U : Tensor R I'' J'' L''}
    (hTS : Restricts T S) (hSU : Restricts S U) : Restricts T U := by
  obtain ⟨A, B, C, rfl⟩ := hTS
  obtain ⟨A', B', C', h⟩ := hSU
  exact ⟨A' * A, B' * B, C' * C, (map_map A B C A' B' C' T).symm.trans h⟩

/-- Equivalence of tensors is mutual restriction, not equality of dimensions. -/
def Equivalent [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') : Prop :=
  Restricts T S ∧ Restricts S T

theorem Equivalent.refl [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : Equivalent T T :=
  ⟨Restricts.refl T, Restricts.refl T⟩

theorem Equivalent.symm [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Equivalent T S) : Equivalent S T := ⟨h.2, h.1⟩

theorem Equivalent.trans [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    [Fintype I''] [Fintype J''] [Fintype L'']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} {U : Tensor R I'' J'' L''}
    (hTS : Equivalent T S) (hSU : Equivalent S U) : Equivalent T U :=
  ⟨hTS.1.trans hSU.1, hSU.2.trans hTS.2⟩

/-- Kronecker product, with the three factors grouped coordinatewise. -/
def kronecker [Mul R] (T : Tensor R I J L) (S : Tensor R I' J' L') :
    Tensor R (I × I') (J × J') (L × L') :=
  fun i j k => T i.1 j.1 k.1 * S i.2 j.2 k.2

/-- Ordinary direct sum; all three tensor factors have separate blocks. -/
def directSum [Zero R] (T : Tensor R I J L) (S : Tensor R I' J' L') :
    Tensor R (I ⊕ I') (J ⊕ J') (L ⊕ L')
  | .inl i, .inl j, .inl k => T i j k
  | .inr i, .inr j, .inr k => S i j k
  | _, _, _ => 0

/-- Partial direct sum, with a common first factor and separate second and third
factors.  Transporting its blocks requires compatible maps on the first factor. -/
def partialSum [Zero R] (T : Tensor R I J L) (S : Tensor R I J' L') :
    Tensor R I (J ⊕ J') (L ⊕ L')
  | i, .inl j, .inl k => T i j k
  | i, .inr j, .inr k => S i j k
  | _, _, _ => 0

@[simp]
theorem directSum_inl [Zero R] (T : Tensor R I J L) (S : Tensor R I' J' L')
    (i : I) (j : J) (k : L) :
    directSum T S (.inl i) (.inl j) (.inl k) = T i j k := rfl

@[simp]
theorem directSum_inr [Zero R] (T : Tensor R I J L) (S : Tensor R I' J' L')
    (i : I') (j : J') (k : L') :
    directSum T S (.inr i) (.inr j) (.inr k) = S i j k := rfl

@[simp]
theorem partialSum_inl [Zero R] (T : Tensor R I J L) (S : Tensor R I J' L')
    (i : I) (j : J) (k : L) :
    partialSum T S i (.inl j) (.inl k) = T i j k := rfl

@[simp]
theorem partialSum_inr [Zero R] (T : Tensor R I J L) (S : Tensor R I J' L')
    (i : I) (j : J') (k : L') :
    partialSum T S i (.inr j) (.inr k) = S i j k := rfl

/-- Projection onto the left block is a restriction, with identity on the
common first factor.  This is the first assertion of `diamondplus-basic`. -/
theorem partialSum_restricts_left [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I J' L') :
    Restricts (partialSum T S) T := by
  classical
  refine ⟨1,
    (fun j x => Sum.elim (fun j' => (1 : Matrix J J R) j j') (fun _ => 0) x),
    (fun k x => Sum.elim (fun k' => (1 : Matrix L L R) k k') (fun _ => 0) x), ?_⟩
  funext i j k
  simp [map, partialSum, Fintype.sum_sum_type, Matrix.one_apply]

/-- Projection onto the right block likewise fixes the common first factor. -/
theorem partialSum_restricts_right [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I J' L') :
    Restricts (partialSum T S) S := by
  classical
  refine ⟨1,
    (fun j x => Sum.elim (fun _ => 0) (fun j' => (1 : Matrix J' J' R) j j') x),
    (fun k x => Sum.elim (fun _ => 0) (fun k' => (1 : Matrix L' L' R) k k') x), ?_⟩
  funext i j k
  simp [map, partialSum, Fintype.sum_sum_type, Matrix.one_apply]

end Tensor
end MatrixMultiplication
