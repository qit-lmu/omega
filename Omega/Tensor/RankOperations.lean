module

public import Omega.Tensor.Rank
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic.Ring

/-!
# Rank bounds for sums and Kronecker products

Finite pure-tensor decompositions supply explicit diagonal restriction
witnesses. All bounds hold over a commutative semiring, hence over every field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]

/-- A finite decomposition into pure tensors bounds the rank by its number of terms. -/
theorem rank_le_of_sum_pure {α : Type*} [Fintype α]
    (x : α → I → R) (y : α → J → R) (z : α → L → R) :
    rank (∑ a, pure (x a) (y a) (z a)) ≤ Fintype.card α := by
  classical
  apply rank_le_of_diagonal_restricts
  let e := (Fintype.equivFin α).symm
  refine ⟨Matrix.of (fun i p => x (e p) i), Matrix.of (fun j p => y (e p) j),
    Matrix.of (fun k p => z (e p) k), ?_⟩
  rw [map_diagonal]
  funext i j k
  simp only [Finset.sum_apply, pure]
  change (∑ p : Fin (Fintype.card α), x (e p) i * y (e p) j * z (e p) k) =
    ∑ a : α, x a i * y a j * z a k
  exact e.sum_comp (fun a => x a i * y a j * z a k)

/-- A rank-minimizing diagonal restriction is a decomposition into that many pure tensors. -/
theorem exists_rank_decomposition (T : Tensor R I J L) :
    ∃ (x : Fin (rank T) → I → R) (y : Fin (rank T) → J → R)
      (z : Fin (rank T) → L → R), T = ∑ a, pure (x a) (y a) (z a) := by
  obtain ⟨A, B, C, h⟩ := diagonal_restricts_of_rank T
  refine ⟨(fun a i => A i a), (fun a j => B j a), (fun a k => C k a), ?_⟩
  calc
    T = map A B C (diagonal R (rank T)) := h.symm
    _ = _ := by
      rw [map_diagonal]
      funext i j k
      simp [pure]

/-- Rank is subadditive for the sum of tensors in fixed ambient spaces. -/
theorem rank_add_le (T S : Tensor R I J L) : rank (T + S) ≤ rank T + rank S := by
  classical
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  obtain ⟨x', y', z', hS⟩ := exists_rank_decomposition S
  have h := rank_le_of_sum_pure (Sum.elim x x') (Sum.elim y y') (Sum.elim z z')
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ← hT, ← hS, Fintype.card_sum, Fintype.card_fin] using h

/-- Rank is subadditive for every finite sum. -/
theorem rank_sum_le {α : Type*} (s : Finset α) (T : α → Tensor R I J L) :
    rank (∑ a ∈ s, T a) ≤ ∑ a ∈ s, rank (T a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Applying maps to the three factors cannot increase rank. -/
theorem rank_map_le [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) : rank (map A B C T) ≤ rank T :=
  rank_mono ⟨A, B, C, rfl⟩

/-- Tensor rank is submultiplicative under Kronecker products. -/
theorem rank_kronecker_le [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    rank (kronecker T S) ≤ rank T * rank S := by
  classical
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  obtain ⟨x', y', z', hS⟩ := exists_rank_decomposition S
  have h := rank_le_of_sum_pure
    (fun p : Fin (rank T) × Fin (rank S) => fun i : I × I' => x p.1 i.1 * x' p.2 i.2)
    (fun p : Fin (rank T) × Fin (rank S) => fun j : J × J' => y p.1 j.1 * y' p.2 j.2)
    (fun p : Fin (rank T) × Fin (rank S) => fun k : L × L' => z p.1 k.1 * z' p.2 k.2)
  have he : kronecker T S = ∑ p : Fin (rank T) × Fin (rank S),
      pure (fun i => x p.1 i.1 * x' p.2 i.2)
        (fun j => y p.1 j.1 * y' p.2 j.2)
        (fun k => z p.1 k.1 * z' p.2 k.2) := by
    funext i j k
    have ht := congrFun (congrFun (congrFun hT i.1) j.1) k.1
    have hs := congrFun (congrFun (congrFun hS i.2) j.2) k.2
    simp only [kronecker, ht, hs, Finset.sum_apply, pure,
      Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simpa only [← he, Fintype.card_prod, Fintype.card_fin] using h

private theorem sum_product_three [Fintype I'] [Fintype J'] [Fintype L']
    (f : I → J → L → R) (g : I' → J' → L' → R) :
    (∑ i : I × I', ∑ j : J × J', ∑ k : L × L',
      f i.1 j.1 k.1 * g i.2 j.2 k.2) =
      (∑ i, ∑ j, ∑ k, f i j k) * (∑ i, ∑ j, ∑ k, g i j k) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Kronecker products of factor maps act on Kronecker products of tensors. -/
theorem map_kronecker {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I₁ I R) (B : Matrix J₁ J R) (C : Matrix L₁ L R)
    (A' : Matrix I₂ I' R) (B' : Matrix J₂ J' R) (C' : Matrix L₂ L' R)
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    map (Matrix.kronecker A A') (Matrix.kronecker B B') (Matrix.kronecker C C')
      (kronecker T S) = kronecker (map A B C T) (map A' B' C' S) := by
  funext i j k
  simp only [map, kronecker, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply]
  calc
    _ = ∑ a : I × I', ∑ b : J × J', ∑ c : L × L',
        (A i.1 a.1 * B j.1 b.1 * C k.1 c.1 * T a.1 b.1 c.1) *
        (A' i.2 a.2 * B' j.2 b.2 * C' k.2 c.2 * S a.2 b.2 c.2) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ac_rfl
    _ = _ := sum_product_three
      (I := I) (J := J) (L := L) (I' := I') (J' := J') (L' := L')
      (fun a b c => A i.1 a * B j.1 b * C k.1 c * T a b c)
      (fun a b c => A' i.2 a * B' j.2 b * C' k.2 c * S a b c)

/-- Restriction is compatible with Kronecker products. -/
theorem Restricts.kronecker {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (kronecker T S) (kronecker T' S') := by
  obtain ⟨A, B, C, rfl⟩ := hT
  obtain ⟨A', B', C', rfl⟩ := hS
  exact ⟨Matrix.kronecker A A', Matrix.kronecker B B', Matrix.kronecker C C',
    map_kronecker A B C A' B' C' T S⟩

/-- A block-diagonal factor map on two disjoint coordinate sets. -/
def directSumMap {I₁ I₂ : Type*} (A : Matrix I₁ I R) (A' : Matrix I₂ I' R) :
    Matrix (I₁ ⊕ I₂) (I ⊕ I') R :=
  Matrix.of fun i j => match i, j with
    | .inl i, .inl j => A i j
    | .inr i, .inr j => A' i j
    | _, _ => 0

/-- Block-diagonal factor maps act independently on an ordinary direct sum. -/
theorem map_directSum {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I₁ I R) (B : Matrix J₁ J R) (C : Matrix L₁ L R)
    (A' : Matrix I₂ I' R) (B' : Matrix J₂ J' R) (C' : Matrix L₂ L' R)
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    map (directSumMap A A') (directSumMap B B') (directSumMap C C')
      (directSum T S) = directSum (map A B C T) (map A' B' C' S) := by
  funext i j k
  cases i <;> cases j <;> cases k <;>
    simp [map, directSum, directSumMap, Fintype.sum_sum_type]

/-- Restriction is compatible with ordinary direct sums. -/
theorem Restricts.directSum {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (directSum T S) (directSum T' S') := by
  obtain ⟨A, B, C, rfl⟩ := hT
  obtain ⟨A', B', C', rfl⟩ := hS
  exact ⟨directSumMap A A', directSumMap B B', directSumMap C C',
    map_directSum A B C A' B' C' T S⟩

/-- Embedding a tensor as the left summand is a restriction (zero padding). -/
theorem restricts_directSum_zero [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) : Restricts T (directSum T (0 : Tensor R I' J' L')) := by
  classical
  refine ⟨Matrix.of (fun i a => Sum.elim (fun i => (1 : Matrix I I R) i a) (fun _ => 0) i),
    Matrix.of (fun j b => Sum.elim (fun j => (1 : Matrix J J R) j b) (fun _ => 0) j),
    Matrix.of (fun k c => Sum.elim (fun k => (1 : Matrix L L R) k c) (fun _ => 0) k), ?_⟩
  funext i j k
  cases i <;> cases j <;> cases k <;> simp [map, directSum, Matrix.one_apply]

omit [Fintype I] [Fintype J] [Fintype L] in
/-- Embedding a tensor as the right summand is a restriction (zero padding). -/
theorem restricts_zero_directSum [Fintype I'] [Fintype J'] [Fintype L']
    (S : Tensor R I' J' L') : Restricts S (directSum (0 : Tensor R I J L) S) := by
  classical
  refine ⟨Matrix.of (fun i a => Sum.elim (fun _ => 0) (fun i => (1 : Matrix I' I' R) i a) i),
    Matrix.of (fun j b => Sum.elim (fun _ => 0) (fun j => (1 : Matrix J' J' R) j b) j),
    Matrix.of (fun k c => Sum.elim (fun _ => 0) (fun k => (1 : Matrix L' L' R) k c) k), ?_⟩
  funext i j k
  cases i <;> cases j <;> cases k <;> simp [map, directSum, Matrix.one_apply]

/-- Rank is subadditive for ordinary direct sums. -/
theorem rank_directSum_le [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    rank (directSum T S) ≤ rank T + rank S := by
  have h : directSum T S = directSum T (0 : Tensor R I' J' L') +
      directSum (0 : Tensor R I J L) S := by
    funext i j k
    cases i <;> cases j <;> cases k <;> simp [directSum]
  rw [h]
  exact (rank_add_le _ _).trans
    (Nat.add_le_add (rank_mono (restricts_directSum_zero T))
      (rank_mono (restricts_zero_directSum S)))

end MatrixMultiplication.Tensor
