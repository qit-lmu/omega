module

public import Omega.Tensor.Powers

/-!
# Reindexing iterated tensor powers

Tuples indexed by a product flatten to a single tuple, and tuples of pairs
split into pairs of tuples. These identifications preserve tensor rank.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Flatten a tuple of tuples using the standard product indexing of `Fin`. -/
def powerTupleEquiv (I : Type*) (m n : ℕ) :
    (Fin m → Fin n → I) ≃ (Fin (m * n) → I) :=
  (Equiv.curry (Fin m) (Fin n) I).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl I))

/-- Taking a tensor power of a tensor power multiplies the exponents. -/
theorem kroneckerPower_mul_reindex [CommMonoid R]
    (T : Tensor R I J L) (k n : ℕ) :
    reindex (powerTupleEquiv I n k) (powerTupleEquiv J n k)
      (powerTupleEquiv L n k) (kroneckerPower (kroneckerPower T k) n) =
      kroneckerPower T (n * k) := by
  funext i j l
  change (∏ a : Fin n, ∏ b : Fin k,
    T (i (finProdFinEquiv (a, b))) (j (finProdFinEquiv (a, b)))
      (l (finProdFinEquiv (a, b)))) = ∏ t, T (i t) (j t) (l t)
  calc
    _ = ∏ p : Fin n × Fin k, T (i (finProdFinEquiv p))
        (j (finProdFinEquiv p)) (l (finProdFinEquiv p)) :=
      (Fintype.prod_prod_type _).symm
    _ = _ := Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)

/-- Iterated powers and the corresponding single power have equal ranks. -/
theorem rank_kroneckerPower_kroneckerPower [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (k n : ℕ) :
    rank (kroneckerPower (kroneckerPower T k) n) =
      rank (kroneckerPower T (n * k)) := by
  have h := rank_reindex (powerTupleEquiv I n k) (powerTupleEquiv J n k)
    (powerTupleEquiv L n k) (kroneckerPower (kroneckerPower T k) n)
  rw [kroneckerPower_mul_reindex] at h
  exact h.symm

/-- Splitting tuples of pairs identifies the power of a product with the
product of the two powers. -/
theorem kroneckerPower_kronecker_reindex [CommMonoid R]
    (T : Tensor R I J L) (S : Tensor R I' J' L') (n : ℕ) :
    reindex (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => I) (fun _ => I'))
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => J) (fun _ => J'))
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => L) (fun _ => L'))
      (kroneckerPower (kronecker T S) n) =
      kronecker (kroneckerPower T n) (kroneckerPower S n) := by
  funext i j l
  simp [reindex, kroneckerPower, kronecker, Equiv.arrowProdEquivProdArrow,
    Finset.prod_mul_distrib]

/-- Tensor rank respects the identification of a product power. -/
theorem rank_kroneckerPower_kronecker [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') (n : ℕ) :
    rank (kroneckerPower (kronecker T S) n) =
      rank (kronecker (kroneckerPower T n) (kroneckerPower S n)) := by
  have h := rank_reindex
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => I) (fun _ => I'))
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => J) (fun _ => J'))
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => L) (fun _ => L'))
    (kroneckerPower (kronecker T S) n)
  rw [kroneckerPower_kronecker_reindex] at h
  exact h.symm

/-- Over a nontrivial coefficient semiring the empty tensor power has rank one. -/
@[simp]
theorem rank_kroneckerPower_zero [CommSemiring R] [Nontrivial R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank (kroneckerPower T 0) = 1 := by
  apply le_antisymm (rank_kroneckerPower_zero_le T)
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  have hzero := (rank_eq_zero_iff _).mp h
  have he := congrFun (congrFun (congrFun hzero
    (Fin.elim0 : Fin 0 → I)) (Fin.elim0 : Fin 0 → J)) (Fin.elim0 : Fin 0 → L)
  simp at he

end MatrixMultiplication.Tensor
