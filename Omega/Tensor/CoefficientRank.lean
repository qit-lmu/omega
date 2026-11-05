module

public import Omega.Tensor.Degeneration
public import Omega.Tensor.RankOperations
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Extracting coefficients of polynomial restrictions

The coefficient of order `d` of a polynomial restriction is a sum of
`(d + 2).choose 2` ordinary restrictions, also bounded by `(d + 1)^2`.
These estimates are independent of the number
of elements of the coefficient field; no evaluations or interpolation are used.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {R : Type*} {I J L I' J' L' : Type*}

/-- Take the same polynomial coefficient in every entry of a factor map. -/
def matrixCoefficient [Semiring R] (A : Matrix I' I R[X]) (d : ℕ) : Matrix I' I R :=
  fun i j => (A i j).coeff d

private theorem sum_fintype_three_comm [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype L] {α : Type*}
    (s : Finset α) (f : I → J → L → α → R) :
    (∑ i, ∑ j, ∑ k, ∑ a ∈ s, f i j k a) =
      ∑ a ∈ s, ∑ i, ∑ j, ∑ k, f i j k a := by
  calc
    _ = ∑ i, ∑ j, ∑ a ∈ s, ∑ k, f i j k a := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ a ∈ s, ∑ j, ∑ k, f i j k a := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Coefficient extraction expands into ordinary restrictions, indexed by
the two antidiagonals in the product of three polynomial factor maps. -/
theorem coefficient_map_liftPolynomial [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R[X]) (B : Matrix J' J R[X]) (D : Matrix L' L R[X])
    (T : Tensor R I J L) (d : ℕ) :
    coefficient (map A B D (liftPolynomial T)) d =
      ∑ p ∈ Finset.antidiagonal d, ∑ q ∈ Finset.antidiagonal p.1,
        map (matrixCoefficient A q.1) (matrixCoefficient B q.2)
          (matrixCoefficient D p.2) T := by
  funext i j k
  simp only [coefficient, map, liftPolynomial, matrixCoefficient,
    Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Finset.sum_apply]
  simp only [Polynomial.coeff_mul, Finset.sum_mul]
  rw [sum_fintype_three_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact sum_fintype_three_comm _ _

/-- The exact number of triples of coefficient degrees gives the manuscript's
binomial rank bound, including coefficient order zero. -/
theorem rank_coefficient_map_le_choose [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I' I R[X]) (B : Matrix J' J R[X]) (D : Matrix L' L R[X])
    (T : Tensor R I J L) (d : ℕ) :
    rank (coefficient (map A B D (liftPolynomial T)) d) ≤
      (d + 2).choose 2 * rank T := by
  have hcount : (∑ p ∈ Finset.antidiagonal d, (p.1 + 1)) = (d + 2).choose 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simpa [Nat.add_assoc, Nat.succ_eq_add_one] using Nat.sum_range_add_choose d 1
  rw [coefficient_map_liftPolynomial]
  calc
    _ ≤ ∑ p ∈ Finset.antidiagonal d,
        rank (∑ q ∈ Finset.antidiagonal p.1,
          map (matrixCoefficient A q.1) (matrixCoefficient B q.2)
            (matrixCoefficient D p.2) T) := rank_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal d, ∑ q ∈ Finset.antidiagonal p.1,
        rank (map (matrixCoefficient A q.1) (matrixCoefficient B q.2)
          (matrixCoefficient D p.2) T) := by
      exact Finset.sum_le_sum fun _ _ => rank_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal d, ∑ _q ∈ Finset.antidiagonal p.1, rank T := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.sum_le_sum fun _ _ => rank_map_le _ _ _ _
    _ = (∑ p ∈ Finset.antidiagonal d, (p.1 + 1)) * rank T := by
      simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_id]
      rw [Finset.sum_mul]
    _ = (d + 2).choose 2 * rank T := by rw [hcount]

/-- A coefficient of a polynomial restriction costs only a quadratic factor
in its order. The source tensor is never evaluated over an extension field. -/
theorem rank_coefficient_map_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (A : Matrix I' I R[X]) (B : Matrix J' J R[X]) (D : Matrix L' L R[X])
    (T : Tensor R I J L) (d : ℕ) :
    rank (coefficient (map A B D (liftPolynomial T)) d) ≤ (d + 1) ^ 2 * rank T := by
  rw [coefficient_map_liftPolynomial]
  calc
    _ ≤ ∑ p ∈ Finset.antidiagonal d,
        rank (∑ q ∈ Finset.antidiagonal p.1,
          map (matrixCoefficient A q.1) (matrixCoefficient B q.2)
            (matrixCoefficient D p.2) T) := rank_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal d, ∑ q ∈ Finset.antidiagonal p.1,
        rank (map (matrixCoefficient A q.1) (matrixCoefficient B q.2)
          (matrixCoefficient D p.2) T) := by
      exact Finset.sum_le_sum fun _ _ => rank_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal d, ∑ _q ∈ Finset.antidiagonal p.1, rank T := by
      exact Finset.sum_le_sum fun _ _ =>
        Finset.sum_le_sum fun _ _ => rank_map_le _ _ _ _
    _ = ∑ p ∈ Finset.antidiagonal d, (p.1 + 1) * rank T := by simp
    _ ≤ ∑ _p ∈ Finset.antidiagonal d, (d + 1) * rank T := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : p.1 + p.2 = d := Finset.mem_antidiagonal.mp hp
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (by omega) _)
    _ = (d + 1) ^ 2 * rank T := by simp [pow_two, Nat.mul_assoc]

/-- The leading coefficient of an order-`d` degeneration costs at most
`(d + 2).choose 2` times the source rank. -/
theorem DegenerationWitness.rank_le_choose [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) : rank S ≤ (w.order + 2).choose 2 * rank T := by
  calc
    rank S = rank (coefficient (map w.firstMap w.secondMap w.thirdMap
        (liftPolynomial T)) w.order) := congrArg rank w.leadingCoefficient.symm
    _ ≤ _ := rank_coefficient_map_le_choose _ _ _ _ _

/-- Extracting the leading coefficient of a degeneration witness bounds the
target rank by a polynomial in the witness order times the source rank. -/
theorem DegenerationWitness.rank_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) : rank S ≤ (w.order + 1) ^ 2 * rank T := by
  calc
    rank S = rank (coefficient (map w.firstMap w.secondMap w.thirdMap
        (liftPolynomial T)) w.order) := congrArg rank w.leadingCoefficient.symm
    _ ≤ _ := rank_coefficient_map_le _ _ _ _ _

end MatrixMultiplication.Tensor
