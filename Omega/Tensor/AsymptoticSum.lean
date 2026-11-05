module

public import Omega.Tensor.AsymptoticDegeneration
public import Omega.Analysis.ExponentialBounds
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Asymptotic rank is subadditive

Expanding a tensor power of a sum produces terms indexed by subsets of its
coordinates. Separating a subset from its complement identifies each term
with a product of two tensor powers. Uniform exponential bounds then sum to
the desired bound, with one constant factor that disappears under roots.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R] {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]

private def indexedPower (T : Tensor R I J L) (α : Type*) [Fintype α] :
    Tensor R (α → I) (α → J) (α → L) :=
  fun i j k => ∏ a, T (i a) (j a) (k a)

private theorem rank_indexedPower (T : Tensor R I J L) (α : Type*)
    [Fintype α] [DecidableEq α] :
    rank (indexedPower T α) = rank (kroneckerPower T (Fintype.card α)) := by
  classical
  let e := Fintype.equivFin α
  have h := rank_reindex (Equiv.arrowCongr e (Equiv.refl I))
    (Equiv.arrowCongr e (Equiv.refl J)) (Equiv.arrowCongr e (Equiv.refl L))
    (indexedPower T α)
  have he : reindex (Equiv.arrowCongr e (Equiv.refl I))
      (Equiv.arrowCongr e (Equiv.refl J)) (Equiv.arrowCongr e (Equiv.refl L))
      (indexedPower T α) = kroneckerPower T (Fintype.card α) := by
    funext i j k
    change (∏ a, T (i (e a)) (j (e a)) (k (e a))) =
      ∏ a, T (i a) (j a) (k a)
    exact e.prod_comp (fun a => T (i a) (j a) (k a))
  rw [he] at h
  exact h.symm

private theorem rank_mixedPower_le (T S : Tensor R I J L) (n : ℕ)
    (s : Finset (Fin n)) :
    rank (fun (i : Fin n → I) (j : Fin n → J) (k : Fin n → L) =>
      (∏ a ∈ s, T (i a) (j a) (k a)) *
        ∏ a ∈ sᶜ, S (i a) (j a) (k a)) ≤
      rank (kroneckerPower T s.card) * rank (kroneckerPower S sᶜ.card) := by
  classical
  let eI := Equiv.piEquivPiSubtypeProd (fun a : Fin n => a ∈ s) (fun _ => I)
  let eJ := Equiv.piEquivPiSubtypeProd (fun a : Fin n => a ∈ s) (fun _ => J)
  let eL := Equiv.piEquivPiSubtypeProd (fun a : Fin n => a ∈ s) (fun _ => L)
  have he : (fun (i : Fin n → I) (j : Fin n → J) (k : Fin n → L) =>
      (∏ a ∈ s, T (i a) (j a) (k a)) *
        ∏ a ∈ sᶜ, S (i a) (j a) (k a)) =
      reindex eI.symm eJ.symm eL.symm
        (kronecker (indexedPower T {a : Fin n // a ∈ s})
          (indexedPower S {a : Fin n // a ∉ s})) := by
    funext i j k
    change _ = (∏ a : {a : Fin n // a ∈ s}, T (i a) (j a) (k a)) *
      ∏ a : {a : Fin n // a ∉ s}, S (i a) (j a) (k a)
    rw [Finset.prod_subtype s (fun _ => Iff.rfl),
      Finset.prod_subtype sᶜ (fun _ => Finset.mem_compl)]
  rw [he, rank_reindex]
  have h := rank_kronecker_le (indexedPower T {a : Fin n // a ∈ s})
    (indexedPower S {a : Fin n // a ∉ s})
  rw [rank_indexedPower, rank_indexedPower, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at h
  rw [Finset.card_compl, Fintype.card_fin]
  exact h

/-- Every positive rate above asymptotic rank bounds all power ranks up to
a fixed positive factor. -/
theorem exists_rank_power_exponential_bound (T : Tensor R I J L) {r : ℝ}
    (hr : asymptoticRank T < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, (rank (kroneckerPower T n) : ℝ) ≤ C * r ^ n :=
  MatrixMultiplication.exists_pos_exponential_bound (fun _ => Nat.cast_nonneg _)
    (asymptoticRank_eq_limit T) ((asymptoticRank_nonneg T).trans_lt hr) hr

/-- Expanding a power of a sum and grouping coordinates bounds its rank by
the sum of the corresponding products of power ranks. -/
theorem rank_kroneckerPower_add_le_sum (T S : Tensor R I J L) (n : ℕ) :
    rank (kroneckerPower (T + S) n) ≤
      ∑ s : Finset (Fin n),
        rank (kroneckerPower T s.card) * rank (kroneckerPower S sᶜ.card) := by
  classical
  have he : kroneckerPower (T + S) n = ∑ s : Finset (Fin n),
      fun (i : Fin n → I) (j : Fin n → J) (k : Fin n → L) =>
        (∏ a ∈ s, T (i a) (j a) (k a)) *
          ∏ a ∈ sᶜ, S (i a) (j a) (k a) := by
    funext i j k
    simp only [kroneckerPower, Pi.add_apply, Finset.sum_apply]
    exact Fintype.prod_add _ _
  rw [he]
  apply (rank_sum_le _ _).trans
  exact Finset.sum_le_sum fun s _ => rank_mixedPower_le T S n s

private theorem asymptoticRank_add_le_rates (T S : Tensor R I J L) {a b : ℝ}
    (ha : asymptoticRank T < a) (hb : asymptoticRank S < b) :
    asymptoticRank (T + S) ≤ a + b := by
  have ha0 := (asymptoticRank_nonneg T).trans_lt ha
  have hb0 := (asymptoticRank_nonneg S).trans_lt hb
  obtain ⟨C, hC, hT⟩ := exists_rank_power_exponential_bound T ha
  obtain ⟨D, hD, hS⟩ := exists_rank_power_exponential_bound S hb
  apply MatrixMultiplication.root_limit_le_of_exponential_bound
    (fun _ => Nat.cast_nonneg _) (asymptoticRank_eq_limit (T + S))
    (mul_pos hC hD) (add_nonneg ha0.le hb0.le)
  intro n
  calc
    (rank (kroneckerPower (T + S) n) : ℝ) ≤
        ∑ s : Finset (Fin n), (rank (kroneckerPower T s.card) : ℝ) *
          (rank (kroneckerPower S sᶜ.card) : ℝ) := by
      exact_mod_cast rank_kroneckerPower_add_le_sum T S n
    _ ≤ ∑ s : Finset (Fin n), (C * a ^ s.card) * (D * b ^ sᶜ.card) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul (hT s.card) (hS sᶜ.card) (Nat.cast_nonneg _)
        (mul_nonneg hC.le (pow_nonneg ha0.le _))
    _ = C * D * (∑ s : Finset (Fin n), a ^ s.card * b ^ sᶜ.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = C * D * (a + b) ^ n := by
      congr 1
      simpa using (Fintype.prod_add (fun _ : Fin n => a) (fun _ : Fin n => b)).symm

/-- Asymptotic rank is subadditive for tensors in the same three spaces. -/
theorem asymptoticRank_add_le (T S : Tensor R I J L) :
    asymptoticRank (T + S) ≤ asymptoticRank T + asymptoticRank S := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := asymptoticRank_add_le_rates T S
    (a := asymptoticRank T + ε / 2) (b := asymptoticRank S + ε / 2)
    (by linarith) (by linarith)
  linarith

/-- Asymptotic rank is subadditive for ordinary direct sums, over every
commutative semiring and hence over every field. -/
theorem asymptoticRank_directSum_le [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    asymptoticRank (directSum T S) ≤ asymptoticRank T + asymptoticRank S := by
  have he : directSum T S = directSum T (0 : Tensor R I' J' L') +
      directSum (0 : Tensor R I J L) S := by
    funext i j k
    cases i <;> cases j <;> cases k <;> simp [directSum]
  rw [he]
  exact (asymptoticRank_add_le _ _).trans
    (add_le_add (asymptoticRank_mono (restricts_directSum_zero T))
      (asymptoticRank_mono (restricts_zero_directSum S)))

end MatrixMultiplication.Tensor
