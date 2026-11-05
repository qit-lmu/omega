module

public import Omega.Exponent
public import Omega.Tensor.RankOperations
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Kronecker powers and their ranks

Splitting a tuple of length `m + n` into two tuples identifies the corresponding
tensor power with the Kronecker product of the two smaller powers.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {I J L : Type*}

/-- Splitting the coordinate tuples identifies a power with a Kronecker product. -/
theorem kroneckerPower_add_reindex [CommMonoid R]
    (T : Tensor R I J L) (m n : ℕ) :
    reindex (Fin.appendEquiv m n).symm (Fin.appendEquiv m n).symm
      (Fin.appendEquiv m n).symm (kroneckerPower T (m + n)) =
      kronecker (kroneckerPower T m) (kroneckerPower T n) := by
  funext i j k
  simp [reindex, kroneckerPower, kronecker, Fin.prod_univ_add]

/-- The rank sequence of tensor powers is submultiplicative. -/
theorem rank_kroneckerPower_add_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (m n : ℕ) :
    rank (kroneckerPower T (m + n)) ≤
      rank (kroneckerPower T m) * rank (kroneckerPower T n) := by
  have h := rank_reindex (Fin.appendEquiv m n).symm (Fin.appendEquiv m n).symm
    (Fin.appendEquiv m n).symm (kroneckerPower T (m + n))
  rw [kroneckerPower_add_reindex] at h
  rw [← h]
  exact rank_kronecker_le _ _

/-- The zeroth power is a pure tensor, even when the original spaces are empty. -/
theorem rank_kroneckerPower_zero_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank (kroneckerPower T 0) ≤ 1 := by
  have h : kroneckerPower T 0 = pure (fun _ => (1 : R)) (fun _ => 1) (fun _ => 1) := by
    funext i j k
    simp [kroneckerPower, pure]
  rw [h]
  exact rank_pure_le_one _ _ _

/-- A rank decomposition can be tensored to bound every tensor power. -/
theorem rank_kroneckerPower_le [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) (n : ℕ) :
    rank (kroneckerPower T n) ≤ rank T ^ n := by
  induction n with
  | zero => simpa using rank_kroneckerPower_zero_le T
  | succ n ih =>
      calc
        rank (kroneckerPower T (n + 1)) ≤
            rank (kroneckerPower T n) * rank (kroneckerPower T 1) :=
          rank_kroneckerPower_add_le T n 1
        _ ≤ rank T ^ n * rank T := Nat.mul_le_mul ih (by simp)
        _ = rank T ^ (n + 1) := (pow_succ _ _).symm

end MatrixMultiplication.Tensor
