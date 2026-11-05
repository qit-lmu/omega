module

public import Omega.Tensor.Flattening
public import Omega.Tensor.BorderRank
import Mathlib.Tactic.FinCases

/-!
# Flattening lower bounds

The rank of each flattening is multiplicative under tensor powers and bounded
by the corresponding tensor rank. Taking positive-power roots gives a lower
bound for their infimum, the asymptotic rank. The bound by border rank then
follows from the previously checked degeneration argument.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K] {I J L : Type*}
variable [Fintype I] [Fintype J] [Fintype L]

private theorem matrix_rank_const_one {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Subsingleton A] [Nonempty B] [Subsingleton B] :
    Matrix.rank (fun (_ : A) (_ : B) => (1 : K)) = 1 := by
  classical
  let : Unique A := ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  let : Unique B := ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  have h := Matrix.rank_submatrix (1 : Matrix Unit Unit K)
    (Equiv.ofUnique A Unit) (Equiv.ofUnique B Unit)
  have he : (1 : Matrix Unit Unit K).submatrix (Equiv.ofUnique A Unit)
      (Equiv.ofUnique B Unit) = (fun (_ : A) (_ : B) => (1 : K)) := by
    ext i j
    simp [Matrix.submatrix]
  rw [he] at h
  simpa only [Matrix.rank_one, Fintype.card_unit] using h

/-- Every flattening of the zeroth tensor power has rank one. -/
@[simp]
theorem flatteningRank_kroneckerPower_zero (T : Tensor K I J L) (a : Fin 3) :
    flatteningRank (kroneckerPower T 0) a = 1 := by
  have hT : kroneckerPower T 0 = fun _ _ _ => (1 : K) := by
    funext i j k
    simp [kroneckerPower]
  rw [hT]
  fin_cases a <;>
    exact matrix_rank_const_one

/-- The singleton-tuple reindexing preserves the three flattening ranks. -/
@[simp]
theorem flatteningRank_kroneckerPower_one (T : Tensor K I J L) (a : Fin 3) :
    flatteningRank (kroneckerPower T 1) a = flatteningRank T a := by
  have h := flatteningRank_reindex (Equiv.funUnique (Fin 1) I)
    (Equiv.funUnique (Fin 1) J) (Equiv.funUnique (Fin 1) L)
    (kroneckerPower T 1) a
  have hT : reindex (Equiv.funUnique (Fin 1) I) (Equiv.funUnique (Fin 1) J)
      (Equiv.funUnique (Fin 1) L) (kroneckerPower T 1) = T := by
    funext i j k
    simp [reindex, kroneckerPower, Equiv.funUnique, Equiv.piUnique]
  rw [hT] at h
  exact h.symm

/-- Each flattening rank is exactly multiplicative under tensor powers. -/
theorem flatteningRank_kroneckerPower (T : Tensor K I J L) (a : Fin 3) (n : ℕ) :
    flatteningRank (kroneckerPower T n) a = flatteningRank T a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := flatteningRank_reindex (Fin.appendEquiv n 1).symm
        (Fin.appendEquiv n 1).symm (Fin.appendEquiv n 1).symm
        (kroneckerPower T (n + 1)) a
      rw [kroneckerPower_add_reindex, flatteningRank_kronecker] at h
      rw [← h, ih, flatteningRank_kroneckerPower_one, pow_succ]

/-- Lemma 2.3: a flattening rank bounds the asymptotic tensor rank from below. -/
theorem flatteningRank_le_asymptoticRank (T : Tensor K I J L) (a : Fin 3) :
    (flatteningRank T a : ℝ) ≤ asymptoticRank T := by
  apply le_csInf (rankRootValues_nonempty T)
  rintro _ ⟨n, hn, rfl⟩
  have h : flatteningRank T a ^ n ≤ rank (kroneckerPower T n) := by
    rw [← flatteningRank_kroneckerPower]
    exact flatteningRank_le_rank _ _
  have h' : (flatteningRank T a : ℝ) ^ n ≤ (rank (kroneckerPower T n) : ℝ) := by
    exact_mod_cast h
  have hroot := Real.rpow_le_rpow (by positivity) h'
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by omega : n ≠ 0)] at hroot
  simpa only [one_div] using hroot

/-- Lemma 2.3: a flattening rank also bounds the polynomial-witness border rank. -/
theorem flatteningRank_le_borderRank (T : Tensor K I J L) (a : Fin 3) :
    flatteningRank T a ≤ borderRank T := by
  exact_mod_cast (flatteningRank_le_asymptoticRank T a).trans
    (asymptoticRank_le_borderRank T)

end MatrixMultiplication.Tensor
