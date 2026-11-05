module

public import Omega.Tensor.Rank
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Asymptotic rank and the matrix-multiplication exponent

These definitions follow the preliminaries of `material/main.tex` over an
arbitrary field. In particular, the base field is an explicit parameter of
`omega`; it has no cardinality or characteristic restriction.

The theorem `omega K ≤ (9 / 4 : ℝ)` for every `K` with `[Field K]` is proved
in `Omega.Main` from the tensor-theoretic and numerical results.
-/

@[expose] public section

namespace MatrixMultiplication

namespace Tensor

variable {R : Type*} {I J L : Type*}

/-- A Kronecker power, with its three bases indexed by tuples. -/
def kroneckerPower [CommMonoid R] (T : Tensor R I J L) (n : ℕ) :
    Tensor R (Fin n → I) (Fin n → J) (Fin n → L) :=
  fun i j k => ∏ t : Fin n, T (i t) (j t) (k t)

@[simp]
theorem kroneckerPower_zero_apply [CommMonoid R] (T : Tensor R I J L)
    (i : Fin 0 → I) (j : Fin 0 → J) (k : Fin 0 → L) :
    kroneckerPower T 0 i j k = 1 := by
  simp [kroneckerPower]

@[simp]
theorem kroneckerPower_one_apply [CommMonoid R] (T : Tensor R I J L)
    (i : Fin 1 → I) (j : Fin 1 → J) (k : Fin 1 → L) :
    kroneckerPower T 1 i j k = T (i 0) (j 0) (k 0) := by
  simp [kroneckerPower]

private def oneTupleEquiv (I : Type*) : (Fin 1 → I) ≃ I where
  toFun f := f 0
  invFun i := fun _ => i
  left_inv f := by
    funext a
    have : a = 0 := Subsingleton.elim _ _
    subst a
    rfl
  right_inv _ := rfl

@[simp]
theorem rank_kroneckerPower_one [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    rank (kroneckerPower T 1) = rank T := by
  have hr := rank_reindex (oneTupleEquiv I) (oneTupleEquiv J) (oneTupleEquiv L)
    (kroneckerPower T 1)
  have he : reindex (oneTupleEquiv I) (oneTupleEquiv J) (oneTupleEquiv L)
      (kroneckerPower T 1) = T := by
    funext i j k
    simp [reindex, oneTupleEquiv]
  rw [he] at hr
  exact hr.symm

/-- The positive-power rank roots appearing in the definition of asymptotic
rank. The restriction to `n ≥ 1` makes the root exponent unambiguous. -/
def rankRootValues [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) : Set ℝ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = (rank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ))}

theorem rankRootValues_nonempty [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    (rankRootValues T).Nonempty :=
  ⟨_, 1, by omega, rfl⟩

theorem rankRootValues_nonneg [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L)
    {x : ℝ} (hx : x ∈ rankRootValues T) : 0 ≤ x := by
  obtain ⟨n, _, rfl⟩ := hx
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem rankRootValues_bddBelow [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    BddBelow (rankRootValues T) :=
  ⟨0, fun _ hx => rankRootValues_nonneg T hx⟩

/-- Asymptotic tensor rank, using the infimum definition in the manuscript. -/
noncomputable def asymptoticRank [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) : ℝ :=
  sInf (rankRootValues T)

theorem asymptoticRank_nonneg [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    0 ≤ asymptoticRank T :=
  le_csInf (rankRootValues_nonempty T) (fun _ hx => rankRootValues_nonneg T hx)

/-- Each positive tensor power gives an upper bound on asymptotic rank. -/
theorem asymptoticRank_le_root [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L)
    {n : ℕ} (hn : 1 ≤ n) :
    asymptoticRank T ≤ (rank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ)) :=
  csInf_le (rankRootValues_bddBelow T) ⟨n, hn, rfl⟩

/-- Taking the first tensor power bounds asymptotic rank by ordinary rank. -/
theorem asymptoticRank_le_rank [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    asymptoticRank T ≤ rank T := by
  simpa using asymptoticRank_le_root T (n := 1) (by omega)

@[simp]
theorem asymptoticRank_zero [CommSemiring R] [Fintype I] [Fintype J] [Fintype L] :
    asymptoticRank (0 : Tensor R I J L) = 0 := by
  apply le_antisymm
  · simpa using asymptoticRank_le_rank (0 : Tensor R I J L)
  · exact asymptoticRank_nonneg _

end Tensor

/-- The matrix-multiplication exponent over `K`, exactly as defined in the
paper: the base-two logarithm of the asymptotic rank of `⟨2,2,2⟩`. -/
noncomputable def omega (K : Type*) [Field K] : ℝ :=
  Real.logb 2 (Tensor.asymptoticRank (Tensor.matrixMul K 2 2 2))

/-!
The size-independent power identity corresponding to `eq:omega-log-n`,
including the unit case, is proved in `Omega.ExponentSize`.
-/

end MatrixMultiplication
