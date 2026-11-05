module

public import Omega.Tensor.AsymptoticDegeneration
public import Omega.Tensor.RationalDegeneration

/-!
# Border rank and its asymptotic lower bound

Border rank is the least size of a diagonal tensor degenerating to the given
tensor, with the polynomial-witness definition of degeneration. Monotonicity
of asymptotic rank immediately gives the bound used in the manuscript.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]

/-- Every finite tensor has a diagonal degeneration source. -/
theorem exists_diagonal_degenerates (T : Tensor R I J L) :
    ∃ r : ℕ, Degenerates (diagonal R r) T :=
  ⟨rank T, (diagonal_restricts_of_rank T).degenerates⟩

/-- Border rank as the minimum size of a diagonal degeneration source. -/
noncomputable def borderRank (T : Tensor R I J L) : ℕ := by
  classical
  exact Nat.find (exists_diagonal_degenerates T)

/-- The minimum in the definition of border rank is attained. -/
theorem diagonal_degenerates_of_borderRank (T : Tensor R I J L) :
    Degenerates (diagonal R (borderRank T)) T := by
  classical
  exact Nat.find_spec (exists_diagonal_degenerates T)

/-- A diagonal degeneration source bounds border rank. -/
theorem borderRank_le_of_diagonal_degenerates {T : Tensor R I J L} {r : ℕ}
    (h : Degenerates (diagonal R r) T) : borderRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_diagonal_degenerates T) h

/-- An ordinary rank decomposition is also a border-rank witness. -/
theorem borderRank_le_rank (T : Tensor R I J L) : borderRank T ≤ rank T :=
  borderRank_le_of_diagonal_degenerates (diagonal_restricts_of_rank T).degenerates

/-- Border rank is monotone under degeneration. -/
theorem borderRank_mono_degeneration [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Degenerates T S) : borderRank S ≤ borderRank T :=
  borderRank_le_of_diagonal_degenerates ((diagonal_degenerates_of_borderRank T).trans h)

/-- The manuscript's asymptotic-rank bound by border rank, over every field. -/
theorem asymptoticRank_le_borderRank (T : Tensor R I J L) :
    asymptoticRank T ≤ (borderRank T : ℝ) := by
  calc
    asymptoticRank T ≤ asymptoticRank (diagonal R (borderRank T)) :=
      asymptoticRank_mono_degeneration (diagonal_degenerates_of_borderRank T)
    _ ≤ (rank (diagonal R (borderRank T)) : ℝ) := asymptoticRank_le_rank _
    _ ≤ (borderRank T : ℝ) := Nat.cast_le.mpr (rank_diagonal_le _)

/-- A rank decomposition over the rational function field specializes to a
border-rank witness over the base field, including for the zero tensor. -/
theorem borderRank_le_rank_liftRational {K : Type*} [Field K]
    (T : Tensor K I J L) : borderRank T ≤ rank (liftRational T) := by
  apply borderRank_le_of_diagonal_degenerates
  apply degenerates_of_restricts_liftRational
  have hdiag : liftRational (diagonal K (rank (liftRational T))) =
      diagonal (RatFunc K) (rank (liftRational T)) := by
    funext i j k
    simp [liftRational, diagonal]
  rw [hdiag]
  exact diagonal_restricts_of_rank (liftRational T)

end MatrixMultiplication.Tensor
