module

public import Omega.Tensor.FlatteningExamples
public import Mathlib.Order.Lattice.Nat

/-!
# Subrank, border subrank, and asymptotic subrank

These are the three maxima/supremum definitions in manuscript Definition 2.1.
The finite maxima are attained: zero is always admissible, and rank bounds
every diagonal restriction target (border rank bounds degeneration targets).
The positive-power subrank roots are uniformly bounded, so their real
supremum is also the usual finite supremum.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]

/-- Every tensor restricts to the size-zero diagonal. -/
theorem restricts_diagonal_zero (T : Tensor K I J L) :
    Restricts T (diagonal K 0) := by
  refine ⟨0, 0, 0, ?_⟩
  funext i
  exact Fin.elim0 i

/-- A diagonal restriction target has size at most the source rank. -/
theorem diagonal_size_le_rank {T : Tensor K I J L} {r : ℕ}
    (h : Restricts T (diagonal K r)) : r ≤ rank T := by
  simpa using rank_mono h

/-- A diagonal degeneration target has size at most the source border rank. -/
theorem diagonal_size_le_borderRank {T : Tensor K I J L} {r : ℕ}
    (h : Degenerates T (diagonal K r)) : r ≤ borderRank T := by
  simpa using borderRank_mono_degeneration h

theorem subrankValues_nonempty (T : Tensor K I J L) :
    {r : ℕ | Restricts T (diagonal K r)}.Nonempty :=
  ⟨0, restricts_diagonal_zero T⟩

theorem subrankValues_bddAbove (T : Tensor K I J L) :
    BddAbove {r : ℕ | Restricts T (diagonal K r)} :=
  ⟨rank T, fun _ h => diagonal_size_le_rank h⟩

/-- Subrank is the maximum size of a diagonal restriction target. -/
noncomputable def subrank (T : Tensor K I J L) : ℕ :=
  sSup {r : ℕ | Restricts T (diagonal K r)}

/-- The maximum in the definition of subrank is attained. -/
theorem restricts_diagonal_of_subrank (T : Tensor K I J L) :
    Restricts T (diagonal K (subrank T)) :=
  Nat.sSup_mem (subrankValues_nonempty T) (subrankValues_bddAbove T)

theorem le_subrank_of_restricts_diagonal {T : Tensor K I J L} {r : ℕ}
    (h : Restricts T (diagonal K r)) : r ≤ subrank T :=
  le_csSup (subrankValues_bddAbove T) h

theorem subrank_le_rank (T : Tensor K I J L) : subrank T ≤ rank T :=
  diagonal_size_le_rank (restricts_diagonal_of_subrank T)

/-- Restriction cannot increase subrank. -/
theorem subrank_mono [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'} (h : Restricts T S) :
    subrank S ≤ subrank T :=
  le_subrank_of_restricts_diagonal (h.trans (restricts_diagonal_of_subrank S))

theorem subrank_eq_of_equivalent [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'} (h : Equivalent T S) :
    subrank T = subrank S :=
  le_antisymm (subrank_mono h.2) (subrank_mono h.1)

theorem subrank_reindex [Fintype I'] [Fintype J'] [Fintype L']
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor K I J L) :
    subrank (reindex eI eJ eL T) = subrank T := by
  apply subrank_eq_of_equivalent
  constructor
  · simpa only [reindex_symm] using
      restricts_reindex eI.symm eJ.symm eL.symm (reindex eI eJ eL T)
  · exact restricts_reindex eI eJ eL T

@[simp]
theorem subrank_kroneckerPower_one (T : Tensor K I J L) :
    subrank (kroneckerPower T 1) = subrank T := by
  have h := subrank_reindex (Equiv.funUnique (Fin 1) I)
    (Equiv.funUnique (Fin 1) J) (Equiv.funUnique (Fin 1) L) (kroneckerPower T 1)
  have hT : reindex (Equiv.funUnique (Fin 1) I) (Equiv.funUnique (Fin 1) J)
      (Equiv.funUnique (Fin 1) L) (kroneckerPower T 1) = T := by
    funext i j k
    simp [reindex]
  rw [hT] at h
  exact h.symm

@[simp]
theorem subrank_zero : subrank (0 : Tensor K I J L) = 0 := by
  simpa using subrank_le_rank (0 : Tensor K I J L)

@[simp]
theorem subrank_diagonal (r : ℕ) : subrank (diagonal K r) = r := by
  apply le_antisymm
  · simpa using subrank_le_rank (diagonal K r)
  · exact le_subrank_of_restricts_diagonal (Restricts.refl _)

theorem borderSubrankValues_nonempty (T : Tensor K I J L) :
    {r : ℕ | Degenerates T (diagonal K r)}.Nonempty :=
  ⟨0, (restricts_diagonal_zero T).degenerates⟩

theorem borderSubrankValues_bddAbove (T : Tensor K I J L) :
    BddAbove {r : ℕ | Degenerates T (diagonal K r)} :=
  ⟨borderRank T, fun _ h => diagonal_size_le_borderRank h⟩

/-- Border subrank is the maximum size of a diagonal degeneration target. -/
noncomputable def borderSubrank (T : Tensor K I J L) : ℕ :=
  sSup {r : ℕ | Degenerates T (diagonal K r)}

/-- The maximum in the definition of border subrank is attained. -/
theorem degenerates_diagonal_of_borderSubrank (T : Tensor K I J L) :
    Degenerates T (diagonal K (borderSubrank T)) :=
  Nat.sSup_mem (borderSubrankValues_nonempty T) (borderSubrankValues_bddAbove T)

theorem le_borderSubrank_of_degenerates_diagonal {T : Tensor K I J L} {r : ℕ}
    (h : Degenerates T (diagonal K r)) : r ≤ borderSubrank T :=
  le_csSup (borderSubrankValues_bddAbove T) h

theorem borderSubrank_le_borderRank (T : Tensor K I J L) :
    borderSubrank T ≤ borderRank T :=
  diagonal_size_le_borderRank (degenerates_diagonal_of_borderSubrank T)

theorem subrank_le_borderSubrank (T : Tensor K I J L) :
    subrank T ≤ borderSubrank T :=
  le_borderSubrank_of_degenerates_diagonal (restricts_diagonal_of_subrank T).degenerates

/-- Degeneration cannot increase border subrank. -/
theorem borderSubrank_mono [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'} (h : Degenerates T S) :
    borderSubrank S ≤ borderSubrank T :=
  le_borderSubrank_of_degenerates_diagonal
    (h.trans (degenerates_diagonal_of_borderSubrank S))

@[simp]
theorem borderSubrank_zero : borderSubrank (0 : Tensor K I J L) = 0 := by
  have h := (borderSubrank_le_borderRank (0 : Tensor K I J L)).trans
    (borderRank_le_rank _)
  simpa using h

@[simp]
theorem borderSubrank_diagonal (r : ℕ) : borderSubrank (diagonal K r) = r := by
  apply le_antisymm
  · simpa using borderSubrank_le_borderRank (diagonal K r)
  · exact le_borderSubrank_of_degenerates_diagonal (Degenerates.refl _)

/-- The positive-power subrank roots used in asymptotic subrank. -/
def subrankRootValues (T : Tensor K I J L) : Set ℝ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = (subrank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ))}

theorem subrankRootValues_nonempty (T : Tensor K I J L) :
    (subrankRootValues T).Nonempty :=
  ⟨_, 1, by omega, rfl⟩

theorem subrankRootValues_nonneg (T : Tensor K I J L)
    {x : ℝ} (hx : x ∈ subrankRootValues T) : 0 ≤ x := by
  obtain ⟨n, _, rfl⟩ := hx
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- All subrank roots are bounded by the original tensor rank. -/
theorem subrankRootValues_le_rank (T : Tensor K I J L)
    {x : ℝ} (hx : x ∈ subrankRootValues T) : x ≤ rank T := by
  obtain ⟨n, hn, rfl⟩ := hx
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hb : (subrank (kroneckerPower T n) : ℝ) ≤ (rank T : ℝ) ^ n := by
    exact_mod_cast (subrank_le_rank (kroneckerPower T n)).trans
      (rank_kroneckerPower_le T n)
  calc
    _ ≤ ((rank T : ℝ) ^ n) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by positivity)
    _ = rank T := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      simp [hn0]

theorem subrankRootValues_bddAbove (T : Tensor K I J L) :
    BddAbove (subrankRootValues T) :=
  ⟨rank T, fun _ h => subrankRootValues_le_rank T h⟩

/-- Asymptotic subrank, exactly the supremum definition in the manuscript. -/
noncomputable def asymptoticSubrank (T : Tensor K I J L) : ℝ :=
  sSup (subrankRootValues T)

theorem root_le_asymptoticSubrank (T : Tensor K I J L) {n : ℕ} (hn : 1 ≤ n) :
    (subrank (kroneckerPower T n) : ℝ) ^ (1 / (n : ℝ)) ≤ asymptoticSubrank T :=
  le_csSup (subrankRootValues_bddAbove T) ⟨n, hn, rfl⟩

theorem asymptoticSubrank_nonneg (T : Tensor K I J L) :
    0 ≤ asymptoticSubrank T :=
  (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
    (root_le_asymptoticSubrank T (n := 1) (by omega))

theorem subrank_le_asymptoticSubrank (T : Tensor K I J L) :
    (subrank T : ℝ) ≤ asymptoticSubrank T := by
  simpa using root_le_asymptoticSubrank T (n := 1) (by omega)

theorem asymptoticSubrank_le_rank (T : Tensor K I J L) :
    asymptoticSubrank T ≤ rank T :=
  csSup_le (subrankRootValues_nonempty T) (fun _ h => subrankRootValues_le_rank T h)

@[simp]
theorem asymptoticSubrank_zero : asymptoticSubrank (0 : Tensor K I J L) = 0 := by
  apply le_antisymm
  · simpa using asymptoticSubrank_le_rank (0 : Tensor K I J L)
  · exact asymptoticSubrank_nonneg _

@[simp]
theorem asymptoticSubrank_diagonal (r : ℕ) :
    asymptoticSubrank (diagonal K r) = r := by
  apply le_antisymm
  · simpa using asymptoticSubrank_le_rank (diagonal K r)
  · simpa using subrank_le_asymptoticSubrank (diagonal K r)

end MatrixMultiplication.Tensor
