module

public import Omega.Tensor.FlatteningExamples

/-!
# Nonzero tensors and the unit diagonal

A nonzero coefficient can be selected and rescaled to obtain the unit tensor.
Products and powers preserve nonzero tensors over fields, including power zero.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*}

/-- A nonzero coefficient tensor has a nonzero coefficient. -/
theorem exists_coeff_ne_zero [Zero K] {T : Tensor K I J L} (hT : T ≠ 0) :
    ∃ i j k, T i j k ≠ 0 := by
  classical
  by_contra! h
  apply hT
  funext i j k
  exact h i j k

/-- Select a nonzero coefficient and rescale it to the unit diagonal tensor. -/
theorem restricts_diagonal_one_of_ne_zero [Field K]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (hT : T ≠ 0) : Restricts T (diagonal K 1) := by
  classical
  obtain ⟨i, j, k, h⟩ := exists_coeff_ne_zero hT
  refine ⟨(fun _ x => if x = i then (T i j k)⁻¹ else 0),
    (fun _ y => if y = j then 1 else 0),
    (fun _ z => if z = k then 1 else 0), ?_⟩
  funext a b c
  simp [map, diagonal, h, Subsingleton.elim a b, Subsingleton.elim b c]

/-- Products of nonzero tensors over a field are nonzero. -/
theorem kronecker_ne_zero [Field K]
    {T : Tensor K I J L} {S : Tensor K I' J' L'} (hT : T ≠ 0) (hS : S ≠ 0) :
    kronecker T S ≠ 0 := by
  obtain ⟨i, j, k, ht⟩ := exists_coeff_ne_zero hT
  obtain ⟨i', j', k', hs⟩ := exists_coeff_ne_zero hS
  intro h
  have hc := congrFun (congrFun (congrFun h (i, i')) (j, j')) (k, k')
  exact mul_ne_zero ht hs hc

/-- Every power of a nonzero tensor over a field is nonzero. -/
theorem kroneckerPower_ne_zero [Field K]
    {T : Tensor K I J L} (hT : T ≠ 0) (n : ℕ) : kroneckerPower T n ≠ 0 := by
  obtain ⟨i, j, k, ht⟩ := exists_coeff_ne_zero hT
  intro h
  have hc := congrFun (congrFun (congrFun h (fun _ => i)) (fun _ => j)) (fun _ => k)
  simp only [kroneckerPower, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Pi.zero_apply] at hc
  exact pow_ne_zero n ht hc

/-- A positive diagonal tensor is nonzero. -/
theorem diagonal_ne_zero [Field K] {a : ℕ} (ha : 0 < a) : diagonal K a ≠ 0 := by
  intro h
  have hc := congrFun (congrFun (congrFun h ⟨0, ha⟩) ⟨0, ha⟩) ⟨0, ha⟩
  simp [diagonal] at hc

/-- Every nonzero tensor has asymptotic rank at least one. -/
theorem one_le_asymptoticRank_of_ne_zero [Field K]
    [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (hT : T ≠ 0) : 1 ≤ asymptoticRank T := by
  simpa only [asymptoticRank_diagonal, Nat.cast_one] using
    asymptoticRank_mono (restricts_diagonal_one_of_ne_zero T hT)

end MatrixMultiplication.Tensor
