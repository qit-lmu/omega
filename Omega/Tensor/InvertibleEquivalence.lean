module

public import Omega.Tensor.FlatteningDegeneration
public import Omega.LinearAlgebra.MatrixExtension

/-!
# Mutual restriction and invertible factor maps

For tensors in the same ambient spaces, mutual restriction is equivalent
to an invertible change in each factor. A restriction between tensors with
equal flattening ranks loses no information on any factor support. Its
factor maps can therefore be replaced by ambient automorphisms.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {K I J L : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq L]

omit [DecidableEq I] in
private theorem flatteningFirst_map_first (T : Tensor K I J L) (A : Matrix I I K) :
    (flatteningFirst (map A 1 1 T)).transpose = A * (flatteningFirst T).transpose := by
  ext i jk
  simp [flatteningFirst, map, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]

omit [DecidableEq J] in
private theorem flatteningSecond_map_second (T : Tensor K I J L) (B : Matrix J J K) :
    (flatteningSecond (map 1 B 1 T)).transpose = B * (flatteningSecond T).transpose := by
  ext j ik
  simp [flatteningSecond, map, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]

omit [DecidableEq L] in
private theorem flatteningThird_map_third (T : Tensor K I J L) (C : Matrix L L K) :
    (flatteningThird (map 1 1 C T)).transpose = C * (flatteningThird T).transpose := by
  ext k ij
  simp [flatteningThird, map, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]

private theorem exists_unit_map_first (T : Tensor K I J L) (A : Matrix I I K)
    (h : flatteningRank (map A (1 : Matrix J J K) (1 : Matrix L L K) T) 0 =
      flatteningRank T 0) :
    ∃ U : (Matrix I I K)ˣ,
      map (U : Matrix I I K) (1 : Matrix J J K) (1 : Matrix L L K) T = map A 1 1 T := by
  have hr : (A * (flatteningFirst T).transpose).rank = (flatteningFirst T).transpose.rank := by
    rw [← flatteningFirst_map_first, Matrix.rank_transpose, Matrix.rank_transpose]
    exact h
  obtain ⟨U, hU⟩ := matrix_exists_unit_mul_eq_of_rank_eq A (flatteningFirst T).transpose hr
  refine ⟨U, ?_⟩
  rw [← flatteningFirst_map_first, ← flatteningFirst_map_first] at hU
  funext i j k
  exact congrFun (congrFun hU i) (j, k)

private theorem exists_unit_map_second (T : Tensor K I J L) (B : Matrix J J K)
    (h : flatteningRank (map (1 : Matrix I I K) B (1 : Matrix L L K) T) 1 =
      flatteningRank T 1) :
    ∃ U : (Matrix J J K)ˣ,
      map (1 : Matrix I I K) (U : Matrix J J K) (1 : Matrix L L K) T = map 1 B 1 T := by
  have hr : (B * (flatteningSecond T).transpose).rank = (flatteningSecond T).transpose.rank := by
    rw [← flatteningSecond_map_second, Matrix.rank_transpose, Matrix.rank_transpose]
    exact h
  obtain ⟨U, hU⟩ := matrix_exists_unit_mul_eq_of_rank_eq B (flatteningSecond T).transpose hr
  refine ⟨U, ?_⟩
  rw [← flatteningSecond_map_second, ← flatteningSecond_map_second] at hU
  funext i j k
  exact congrFun (congrFun hU j) (i, k)

private theorem exists_unit_map_third (T : Tensor K I J L) (C : Matrix L L K)
    (h : flatteningRank (map (1 : Matrix I I K) (1 : Matrix J J K) C T) 2 =
      flatteningRank T 2) :
    ∃ U : (Matrix L L K)ˣ,
      map (1 : Matrix I I K) (1 : Matrix J J K) (U : Matrix L L K) T = map 1 1 C T := by
  have hr : (C * (flatteningThird T).transpose).rank = (flatteningThird T).transpose.rank := by
    rw [← flatteningThird_map_third, Matrix.rank_transpose, Matrix.rank_transpose]
    exact h
  obtain ⟨U, hU⟩ := matrix_exists_unit_mul_eq_of_rank_eq C (flatteningThird T).transpose hr
  refine ⟨U, ?_⟩
  rw [← flatteningThird_map_third, ← flatteningThird_map_third] at hU
  funext i j k
  exact congrFun (congrFun hU k) (i, j)

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] in
private theorem flatteningRank_eq_intermediate {T S U : Tensor K I J L}
    (hTS : Equivalent T S) (hTU : Restricts T U) (hUS : Restricts U S) (a : Fin 3) :
    flatteningRank U a = flatteningRank T a :=
  le_antisymm (flatteningRank_mono hTU a)
    ((flatteningRank_eq_of_equivalent hTS a).trans_le (flatteningRank_mono hUS a))

/-- An invertible change of each tensor factor gives mutual restriction. -/
theorem equivalent_of_unit_maps (T : Tensor K I J L)
    (A : (Matrix I I K)ˣ) (B : (Matrix J J K)ˣ) (C : (Matrix L L K)ˣ) :
    Equivalent T (map (A : Matrix I I K) (B : Matrix J J K) (C : Matrix L L K) T) := by
  refine ⟨⟨A, B, C, rfl⟩, ⟨↑A⁻¹, ↑B⁻¹, ↑C⁻¹, ?_⟩⟩
  rw [map_map]
  simp

/-- For tensors in the same ambient dimensions, mutual restriction is
equivalent to a change of basis in each of the three factors. -/
theorem equivalent_iff_invertible_factor_maps (T S : Tensor K I J L) :
    Equivalent T S ↔
      ∃ (A : (Matrix I I K)ˣ) (B : (Matrix J J K)ˣ) (C : (Matrix L L K)ˣ),
        map (A : Matrix I I K) (B : Matrix J J K) (C : Matrix L L K) T = S := by
  constructor
  · intro hTS
    obtain ⟨A, B, C, hmap⟩ := hTS.1
    have hA : Restricts (map A (1 : Matrix J J K) (1 : Matrix L L K) T) S := by
      refine ⟨1, B, C, ?_⟩
      simpa only [map_map, one_mul, mul_one] using hmap
    have hB : Restricts (map (1 : Matrix I I K) B (1 : Matrix L L K) T) S := by
      refine ⟨A, 1, C, ?_⟩
      simpa only [map_map, one_mul, mul_one] using hmap
    have hC : Restricts (map (1 : Matrix I I K) (1 : Matrix J J K) C T) S := by
      refine ⟨A, B, 1, ?_⟩
      simpa only [map_map, one_mul, mul_one] using hmap
    obtain ⟨U, hU⟩ := exists_unit_map_first T A
      (flatteningRank_eq_intermediate hTS ⟨A, 1, 1, rfl⟩ hA 0)
    obtain ⟨V, hV⟩ := exists_unit_map_second T B
      (flatteningRank_eq_intermediate hTS ⟨1, B, 1, rfl⟩ hB 1)
    obtain ⟨W, hW⟩ := exists_unit_map_third T C
      (flatteningRank_eq_intermediate hTS ⟨1, 1, C, rfl⟩ hC 2)
    have hfirst : map (U : Matrix I I K) B C T = map A B C T := by
      have h := congrArg (map (1 : Matrix I I K) B C) hU
      simpa only [map_map, one_mul, mul_one] using h
    have hsecond : map (U : Matrix I I K) (V : Matrix J J K) C T =
        map (U : Matrix I I K) B C T := by
      have h := congrArg (map (U : Matrix I I K) (1 : Matrix J J K) C) hV
      simpa only [map_map, one_mul, mul_one] using h
    have hthird : map (U : Matrix I I K) (V : Matrix J J K) (W : Matrix L L K) T =
        map (U : Matrix I I K) (V : Matrix J J K) C T := by
      have h := congrArg (map (U : Matrix I I K) (V : Matrix J J K) (1 : Matrix L L K)) hW
      simpa only [map_map, one_mul, mul_one] using h
    exact ⟨U, V, W, hthird.trans (hsecond.trans (hfirst.trans hmap))⟩
  · rintro ⟨A, B, C, rfl⟩
    exact equivalent_of_unit_maps T A B C

end MatrixMultiplication.Tensor
