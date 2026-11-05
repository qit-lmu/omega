module

public import Omega.Tensor.RankOperations
public import Omega.LinearAlgebra.MatrixRank
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases

/-!
# Flattenings of finite coefficient tensors

Each of the three flattenings regards one tensor index as a column and the
other two as a row. Their matrix ranks give lower bounds for tensor rank.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {K : Type*} {I J L I' J' L' : Type*}

/-- The first flattening, with rows indexed by the second and third factors. -/
def flatteningFirst (T : Tensor K I J L) : Matrix (J × L) I K :=
  fun jk i => T i jk.1 jk.2

/-- The second flattening, with rows indexed by the first and third factors. -/
def flatteningSecond (T : Tensor K I J L) : Matrix (I × L) J K :=
  fun ik j => T ik.1 j ik.2

/-- The third flattening, with rows indexed by the first and second factors. -/
def flatteningThird (T : Tensor K I J L) : Matrix (I × J) L K :=
  fun ij k => T ij.1 ij.2 k

/-- The three flattening ranks, indexed by `0`, `1`, and `2`. -/
def flatteningRank [CommSemiring K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (a : Fin 3) : ℕ :=
  ![(flatteningFirst T).rank, (flatteningSecond T).rank, (flatteningThird T).rank] a

@[simp]
theorem flatteningRank_zero [CommSemiring K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : flatteningRank T 0 = (flatteningFirst T).rank := rfl

@[simp]
theorem flatteningRank_one [CommSemiring K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : flatteningRank T 1 = (flatteningSecond T).rank := rfl

@[simp]
theorem flatteningRank_two [CommSemiring K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : flatteningRank T 2 = (flatteningThird T).rank := rfl

private theorem matrix_rank_sum_factors_le [Field K]
    {A B C : Type*} [Fintype A] [Fintype C]
    (x : C → A → K) (y : C → B → K) :
    Matrix.rank (fun j i => ∑ c, x c i * y c j) ≤ Fintype.card C := by
  let M : Matrix B C K := fun j c => y c j
  let N : Matrix C A K := fun c i => x c i
  have h : (fun j i => ∑ c, x c i * y c j) = (M * N : Matrix B A K) := by
    funext j i
    change (∑ c, x c i * y c j) = ∑ c, y c j * x c i
    simp only [mul_comm]
  rw [h]
  exact (Matrix.rank_mul_le_left M N).trans M.rank_le_card_width

/-- The first flattening rank is bounded by tensor rank. -/
theorem flatteningFirst_rank_le [Field K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : (flatteningFirst T).rank ≤ rank T := by
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  have h := matrix_rank_sum_factors_le x (fun a (jk : J × L) => y a jk.1 * z a jk.2)
  have he : flatteningFirst T =
      fun jk i => ∑ a, x a i * (y a jk.1 * z a jk.2) := by
    funext jk i
    simp [flatteningFirst, hT, pure, mul_assoc]
  simpa only [← he, Fintype.card_fin] using h

/-- The second flattening rank is bounded by tensor rank. -/
theorem flatteningSecond_rank_le [Field K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : (flatteningSecond T).rank ≤ rank T := by
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  have h := matrix_rank_sum_factors_le y (fun a (ik : I × L) => x a ik.1 * z a ik.2)
  have he : flatteningSecond T =
      fun ik j => ∑ a, y a j * (x a ik.1 * z a ik.2) := by
    funext ik j
    simp [flatteningSecond, hT, pure, mul_assoc, mul_left_comm]
  simpa only [← he, Fintype.card_fin] using h

/-- The third flattening rank is bounded by tensor rank. -/
theorem flatteningThird_rank_le [Field K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) : (flatteningThird T).rank ≤ rank T := by
  obtain ⟨x, y, z, hT⟩ := exists_rank_decomposition T
  have h := matrix_rank_sum_factors_le z (fun a (ij : I × J) => x a ij.1 * y a ij.2)
  have he : flatteningThird T =
      fun ij k => ∑ a, z a k * (x a ij.1 * y a ij.2) := by
    funext ij k
    simp [flatteningThird, hT, pure, mul_comm]
  simpa only [← he, Fintype.card_fin] using h

/-- Every flattening rank is a lower bound for tensor rank. -/
theorem flatteningRank_le_rank [Field K] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (a : Fin 3) : flatteningRank T a ≤ rank T := by
  fin_cases a
  · exact flatteningFirst_rank_le T
  · exact flatteningSecond_rank_le T
  · exact flatteningThird_rank_le T

@[simp]
theorem flatteningFirst_reindex
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor K I J L) :
    flatteningFirst (reindex eI eJ eL T) =
      (flatteningFirst T).reindex (eJ.prodCongr eL) eI := rfl

@[simp]
theorem flatteningSecond_reindex
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor K I J L) :
    flatteningSecond (reindex eI eJ eL T) =
      (flatteningSecond T).reindex (eI.prodCongr eL) eJ := rfl

@[simp]
theorem flatteningThird_reindex
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L') (T : Tensor K I J L) :
    flatteningThird (reindex eI eJ eL T) =
      (flatteningThird T).reindex (eI.prodCongr eJ) eL := rfl

/-- Relabelling the three factors does not change any flattening rank. -/
theorem flatteningRank_reindex [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    (T : Tensor K I J L) (a : Fin 3) :
    flatteningRank (reindex eI eJ eL T) a = flatteningRank T a := by
  fin_cases a
  · change (flatteningFirst (reindex eI eJ eL T)).rank = (flatteningFirst T).rank
    rw [flatteningFirst_reindex]
    exact Matrix.rank_reindex (eJ.prodCongr eL) eI (flatteningFirst T)
  · change (flatteningSecond (reindex eI eJ eL T)).rank = (flatteningSecond T).rank
    rw [flatteningSecond_reindex]
    exact Matrix.rank_reindex (eI.prodCongr eL) eJ (flatteningSecond T)
  · change (flatteningThird (reindex eI eJ eL T)).rank = (flatteningThird T).rank
    rw [flatteningThird_reindex]
    exact Matrix.rank_reindex (eI.prodCongr eJ) eL (flatteningThird T)

/-- The first flattening of a tensor product is a reindexed matrix Kronecker product. -/
theorem flatteningFirst_kronecker [Mul K]
    (T : Tensor K I J L) (S : Tensor K I' J' L') :
    flatteningFirst (kronecker T S) =
      (Matrix.kronecker (flatteningFirst T) (flatteningFirst S)).reindex
        (Equiv.prodProdProdComm J L J' L') (Equiv.refl (I × I')) := rfl

/-- The second flattening of a tensor product is a reindexed matrix Kronecker product. -/
theorem flatteningSecond_kronecker [Mul K]
    (T : Tensor K I J L) (S : Tensor K I' J' L') :
    flatteningSecond (kronecker T S) =
      (Matrix.kronecker (flatteningSecond T) (flatteningSecond S)).reindex
        (Equiv.prodProdProdComm I L I' L') (Equiv.refl (J × J')) := rfl

/-- The third flattening of a tensor product is a reindexed matrix Kronecker product. -/
theorem flatteningThird_kronecker [Mul K]
    (T : Tensor K I J L) (S : Tensor K I' J' L') :
    flatteningThird (kronecker T S) =
      (Matrix.kronecker (flatteningThird T) (flatteningThird S)).reindex
        (Equiv.prodProdProdComm I J I' J') (Equiv.refl (L × L')) := rfl

/-- Each flattening rank is multiplicative under tensor products. -/
theorem flatteningRank_kronecker [Field K]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor K I J L) (S : Tensor K I' J' L') (a : Fin 3) :
    flatteningRank (kronecker T S) a = flatteningRank T a * flatteningRank S a := by
  fin_cases a
  · change (flatteningFirst (kronecker T S)).rank = _
    rw [flatteningFirst_kronecker, Matrix.rank_reindex]
    exact matrix_rank_kronecker (flatteningFirst T) (flatteningFirst S)
  · change (flatteningSecond (kronecker T S)).rank = _
    rw [flatteningSecond_kronecker, Matrix.rank_reindex]
    exact matrix_rank_kronecker (flatteningSecond T) (flatteningSecond S)
  · change (flatteningThird (kronecker T S)).rank = _
    rw [flatteningThird_kronecker, Matrix.rank_reindex]
    exact matrix_rank_kronecker (flatteningThird T) (flatteningThird S)

end MatrixMultiplication.Tensor
