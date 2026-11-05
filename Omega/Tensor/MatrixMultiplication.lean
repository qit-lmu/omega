module

public import Omega.Tensor.FlatteningExamples
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Coordinate calculus for matrix multiplication tensors

Dimension inclusions give restrictions. Regrouping the three matrix indices
identifies Kronecker products and powers with multiplied dimensions.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {R : Type*}

private theorem restricts_precomp [CommSemiring R]
    {I J L I' J' L' : Type*} [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor R I J L) (f : I' → I) (g : J' → J) (h : L' → L) :
    Restricts T (fun i j k => T (f i) (g j) (h k)) := by
  classical
  refine ⟨Matrix.of (fun i a => if a = f i then 1 else 0),
    Matrix.of (fun j b => if b = g j then 1 else 0),
    Matrix.of (fun k c => if c = h k then 1 else 0), ?_⟩
  funext i j k
  simp [map]

/-- Decreasing any of the three matrix dimensions is a tensor restriction. -/
theorem matrixMul_restricts_of_le (R : Type*) [CommSemiring R]
    {l m n l' m' n' : ℕ} (hl : l ≤ l') (hm : m ≤ m') (hn : n ≤ n') :
    Restricts (matrixMul R l' m' n') (matrixMul R l m n) := by
  have h := restricts_precomp (matrixMul R l' m' n')
    (Prod.map (Fin.castLE hl) (Fin.castLE hm))
    (Prod.map (Fin.castLE hm) (Fin.castLE hn))
    (Prod.map (Fin.castLE hl) (Fin.castLE hn))
  have he : (fun i j k => matrixMul R l' m' n'
      (Prod.map (Fin.castLE hl) (Fin.castLE hm) i)
      (Prod.map (Fin.castLE hm) (Fin.castLE hn) j)
      (Prod.map (Fin.castLE hl) (Fin.castLE hn) k)) = matrixMul R l m n := by
    funext i j k
    simp [matrixMul]
  rw [he] at h
  exact h

/-- Asymptotic rank is monotone in the three matrix dimensions. -/
theorem asymptoticRank_matrixMul_mono (R : Type*) [CommSemiring R]
    {l m n l' m' n' : ℕ} (hl : l ≤ l') (hm : m ≤ m') (hn : n ≤ n') :
    asymptoticRank (matrixMul R l m n) ≤ asymptoticRank (matrixMul R l' m' n') :=
  asymptoticRank_mono (matrixMul_restricts_of_le R hl hm hn)

/-- Regroup the two row indices and the two column indices, then encode each pair. -/
def matrixMulProductEquiv (l m l' m' : ℕ) :
    (Fin l × Fin m) × (Fin l' × Fin m') ≃ Fin (l * l') × Fin (m * m') :=
  (Equiv.prodProdProdComm (Fin l) (Fin m) (Fin l') (Fin m')).trans
    (finProdFinEquiv.prodCongr finProdFinEquiv)

@[simp]
theorem matrixMulProductEquiv_apply (l m l' m' : ℕ)
    (i : (Fin l × Fin m) × (Fin l' × Fin m')) :
    matrixMulProductEquiv l m l' m' i =
      (finProdFinEquiv (i.1.1, i.2.1), finProdFinEquiv (i.1.2, i.2.2)) := rfl

/-- Coordinate reindexing identifies the product with multiplied matrix dimensions. -/
theorem matrixMul_kronecker_reindex (R : Type*) [CommSemiring R]
    (l m n l' m' n' : ℕ) :
    reindex (matrixMulProductEquiv l m l' m') (matrixMulProductEquiv m n m' n')
      (matrixMulProductEquiv l n l' n')
      (kronecker (matrixMul R l m n) (matrixMul R l' m' n')) =
        matrixMul R (l * l') (m * m') (n * n') := by
  funext i j k
  obtain ⟨i, rfl⟩ := (matrixMulProductEquiv l m l' m').surjective i
  obtain ⟨j, rfl⟩ := (matrixMulProductEquiv m n m' n').surjective j
  obtain ⟨k, rfl⟩ := (matrixMulProductEquiv l n l' n').surjective k
  simp only [reindex, Equiv.symm_apply_apply]
  simp only [kronecker, matrixMul,
    matrixMulProductEquiv_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem equivalent_of_reindex [CommSemiring R]
    {I J L I' J' L' : Type*}
    [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']
    (eI : I ≃ I') (eJ : J ≃ J') (eL : L ≃ L')
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : reindex eI eJ eL T = S) :
    Equivalent T S := by
  subst S
  refine ⟨restricts_reindex eI eJ eL T, ?_⟩
  simpa only [reindex_symm] using
    restricts_reindex eI.symm eJ.symm eL.symm (reindex eI eJ eL T)

/-- Kronecker products multiply all three matrix dimensions. -/
theorem matrixMul_kronecker_equivalent (R : Type*) [CommSemiring R]
    (l m n l' m' n' : ℕ) :
    Equivalent (kronecker (matrixMul R l m n) (matrixMul R l' m' n'))
      (matrixMul R (l * l') (m * m') (n * n')) :=
  equivalent_of_reindex _ _ _ (matrixMul_kronecker_reindex R l m n l' m' n')

/-- Encode a tuple of finite indices as one index of the corresponding power size. -/
def matrixMulTupleEquiv (n k : ℕ) : (Fin k → Fin n) ≃ Fin (n ^ k) :=
  (Fintype.equivFin (Fin k → Fin n)).trans (finCongr (by simp))

/-- Split a tuple of matrix coordinates into its two tuples of indices. -/
def matrixMulPowerEquiv (l m k : ℕ) :
    (Fin k → Fin l × Fin m) ≃ Fin (l ^ k) × Fin (m ^ k) :=
  (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin l) (fun _ => Fin m)).trans
    ((matrixMulTupleEquiv l k).prodCongr (matrixMulTupleEquiv m k))

@[simp]
theorem matrixMulPowerEquiv_apply (l m k : ℕ) (i : Fin k → Fin l × Fin m) :
    matrixMulPowerEquiv l m k i =
      (matrixMulTupleEquiv l k (fun t => (i t).1),
        matrixMulTupleEquiv m k (fun t => (i t).2)) := rfl

/-- Tensor powers raise each matrix dimension to the same power, including power zero. -/
theorem matrixMul_kroneckerPower_reindex (R : Type*) [CommSemiring R]
    (l m n k : ℕ) :
    reindex (matrixMulPowerEquiv l m k) (matrixMulPowerEquiv m n k)
      (matrixMulPowerEquiv l n k) (kroneckerPower (matrixMul R l m n) k) =
        matrixMul R (l ^ k) (m ^ k) (n ^ k) := by
  funext i j p
  obtain ⟨i, rfl⟩ := (matrixMulPowerEquiv l m k).surjective i
  obtain ⟨j, rfl⟩ := (matrixMulPowerEquiv m n k).surjective j
  obtain ⟨p, rfl⟩ := (matrixMulPowerEquiv l n k).surjective p
  simp only [reindex, Equiv.symm_apply_apply]
  simp only [kroneckerPower, matrixMul]
  rw [Fintype.prod_boole]
  simp only [matrixMulPowerEquiv_apply, Equiv.apply_eq_iff_eq, funext_iff, forall_and]

/-- Matrix-multiplication tensor powers are equivalent to powered dimensions. -/
theorem matrixMul_kroneckerPower_equivalent (R : Type*) [CommSemiring R]
    (l m n k : ℕ) :
    Equivalent (kroneckerPower (matrixMul R l m n) k)
      (matrixMul R (l ^ k) (m ^ k) (n ^ k)) :=
  equivalent_of_reindex _ _ _ (matrixMul_kroneckerPower_reindex R l m n k)

/-- Ordinary rank is unchanged when tensor powers are replaced by powered dimensions. -/
theorem rank_matrixMul_pow (R : Type*) [CommSemiring R] (l m n k : ℕ) :
    rank (matrixMul R (l ^ k) (m ^ k) (n ^ k)) =
      rank (kroneckerPower (matrixMul R l m n) k) :=
  (rank_eq_of_equivalent (matrixMul_kroneckerPower_equivalent R l m n k)).symm

/-- Asymptotic rank is unchanged when tensor powers are replaced by powered dimensions. -/
theorem asymptoticRank_matrixMul_pow (R : Type*) [CommSemiring R] (l m n k : ℕ) :
    asymptoticRank (matrixMul R (l ^ k) (m ^ k) (n ^ k)) =
      asymptoticRank (kroneckerPower (matrixMul R l m n) k) :=
  (asymptoticRank_eq_of_equivalent
    (matrixMul_kroneckerPower_equivalent R l m n k)).symm

/-- The elementary decomposition uses one pure tensor for each multiplication term. -/
theorem rank_matrixMul_le (R : Type*) [CommSemiring R] (l m n : ℕ) :
    rank (matrixMul R l m n) ≤ l * m * n := by
  classical
  let x : Fin l × Fin m × Fin n → Fin l × Fin m → R :=
    fun a ij => if ij = (a.1, a.2.1) then 1 else 0
  let y : Fin l × Fin m × Fin n → Fin m × Fin n → R :=
    fun a jk => if jk = (a.2.1, a.2.2) then 1 else 0
  let z : Fin l × Fin m × Fin n → Fin l × Fin n → R :=
    fun a ik => if ik = (a.1, a.2.2) then 1 else 0
  have he : matrixMul R l m n = ∑ a, pure (x a) (y a) (z a) := by
    funext ij jk ik
    simp [x, y, z, pure, matrixMul, Fintype.sum_prod_type, Prod.ext_iff,
      ite_and, mul_ite]
    split_ifs <;> simp_all
  have h := rank_le_of_sum_pure x y z
  simpa only [← he, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using h

/-- Multiplication of one-by-one matrices is the unit diagonal tensor. -/
theorem matrixMul_one_equivalent_diagonal (R : Type*) [CommSemiring R] :
    Equivalent (matrixMul R 1 1 1) (diagonal R 1) := by
  apply equivalent_of_reindex (finProdFinEquiv : Fin 1 × Fin 1 ≃ Fin 1)
    (finProdFinEquiv : Fin 1 × Fin 1 ≃ Fin 1)
    (finProdFinEquiv : Fin 1 × Fin 1 ≃ Fin 1)
  funext i j k
  have hi : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance i 0
  have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance j 0
  have hk : k = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance k 0
  subst i
  subst j
  subst k
  rfl

/-- The asymptotic rank of scalar multiplication is one over every field. -/
@[simp]
theorem asymptoticRank_matrixMul_one (K : Type*) [Field K] :
    asymptoticRank (matrixMul K 1 1 1) = 1 := by
  rw [asymptoticRank_eq_of_equivalent (matrixMul_one_equivalent_diagonal K)]
  simpa only [Nat.cast_one] using asymptoticRank_diagonal (K := K) 1

end MatrixMultiplication.Tensor
