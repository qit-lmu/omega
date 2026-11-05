module

public import Omega.External.Prove2MeDefinitions
public import Omega.Tensor.Rank
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases

/-!
# Comparing Prove2Me tensors with the manuscript's coefficient tensors

The product of standard coordinate bases identifies the imported three-factor
`PiTensorProduct` with coefficient arrays. Prove2Me orders the third basis by
`(k, i)`, whereas the manuscript uses `(i, k)`; `mmCoefficients` transposes that
factor. Pure-tensor decompositions correspond exactly to restrictions of
diagonal tensors, so the two ordinary ranks agree, including zero dimensions.
-/

@[expose] public section

open scoped BigOperators
open PiTensorProduct MatrixMultiplication

namespace MME

variable {K : Type*} [Field K]

/-- The three standard basis index types in the imported model. -/
abbrev MMIndex (n m p : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin n × Fin m
  | ⟨1, _⟩ => Fin m × Fin p
  | ⟨2, _⟩ => Fin p × Fin n

/-- Standard coordinate bases of the imported mode spaces. -/
noncomputable def mmBasis (n m p : ℕ) (s : Fin 3) :
    Module.Basis (MMIndex n m p s) K (MMSpace K n m p s) :=
  match s with
  | ⟨0, _⟩ => Pi.basisFun K _
  | ⟨1, _⟩ => Pi.basisFun K _
  | ⟨2, _⟩ => Pi.basisFun K _

/-- Convert our three coefficient indices to the imported dependent index family. -/
def mmIndices {n m p : ℕ}
    (ij : Fin n × Fin m) (jk : Fin m × Fin p) (ik : Fin n × Fin p) :
    ∀ s, MMIndex n m p s
  | ⟨0, _⟩ => ij
  | ⟨1, _⟩ => jk
  | ⟨2, _⟩ => ik.swap

/-- The external tensor's coordinates in our convention: transpose its third factor. -/
noncomputable def mmCoefficients (n m p : ℕ) :
    PiTensorProduct K (MMSpace K n m p) →ₗ[K]
      Tensor K (Fin n × Fin m) (Fin m × Fin p) (Fin n × Fin p) where
  toFun T ij jk ik := (Basis.piTensorProduct (mmBasis n m p)).repr T
    (mmIndices ij jk ik)
  map_add' T S := by ext ij jk ik; simp
  map_smul' c T := by ext ij jk ik; simp

@[simp]
theorem mmCoefficients_tprod (n m p : ℕ) (f : ∀ s, MMSpace K n m p s)
    (ij : Fin n × Fin m) (jk : Fin m × Fin p) (ik : Fin n × Fin p) :
    mmCoefficients n m p (tprod K f) ij jk ik =
      f 0 ij * f 1 jk * f 2 ik.swap := by
  simp [mmCoefficients, Basis.piTensorProduct_repr_tprod_apply,
    Fin.prod_univ_succ, mmBasis, mmIndices, mul_assoc]

/-- Passing to coordinates loses no information. -/
theorem mmCoefficients_injective (n m p : ℕ) :
    Function.Injective (mmCoefficients (K := K) n m p) := by
  intro T S h
  apply (Basis.piTensorProduct (mmBasis n m p)).repr.injective
  ext x
  have hx : mmIndices (x 0) (x 1) (x 2).swap = x := by
    funext s
    fin_cases s <;> rfl
  simpa only [mmCoefficients, LinearMap.coe_mk, AddHom.coe_mk, hx] using
    congrFun (congrFun (congrFun h (x 0)) (x 1)) (x 2).swap

@[simp]
theorem mmCoefficients_MMTensor (n m p : ℕ) :
    mmCoefficients (K := K) n m p (MMTensor K n m p) =
      Tensor.matrixMul K n m p := by
  classical
  ext ⟨i, j⟩ ⟨j', k⟩ ⟨i', k'⟩
  simp [MMTensor, map_sum, mmCoefficients_tprod, Pi.single_apply,
    Tensor.matrixMul, Prod.mk.injEq, mul_ite, ite_and, Prod.swap_prod_mk]
  split_ifs <;> rfl

/-- Pure-tensor decompositions and diagonal restrictions have the same lengths. -/
theorem mm_decomposition_iff (n m p r : ℕ)
    (T : PiTensorProduct K (MMSpace K n m p)) :
    (∃ f : Fin r → ∀ s, MMSpace K n m p s, T = ∑ j, tprod K (f j)) ↔
      Tensor.Restricts (Tensor.diagonal K r) (mmCoefficients n m p T) := by
  classical
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨Matrix.of (fun ij q => f q 0 ij), Matrix.of (fun jk q => f q 1 jk),
      Matrix.of (fun ik q => f q 2 ik.swap), ?_⟩
    rw [Tensor.map_diagonal]
    ext ij jk ik
    simp
  · rintro ⟨A, B, C, h⟩
    let f : Fin r → ∀ s, MMSpace K n m p s := fun q s =>
      match s with
      | ⟨0, _⟩ => fun ij => A ij q
      | ⟨1, _⟩ => fun jk => B jk q
      | ⟨2, _⟩ => fun ki => C ki.swap q
    refine ⟨f, mmCoefficients_injective n m p ?_⟩
    rw [Tensor.map_diagonal] at h
    ext ij jk ik
    simpa [f] using (congrFun (congrFun (congrFun h ij) jk) ik).symm

/-- The imported textbook rank equals our coordinate restriction rank. -/
theorem tensorRank_eq_rank_mmCoefficients (n m p : ℕ)
    (T : PiTensorProduct K (MMSpace K n m p)) :
    tensorRank T = Tensor.rank (mmCoefficients n m p T) := by
  classical
  unfold tensorRank
  apply le_antisymm
  · exact Nat.sInf_le ((mm_decomposition_iff n m p _ T).mpr
      (Tensor.diagonal_restricts_of_rank _))
  · apply le_csInf
    · exact ⟨_, (mm_decomposition_iff n m p _ T).mpr
        (Tensor.diagonal_restricts_of_rank _)⟩
    · intro r hr
      exact Tensor.rank_le_of_diagonal_restricts ((mm_decomposition_iff n m p r T).mp hr)

/-- The two formalizations assign the same ordinary rank to matrix multiplication. -/
theorem tensorRank_MMTensor_eq_rank (n m p : ℕ) :
    tensorRank (MMTensor K n m p) = Tensor.rank (Tensor.matrixMul K n m p) := by
  rw [tensorRank_eq_rank_mmCoefficients, mmCoefficients_MMTensor]

end MME
