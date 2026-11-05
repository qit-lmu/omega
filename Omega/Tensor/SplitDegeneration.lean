module

public import Omega.Tensor.MonomialDegeneration
public import Omega.Tensor.DegenerationOperations

/-!
# Degeneration from compatible split coefficient maps

Three block identities suffice: the two diagonal blocks are prescribed and
one off-diagonal block vanishes. No ambient exact-sequence or invertibility
assumption is needed once these identities are available.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R I J L J₀ J₁ L₀ L₁ : Type*} [CommSemiring R]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype J₀] [Fintype J₁] [Fintype L₀] [Fintype L₁]

/-- Compatible input and output maps split a tensor into a partially direct sum. -/
theorem degenerates_partialSum_of_split_maps [DecidableEq I]
    (T : Tensor R I J L) (T₀ : Tensor R I J₀ L₀) (T₁ : Tensor R I J₁ L₁)
    (B₀ : Matrix J₀ J R) (B₁ : Matrix J₁ J R)
    (C₀ : Matrix L₀ L R) (C₁ : Matrix L₁ L R)
    (h₀₀ : map (1 : Matrix I I R) B₀ C₀ T = T₀) (h₀₁ : map (1 : Matrix I I R) B₀ C₁ T = 0)
    (h₁₁ : map (1 : Matrix I I R) B₁ C₁ T = T₁) : Degenerates T (partialSum T₀ T₁) := by
  let B : Matrix (J₀ ⊕ J₁) J R := Sum.elim B₀ B₁
  let C : Matrix (L₀ ⊕ L₁) L R := Sum.elim C₀ C₁
  let S := map (1 : Matrix I I R) B C T
  have hTS : Restricts T S := ⟨1, B, C, rfl⟩
  apply hTS.degenerates.trans
  apply degenerates_of_monomial_pullback S (partialSum T₀ T₁) id id id
    (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))
    (Sum.elim (fun _ => 1) (fun _ => 0)) 1
  · intro i j k hlt
    rcases j with j | j <;> rcases k with k | k <;> norm_num at hlt
    change map (1 : Matrix I I R) B₀ C₁ T i j k = 0
    rw [h₀₁]
    rfl
  · intro i j k
    rcases j with j | j <;> rcases k with k | k
    · change T₀ i j k = if 0 + 0 + 1 = 1 then map (1 : Matrix I I R) B₀ C₀ T i j k else 0
      simp [h₀₀]
    · simp [partialSum]
    · simp [partialSum]
    · change T₁ i j k = if 0 + 1 + 0 = 1 then map (1 : Matrix I I R) B₁ C₁ T i j k else 0
      simp [h₁₁]

end MatrixMultiplication.Tensor
