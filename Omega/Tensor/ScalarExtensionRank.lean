module

public import Omega.Tensor.RankOperations
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Tensor rank under scalar extension

A finite extension of degree `k` can decrease tensor rank by at most a factor
`k²`. Expand the first two coordinates of each pure summand in an arbitrary
basis of the extension, and retract the third coordinate to the base field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]
variable {I J L : Type*}

/-- Extend tensor coefficients along the algebra map. -/
def scalarExtension (E : Type*) [Field E] [Algebra K E]
    (T : Tensor K I J L) : Tensor E I J L :=
  fun i j l => algebraMap K E (T i j l)

@[simp]
theorem scalarExtension_polynomialMul (E : Type*) [Field E] [Algebra K E]
    (a b : ℕ) : scalarExtension E (polynomialMul K a b) = polynomialMul E a b := by
  classical
  funext i j l
  simp [scalarExtension, polynomialMul]

private theorem retract_mul_mul {E : Type*} [Field E] [Algebra K E]
    {A : Type*} [Fintype A] (b : Module.Basis A K E) (r : E →ₗ[K] K) (x y z : E) :
    r (x * y * z) =
      ∑ u, ∑ v, b.repr x u * b.repr y v * r (b u * b v * z) := by
  calc
    r (x * y * z) =
        r (((∑ u, b.repr x u • b u) * ∑ v, b.repr y v • b v) * z) := by
          rw [b.sum_repr, b.sum_repr]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, _root_.map_sum,
        smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Rank descent through an extension of finite degree, as in
`eq:extensionscalars` of the manuscript. -/
theorem rank_le_extension_degree_sq_mul (E : Type*) [Field E] [Algebra K E]
    [FiniteDimensional K E] [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) :
    rank T ≤ (Module.finrank K E) ^ 2 * rank (scalarExtension E T) := by
  classical
  let b := Module.finBasis K E
  obtain ⟨r, hr⟩ := (Algebra.linearMap K E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K E).injective)
  have hr' (x : K) : r (algebraMap K E x) = x := LinearMap.congr_fun hr x
  obtain ⟨x, y, z, h⟩ := exists_rank_decomposition (scalarExtension E T)
  let x' (p : Fin (rank (scalarExtension E T)) ×
      Fin (Module.finrank K E) × Fin (Module.finrank K E)) (i : I) := b.repr (x p.1 i) p.2.1
  let y' (p : Fin (rank (scalarExtension E T)) ×
      Fin (Module.finrank K E) × Fin (Module.finrank K E)) (j : J) := b.repr (y p.1 j) p.2.2
  let z' (p : Fin (rank (scalarExtension E T)) ×
      Fin (Module.finrank K E) × Fin (Module.finrank K E)) (l : L) :=
    r (b p.2.1 * b p.2.2 * z p.1 l)
  have hT : T = ∑ p, pure (x' p) (y' p) (z' p) := by
    funext i j l
    calc
      T i j l = r (scalarExtension E T i j l) := (hr' _).symm
      _ = ∑ a, r (x a i * y a j * z a l) := by
        have hc := congrArg (fun S : Tensor E I J L => r (S i j l)) h
        simpa only [Finset.sum_apply, pure, _root_.map_sum] using hc
      _ = _ := by
        simp only [Finset.sum_apply, Fintype.sum_prod_type, pure, x', y', z']
        apply Finset.sum_congr rfl
        intro a _
        exact retract_mul_mul b r _ _ _
  have hb := rank_le_of_sum_pure x' y' z'
  rw [← hT] at hb
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hb

end MatrixMultiplication.Tensor
