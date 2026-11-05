module

public import Omega.ValueScaling
public import Omega.ValueWitnessBounds

/-!
# Diagonal and matrix-multiplication normalization

The scaling laws applied to the unit diagonal give the normalization formulas
in manuscript Corollary `value-diag-matrix`. Diagonal size zero is included.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

/-- A unit diagonal factor can be removed from the right of a Kronecker product. -/
theorem kronecker_diagonal_one_equivalent {R I J L : Type*} [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L] (T : Tensor R I J L) :
    Equivalent (kronecker T (diagonal R 1)) T := by
  apply equivalent_of_reindex (Equiv.prodUnique I (Fin 1))
    (Equiv.prodUnique J (Fin 1)) (Equiv.prodUnique L (Fin 1))
  funext i j k
  simp [reindex, kronecker, diagonal, Equiv.prodUnique_symm_apply]

variable {K : Type*} [Field K]

/-- The fractional value of a diagonal tensor is its size throughout the
admissible interval, including size zero. -/
theorem fractionalValue_diagonal (r : ℕ) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (diagonal K r) τ = (r : ℝ≥0∞) := by
  have h := fractionalValue_diagonal_kronecker (diagonal K 1) r τ
  rw [fractionalValue_eq_of_equivalent (kronecker_diagonal_one_equivalent _) τ,
    fractionalValue_unit hτ hτω, mul_one] at h
  exact h

/-- The fractional value of positive rectangular matrix multiplication is
the product of its three dimensions raised to the value parameter. -/
theorem fractionalValue_matrixMul (l m n : ℕ)
    (hl : 1 ≤ l) (hm : 1 ≤ m) (hn : 1 ≤ n) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (matrixMul K l m n) τ = ((l * m * n : ℕ) : ℝ≥0∞) ^ τ := by
  have h := fractionalValue_matrixMul_kronecker (diagonal K 1) l m n hl hm hn τ
  rw [fractionalValue_eq_of_equivalent (kronecker_diagonal_one_equivalent _) τ,
    fractionalValue_unit hτ hτω, mul_one, ENNReal.ofReal_natCast] at h
  exact h

end MatrixMultiplication.Tensor
