module

public import Omega.Tensor.Basic

/-!
# The diagonal, matrix-multiplication, and polynomial-multiplication tensors

All bases are indexed from zero.  Thus polynomial multiplication has coefficient
one exactly when the output index equals the sum of the two input indices.
The definitions are valid over any semiring and impose no cardinality or
characteristic assumptions on a field.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

/-- The diagonal tensor denoted by `⟨r⟩` in the manuscript. -/
def diagonal (R : Type*) [Zero R] [One R] (r : ℕ) :
    Tensor R (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ j = k then 1 else 0

/-- The matrix-multiplication tensor denoted by `⟨l,m,n⟩`. -/
def matrixMul (R : Type*) [Zero R] [One R] (l m n : ℕ) :
    Tensor R (Fin l × Fin m) (Fin m × Fin n) (Fin l × Fin n) :=
  fun ij jk ik => if ij.1 = ik.1 ∧ ij.2 = jk.1 ∧ jk.2 = ik.2 then 1 else 0

/-- Polynomial multiplication `PM_{a,b}` on coefficient vectors.  The paper
uses positive `a,b`; the formula also defines the degenerate zero-size cases. -/
def polynomialMul (R : Type*) [Zero R] [One R] (a b : ℕ) :
    Tensor R (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp]
theorem diagonal_self (R : Type*) [Zero R] [One R] {r : ℕ} (i : Fin r) :
    diagonal R r i i i = 1 := by simp [diagonal]

@[simp]
theorem matrixMul_matching (R : Type*) [Zero R] [One R]
    {l m n : ℕ} (i : Fin l) (j : Fin m) (k : Fin n) :
    matrixMul R l m n (i, j) (j, k) (i, k) = 1 := by simp [matrixMul]

/-- A valid input pair contributes precisely to its coefficient-sum position. -/
theorem polynomialMul_matching (R : Type*) [Zero R] [One R]
    {a b : ℕ} (i : Fin a) (j : Fin b) (h : i.val + j.val < a + b - 1) :
    polynomialMul R a b i j ⟨i.val + j.val, h⟩ = 1 := by simp [polynomialMul]

end MatrixMultiplication.Tensor
