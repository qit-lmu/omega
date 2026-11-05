module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Coordinate maps on a rectangular monomial grid

An edge is the difference of the two monomials obtained by multiplying by
`x` and by `y`. Diagonal summation specializes `y` to `x`, and a tail along
each diagonal recovers the edge coefficients.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} {b p : ℕ}

/-- The endpoint obtained by multiplying an edge monomial by `x`. -/
def gridEdgeHigh (j : Fin (b - 1) × Fin p) : Fin b × Fin (p + 1) :=
  (⟨j.1.val + 1, by have := j.1.isLt; omega⟩, j.2.castSucc)

/-- The endpoint obtained by multiplying an edge monomial by `y`. -/
def gridEdgeLow (j : Fin (b - 1) × Fin p) : Fin b × Fin (p + 1) :=
  (⟨j.1.val, by have := j.1.isLt; omega⟩, j.2.succ)

/-- Coefficient matrix of multiplication by `x-y` on the smaller rectangle. -/
def gridEdgeMap [Ring R] (b p : ℕ) :
    Matrix (Fin (b - 1) × Fin p) (Fin b × Fin (p + 1)) R :=
  fun j v => (if v = gridEdgeHigh j then 1 else 0) -
    (if v = gridEdgeLow j then 1 else 0)

theorem sum_gridEdgeMap_mul [Ring R] (j : Fin (b - 1) × Fin p)
    (f : Fin b × Fin (p + 1) → R) :
    (∑ v, gridEdgeMap b p j v * f v) = f (gridEdgeHigh j) - f (gridEdgeLow j) := by
  classical
  simp [gridEdgeMap, sub_mul, Finset.sum_sub_distrib]

/-- A boundary monomial representing the specified total degree. -/
def gridSection (b p : ℕ) (hb : 1 ≤ b) (s : Fin (b + p)) :
    Fin b × Fin (p + 1) :=
  (⟨min s.val (b - 1), by omega⟩,
    ⟨s.val - min s.val (b - 1), by have := s.isLt; omega⟩)

@[simp]
theorem gridSection_degree (hb : 1 ≤ b) (s : Fin (b + p)) :
    (gridSection b p hb s).1.val + (gridSection b p hb s).2.val = s.val := by
  simp only [gridSection]
  omega

/-- The boundary section, as a matrix on coefficient vectors. -/
def gridSectionMap [Zero R] [One R] (b p : ℕ) (hb : 1 ≤ b) :
    Matrix (Fin (b + p)) (Fin b × Fin (p + 1)) R :=
  fun s v => if v = gridSection b p hb s then 1 else 0

theorem sum_gridSectionMap_mul [Semiring R] (hb : 1 ≤ b) (s : Fin (b + p))
    (f : Fin b × Fin (p + 1) → R) :
    (∑ v, gridSectionMap b p hb s v * f v) = f (gridSection b p hb s) := by
  classical
  simp [gridSectionMap]

/-- The coefficient of diagonal summation, or specialization `y=x`. -/
def gridDiagonalCoefficient [Zero R] [One R] (s x y : ℕ) : R :=
  if x + y = s then 1 else 0

/-- A tail of one diagonal recovers the corresponding edge coefficient. -/
def gridTailCoefficient [Zero R] [One R] (k t x y : ℕ) : R :=
  if k < x ∧ x + y = k + t + 1 then 1 else 0

/-- Diagonal summation kills multiplication by `x-y`. -/
theorem gridDiagonalCoefficient_edge [Ring R] (s x t : ℕ) :
    (gridDiagonalCoefficient s (x + 1) t : R) -
      gridDiagonalCoefficient s x (t + 1) = 0 := by
  have h : x + 1 + t = x + (t + 1) := by omega
  simp [gridDiagonalCoefficient, h]

/-- The difference of adjacent tails is the coefficient of the edge between them. -/
theorem gridTailCoefficient_edge [Ring R] (k u x t : ℕ) :
    (gridTailCoefficient k u (x + 1) t : R) -
      gridTailCoefficient k u x (t + 1) =
      if t = u then (if x = k then 1 else 0) else 0 := by
  unfold gridTailCoefficient
  split_ifs <;> simp_all <;> omega

end MatrixMultiplication.Tensor
