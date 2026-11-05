module

public import Omega.Tensor.SymmetrizationDegeneration
public import Omega.Tensor.Nonzero
public import Omega.Tensor.DirectSumCopies
public import Mathlib.Basic.ENNReal.Real

/-!
# Fractional symmetrized value and its witnesses

Each witness stores positive integer sizes and a polynomial degeneration.
Its score is the positive real expression in Definition 4.3. The value is
an extended nonnegative real supremum, so unbounded values remain expressible.
The zero tensor has no witnesses, so its value is the empty supremum, zero.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]

/-- A positive integer witness in the definition of fractional symmetrized
value, using the project's polynomial degeneration relation. -/
structure ValueWitness (T : Tensor K I J L) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  N : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hc : 1 ≤ c
  hd : 1 ≤ d
  hN : 1 ≤ N
  degeneration : Degenerates
    (kronecker (directSumCopies (matrixMul K d d d) c)
      (kroneckerPower (symmetrize T) N))
    (directSumCopies (matrixMul K b b b) a)

/-- The real score of a fractional-value witness. -/
def ValueWitness.score {T : Tensor K I J L} (w : ValueWitness T) (τ : ℝ) : ℝ :=
  (((w.a : ℝ) * (w.b : ℝ) ^ (3 * τ)) /
    ((w.c : ℝ) * (w.d : ℝ) ^ (3 * τ))) ^ ((6 * w.N : ℕ) : ℝ)⁻¹

/-- Every witness score is strictly positive. -/
theorem ValueWitness.score_pos {T : Tensor K I J L} (w : ValueWitness T) (τ : ℝ) :
    0 < w.score τ := by
  apply Real.rpow_pos_of_pos
  apply div_pos
  · exact mul_pos (by exact_mod_cast Nat.succ_le_iff.mp w.ha)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_le_iff.mp w.hb) _)
  · exact mul_pos (by exact_mod_cast Nat.succ_le_iff.mp w.hc)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_le_iff.mp w.hd) _)

/-- A witness can exist only for a nonzero tensor: its source is zero when
the argument tensor is zero, whereas its target has a nonzero coefficient. -/
theorem ValueWitness.tensor_ne_zero {T : Tensor K I J L} (w : ValueWitness T) : T ≠ 0 := by
  intro hT
  subst T
  have h := w.degeneration
  rw [symmetrize_zero,
    kroneckerPower_zero_of_pos w.N (Nat.succ_le_iff.mp w.hN)] at h
  rw [kronecker_zero_right, zero_degenerates_iff] at h
  let ia : Fin w.a := ⟨0, Nat.succ_le_iff.mp w.ha⟩
  let ib : Fin w.b := ⟨0, Nat.succ_le_iff.mp w.hb⟩
  have hc := congrFun (congrFun (congrFun h (ia, (ib, ib))) (ia, (ib, ib))) (ia, (ib, ib))
  simp [directSumCopies, kronecker, diagonal, matrixMul] at hc

/-- The witness type for the zero tensor is empty. -/
instance valueWitness_zero_isEmpty : IsEmpty (ValueWitness (0 : Tensor K I J L)) :=
  ⟨fun w => w.tensor_ne_zero rfl⟩

/-- Fractional symmetrized value is the supremum of its witness scores in
the extended nonnegative reals, including the empty supremum. -/
def fractionalValue (T : Tensor K I J L) (τ : ℝ) : ℝ≥0∞ :=
  ⨆ w : ValueWitness T, ENNReal.ofReal (w.score τ)

/-- The witness-supremum formula holds definitionally for every tensor. -/
theorem fractionalValue_eq_iSup (T : Tensor K I J L) (τ : ℝ) :
    fractionalValue T τ = ⨆ w : ValueWitness T, ENNReal.ofReal (w.score τ) := rfl

/-- The zero value follows from the empty witness supremum. -/
@[simp]
theorem fractionalValue_zero (τ : ℝ) :
    fractionalValue (0 : Tensor K I J L) τ = 0 := by
  simp [fractionalValue]

/-- Any defining witness provides a lower bound on the tensor's value. -/
theorem ValueWitness.score_le_fractionalValue {T : Tensor K I J L}
    (w : ValueWitness T) (τ : ℝ) :
    ENNReal.ofReal (w.score τ) ≤ fractionalValue T τ :=
  le_iSup (fun w : ValueWitness T => ENNReal.ofReal (w.score τ)) w

end MatrixMultiplication.Tensor
