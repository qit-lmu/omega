module

public import Omega.ValueMonotonicity
public import Omega.Tensor.RationalDegeneration

/-!
# Fractional value agrees with the manuscript's rational-function definition

Replacing polynomial degeneration witnesses by rational factor maps regular
on the output preserves every integer parameter and every score. The resulting
extended-real supremum is therefore exactly the implemented fractional value.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]

/-- A witness written using the manuscript's rational-function degeneration relation. -/
structure RationalValueWitness (T : Tensor K I J L) where
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
  degeneration : RationalDegenerates
    (kronecker (directSumCopies (matrixMul K d d d) c)
      (kroneckerPower (symmetrize T) N))
    (directSumCopies (matrixMul K b b b) a)

/-- Clear the rational denominators without changing the witness parameters. -/
def RationalValueWitness.toPolynomial {T : Tensor K I J L}
    (w : RationalValueWitness T) : ValueWitness T :=
  ⟨w.a, w.b, w.c, w.d, w.N, w.ha, w.hb, w.hc, w.hd, w.hN, w.degeneration.degenerates⟩

/-- Regard a polynomial leading-term witness as rational specialization data. -/
def ValueWitness.toRational {T : Tensor K I J L}
    (w : ValueWitness T) : RationalValueWitness T :=
  ⟨w.a, w.b, w.c, w.d, w.N, w.ha, w.hb, w.hc, w.hd, w.hN, w.degeneration.rationalDegenerates⟩

/-- The score in the rational-function definition is the same positive real expression. -/
def RationalValueWitness.score {T : Tensor K I J L}
    (w : RationalValueWitness T) (τ : ℝ) : ℝ :=
  (((w.a : ℝ) * (w.b : ℝ) ^ (3 * τ)) /
    ((w.c : ℝ) * (w.d : ℝ) ^ (3 * τ))) ^ ((6 * w.N : ℕ) : ℝ)⁻¹

@[simp]
theorem RationalValueWitness.score_toPolynomial {T : Tensor K I J L}
    (w : RationalValueWitness T) (τ : ℝ) : w.toPolynomial.score τ = w.score τ := rfl

@[simp]
theorem ValueWitness.score_toRational {T : Tensor K I J L}
    (w : ValueWitness T) (τ : ℝ) : w.toRational.score τ = w.score τ := rfl

/-- The two types of witnesses have exactly the same parameters and admissibility. -/
def valueWitnessEquivRational (T : Tensor K I J L) : ValueWitness T ≃ RationalValueWitness T where
  toFun := ValueWitness.toRational
  invFun := RationalValueWitness.toPolynomial
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- The supremum using rational-function witnesses, including an empty supremum at zero. -/
def rationalFractionalValue (T : Tensor K I J L) (τ : ℝ) : ℝ≥0∞ :=
  ⨆ w : RationalValueWitness T, ENNReal.ofReal (w.score τ)

/-- The implemented fractional value equals the manuscript's rational-function supremum. -/
theorem fractionalValue_eq_rationalFractionalValue (T : Tensor K I J L) (τ : ℝ) :
    fractionalValue T τ = rationalFractionalValue T τ := by
  rw [fractionalValue_eq_iSup, rationalFractionalValue]
  apply le_antisymm
  · apply iSup_le
    intro w
    exact le_iSup_of_le w.toRational le_rfl
  · apply iSup_le
    intro w
    exact le_iSup_of_le w.toPolynomial le_rfl

@[simp]
theorem rationalFractionalValue_zero (τ : ℝ) :
    rationalFractionalValue (0 : Tensor K I J L) τ = 0 := by
  rw [← fractionalValue_eq_rationalFractionalValue, fractionalValue_zero]

/-- Fractional value is monotone under the rational-function degeneration relation. -/
theorem fractionalValue_mono_rational [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : RationalDegenerates T S) (τ : ℝ) : fractionalValue S τ ≤ fractionalValue T τ :=
  fractionalValue_mono h.degenerates τ

end MatrixMultiplication.Tensor
