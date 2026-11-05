module

public import Omega.ValueWitnessOperations
public import Omega.ValueScore
public import Omega.ValueWitnessBounds
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Products and powers of fractional symmetrized value

Product witnesses multiply their scores. The extended-real supremum therefore
gives supermultiplicativity, even outside the admissible interval. Transfers
of witnesses in both directions give the exact positive-power law. The unit
normalization supplies power zero in the admissible interval.
-/

@[expose] public section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

private theorem log_nat_pow_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (n m : ℕ) :
    Real.log ((a ^ n * b ^ m : ℕ) : ℝ) =
      (n : ℝ) * Real.log (a : ℝ) + (m : ℝ) * Real.log (b : ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp ha)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hb)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Real.log_mul (pow_ne_zero _ ha') (pow_ne_zero _ hb'), Real.log_pow, Real.log_pow]

/-- Cross-powering the integer witness parameters multiplies their scores. -/
@[simp]
theorem ValueWitness.product_score {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness T) (v : ValueWitness S) (τ : ℝ) :
    (w.product v).score τ = w.score τ * v.score τ := by
  apply Real.log_injOn_pos ((w.product v).score_pos τ)
    (mul_pos (w.score_pos τ) (v.score_pos τ))
  rw [Real.log_mul (w.score_pos τ).ne' (v.score_pos τ).ne']
  simp only [ValueWitness.log_score, ValueWitness.product_a, ValueWitness.product_b,
    ValueWitness.product_c, ValueWitness.product_d, ValueWitness.product_N]
  rw [log_nat_pow_mul w.ha v.ha, log_nat_pow_mul w.hb v.hb,
    log_nat_pow_mul w.hc v.hc, log_nat_pow_mul w.hd v.hd]
  simp only [Nat.cast_mul]
  have hN : (w.N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp w.hN)
  have hM : (v.N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp v.hN)
  field_simp
  ring

/-- Powering all four block parameters powers the score by the same amount. -/
@[simp]
theorem ValueWitness.tensorPower_score {T : Tensor K I J L} (w : ValueWitness T)
    (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) :
    (w.tensorPower n hn).score τ = w.score τ ^ n := by
  apply Real.log_injOn_pos ((w.tensorPower n hn).score_pos τ) (pow_pos (w.score_pos τ) n)
  simp only [Real.log_pow, ValueWitness.log_score, ValueWitness.tensorPower_a,
    ValueWitness.tensorPower_b, ValueWitness.tensorPower_c, ValueWitness.tensorPower_d,
    ValueWitness.tensorPower_N, Nat.cast_pow, Real.log_pow]
  ring

/-- Absorbing a positive tensor power into the witness exponent takes the
corresponding root of its score. -/
theorem ValueWitness.ofPower_score_pow {T : Tensor K I J L}
    (n : ℕ) (hn : 1 ≤ n) (w : ValueWitness (kroneckerPower T n)) (τ : ℝ) :
    (ValueWitness.ofPower n hn w).score τ ^ n = w.score τ := by
  apply Real.log_injOn_pos
    (pow_pos ((ValueWitness.ofPower n hn w).score_pos τ) n) (w.score_pos τ)
  simp only [Real.log_pow, ValueWitness.log_score, ValueWitness.ofPower_a,
    ValueWitness.ofPower_b, ValueWitness.ofPower_c, ValueWitness.ofPower_d,
    ValueWitness.ofPower_N, Nat.cast_mul]
  have hN : (w.N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp w.hN)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
  field_simp

/-- Fractional value is supermultiplicative for every real parameter,
including zero tensors and infinite values. -/
theorem fractionalValue_kronecker_ge (T : Tensor K I J L) (S : Tensor K I' J' L')
    (τ : ℝ) :
    fractionalValue T τ * fractionalValue S τ ≤ fractionalValue (kronecker T S) τ := by
  simp only [fractionalValue]
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro w
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro v
  rw [← ENNReal.ofReal_mul (w.score_pos τ).le, ← ValueWitness.product_score]
  exact le_iSup (fun u : ValueWitness (kronecker T S) => ENNReal.ofReal (u.score τ))
    (w.product v)

/-- Every positive tensor power obeys the exact value power law, for every
real parameter, including potentially infinite values. -/
theorem fractionalValue_pow_of_pos (T : Tensor K I J L) (n : ℕ) (hn : 1 ≤ n)
    (τ : ℝ) :
    fractionalValue (kroneckerPower T n) τ = fractionalValue T τ ^ n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
  apply le_antisymm
  · simp only [fractionalValue]
    apply iSup_le
    intro w
    rw [← ValueWitness.ofPower_score_pow n hn w τ,
      ENNReal.ofReal_pow ((ValueWitness.ofPower n hn w).score_pos τ).le]
    exact pow_le_pow_left' (le_iSup (fun v : ValueWitness T => ENNReal.ofReal (v.score τ))
      (ValueWitness.ofPower n hn w)) n
  · simp only [fractionalValue]
    rw [ENNReal.iSup_pow_of_ne_zero hn0]
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_pow (w.score_pos τ).le, ← ValueWitness.tensorPower_score w n hn τ]
    exact le_iSup (fun v : ValueWitness (kroneckerPower T n) => ENNReal.ofReal (v.score τ))
      (w.tensorPower n hn)

/-- The zeroth tensor power has value one throughout the admissible interval. -/
@[simp]
theorem fractionalValue_kroneckerPower_zero (T : Tensor K I J L) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (kroneckerPower T 0) τ = 1 := by
  apply le_antisymm
  · simpa only [asymptoticRank_kroneckerPower_zero, ENNReal.ofReal_one] using
      fractionalValue_le_asymptoticRank (kroneckerPower T 0) hτ hτω
  · apply one_le_fractionalValue
    intro hzero
    have h := congrArg rank hzero
    simp at h

/-- Fractional value is exactly multiplicative under all tensor powers in
the admissible interval, including the zeroth power and the zero tensor. -/
theorem fractionalValue_pow (T : Tensor K I J L) (n : ℕ) {τ : ℝ}
    (hτ : (2 : ℝ) / 3 ≤ τ) (hτω : τ ≤ omega K / 3) :
    fractionalValue (kroneckerPower T n) τ = fractionalValue T τ ^ n := by
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero] using fractionalValue_kroneckerPower_zero T hτ hτω
  · exact fractionalValue_pow_of_pos T n (Nat.one_le_iff_ne_zero.mpr hn) τ

end MatrixMultiplication.Tensor
