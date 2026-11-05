module

public import Omega.Tensor.CoefficientRank
public import Omega.Tensor.DegenerationOperations
public import Omega.Tensor.Asymptotic

/-!
# Degeneration cannot increase asymptotic rank

An order-`d` degeneration gives an order-`d*n` degeneration of nth powers.
Coefficient extraction bounds the target power rank by `(d*n+2).choose 2`
times the source power rank. The weaker bound `(d*n+1)^2` suffices for the
limit proof: the nth root of this polynomial overhead tends to one.

The proof works over a commutative semiring, so in particular over every field,
including finite fields. It uses no evaluation points or scalar extensions.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {R : Type*} [CommSemiring R]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

/-- The exact binomial coefficient bound from the manuscript's proof of
degeneration monotonicity, valid also for the zeroth tensor power. -/
theorem DegenerationWitness.rank_kroneckerPower_le_choose
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (n : ℕ) :
    rank (Tensor.kroneckerPower S n) ≤
      (w.order * n + 2).choose 2 * rank (Tensor.kroneckerPower T n) := by
  simpa only [DegenerationWitness.kroneckerPower_order] using
    (w.kroneckerPower n).rank_le_choose

/-- A single degeneration witness controls all tensor-power ranks with a
quadratic overhead, uniformly in the power. -/
theorem DegenerationWitness.rank_kroneckerPower_le
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (n : ℕ) :
    rank (Tensor.kroneckerPower S n) ≤
      (w.order * n + 1) ^ 2 * rank (Tensor.kroneckerPower T n) := by
  simpa only [DegenerationWitness.kroneckerPower_order] using (w.kroneckerPower n).rank_le

/-- Asymptotic rank is monotone under algebraic degeneration over every field.
More generally, the same argument works over any commutative semiring. -/
theorem asymptoticRank_mono_degeneration
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Degenerates T S) : asymptoticRank S ≤ asymptoticRank T := by
  obtain ⟨w⟩ := h
  apply asymptoticRank_le_of_power_rank_le T S w.order 2
  intro n _
  exact w.rank_kroneckerPower_le n

/-- Ordinary restriction is a special case of degeneration monotonicity. -/
theorem asymptoticRank_mono
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Restricts T S) : asymptoticRank S ≤ asymptoticRank T :=
  asymptoticRank_mono_degeneration h.degenerates

/-- Equivalent tensors have equal asymptotic rank. -/
theorem asymptoticRank_eq_of_equivalent
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Equivalent T S) : asymptoticRank T = asymptoticRank S :=
  le_antisymm (asymptoticRank_mono h.2) (asymptoticRank_mono h.1)

end MatrixMultiplication.Tensor
