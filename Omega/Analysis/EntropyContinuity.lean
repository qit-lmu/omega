module

public import Omega.Analysis.Entropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Entropy limits with fixed zero coordinates

Entropy is continuous, including zero coordinates. For a fixed finite value
vector, the entropy-weighted product also passes to the limit when zero
probability coordinates remain zero. This is the support condition used in
the manuscript's rational-approximation step, including zero block values.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace MatrixMultiplication

variable {H : Type*} [Fintype H]

/-- Entropy passes to coordinatewise limits, including zero coordinates. -/
theorem entropy_tendsto {A : Type*} {l : Filter A} {p : A → H → ℝ} {q : H → ℝ}
    (h : ∀ i, Tendsto (fun a => p a i) l (𝓝 (q i))) :
    Tendsto (fun a => entropy (p a)) l (𝓝 (entropy q)) := by
  unfold entropy
  exact ((tendsto_finsetSum Finset.univ (fun i _ =>
    Real.continuous_mul_log.continuousAt.tendsto.comp (h i))).neg).div_const _

/-- The weighted product passes to the limit if coordinates that vanish
in the limiting probability vector stay zero throughout the approximation. -/
theorem entropy_weightedProduct_tendsto {A : Type*} {l : Filter A}
    (v : H → ℝ) (τ : ℝ) {p : A → H → ℝ} {q : H → ℝ}
    (h : ∀ i, Tendsto (fun a => p a i) l (𝓝 (q i)))
    (hzero : ∀ a i, q i = 0 → p a i = 0) :
    Tendsto (fun a => (2 : ℝ) ^ (τ * entropy (p a)) * ∏ i, v i ^ p a i)
      l (𝓝 ((2 : ℝ) ^ (τ * entropy q) * ∏ i, v i ^ q i)) := by
  apply Tendsto.mul
  · exact tendsto_const_nhds.rpow ((entropy_tendsto h).const_mul τ)
      (Or.inl (by norm_num))
  · apply tendsto_finsetProd Finset.univ
    intro i _
    by_cases hi : q i = 0
    · simp only [hzero _ i hi, hi, Real.rpow_zero]
      exact tendsto_const_nhds
    · exact (Real.continuousAt_const_rpow' hi).tendsto.comp (h i)

end MatrixMultiplication
