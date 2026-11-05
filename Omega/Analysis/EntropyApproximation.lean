module

public import Omega.Analysis.EntropyContinuity
public import Omega.Analysis.ProbabilityApproximation

/-!
# Passing entropy bounds from rational to real probabilities

Approximation with the same support justifies the final limiting step of
the manuscript's entropy proof, even when some fixed tensor values are zero.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace MatrixMultiplication

variable {H : Type*} [Fintype H]

/-- An entropy-weighted product bound for rational probabilities extends to
all real probabilities. No positivity of the fixed values is needed. -/
theorem entropy_weightedProduct_le_of_rational (v : H → ℝ) (τ B : ℝ)
    (hbound : ∀ r : H → ℚ, (∀ i, 0 ≤ r i) → (∑ i, r i) = 1 →
      (2 : ℝ) ^ (τ * entropy (fun i => (r i : ℝ))) *
        ∏ i, v i ^ (r i : ℝ) ≤ B)
    (q : H → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) :
    (2 : ℝ) ^ (τ * entropy q) * ∏ i, v i ^ q i ≤ B := by
  obtain ⟨r, hrnonneg, hrsum, hrsupport, hr⟩ :=
    rational_probability_approximation q hq hqsum
  have ht := entropy_weightedProduct_tendsto v τ hr (fun n i hi => by
    exact_mod_cast (hrsupport n i).mpr hi)
  exact le_of_tendsto ht (Filter.Eventually.of_forall fun n =>
    hbound (r n) (hrnonneg n) (hrsum n))

/-- It suffices to check the bound on normalized nonnegative integer counts,
the distributions used in the multinomial argument. -/
theorem entropy_weightedProduct_le_of_counts (v : H → ℝ) (τ B : ℝ)
    (hbound : ∀ c : H → ℕ, 0 < ∑ i, c i →
      (2 : ℝ) ^ (τ * entropy (fun i => (c i : ℝ) / (∑ j, c j : ℕ))) *
        ∏ i, v i ^ ((c i : ℝ) / (∑ j, c j : ℕ)) ≤ B)
    (q : H → ℝ) (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) :
    (2 : ℝ) ^ (τ * entropy q) * ∏ i, v i ^ q i ≤ B := by
  obtain ⟨c, N, hN, hsum, hsupport, hc⟩ :=
    probability_count_approximation q hq hqsum
  have ht := entropy_weightedProduct_tendsto v τ hc (fun n i hi => by
    simp [(hsupport n i).mpr hi])
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  have h := hbound (c n) (by rw [hsum]; exact hN n)
  simpa only [hsum] using h

end MatrixMultiplication
