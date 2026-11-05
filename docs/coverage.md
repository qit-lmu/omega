# Formalization coverage and module map

[Project overview](../README.md) · [Development guide](development.md)

The [manifest](../blueprint/manifest.json) is the canonical correspondence
between the [manuscript](../material/main.tex) and checked Lean declarations.
This guide summarizes the results and their implementation locations.

## Formalized results

The main theorem and its supporting results are checked:

- Coefficient tensors, restriction and equivalence, Kronecker products, direct
  sums, and partial direct sums with a shared first factor.
- In equal ambient dimensions, mutual restriction is equivalent to invertible
  maps on the three factors. Rank-preserving maps on tensor supports extend
  to ambient automorphisms over every field.
- Diagonal, matrix-multiplication, and polynomial-multiplication tensors,
  including their coefficient identities for matrix and polynomial multiplication.
  The matrix tensor is exactly the bilinear multiplication structure tensor
  in standard matrix bases, including zero dimensions.
- Tensor rank as an attained minimum, with monotonicity, reindexing invariance,
  sum bounds, product bounds, and submultiplicativity of tensor-power ranks.
- Polynomial degeneration witnesses, composition, compatibility with tensor
  powers, products and direct sums, and leading coefficient identities.
- Equivalence of polynomial witnesses with the manuscript's rational-function
  specialization definition, over every field. Factor maps may have poles;
  only their tensor output must be regular at zero.
- Asymptotic rank as both an infimum and a limit of rank roots, and `omega`.
- Exact power multiplicativity of asymptotic rank, product submultiplicativity,
  and subadditivity for tensor addition and direct sums. The sum proof uses
  uniform exponential bounds and an expansion over subsets of power coordinates.
- Monotonicity of asymptotic rank under polynomial degeneration, over every
  field. Coefficient extraction gives the explicit bound
  `rank (S^n) ≤ choose(d*n+2,2) * rank (T^n)` for a witness of order `d`.
  This matches the exponent-triple count in Lemma 2.2; the coarser
  square bound remains available. Taking roots removes the polynomial overhead.
- Border rank as an attained minimum and the bounds
  `asymptoticRank T ≤ borderRank T ≤ rank T`.
- Subrank and border subrank as attained finite maxima, and asymptotic
  subrank as the bounded supremum of positive-power subrank roots. All three
  invariants have the expected values on zero and diagonal tensors.
- The cited sharp matrix-multiplication border-subrank lower bound
  `ceil(3*n^2/4)`, over every field. A central band of index pairs has exactly
  that size, and explicit monomial weights give the diagonal degeneration.
  The construction also covers size zero and works over any commutative semiring.
- The paper's Lemma 2.3: all three flattening ranks bound asymptotic rank and
  border rank from below. Flattening ranks multiply under tensor products
  and tensor powers, and cannot increase under polynomial degeneration.
- Exact rank, border rank, and asymptotic rank of diagonal tensors, including
  size zero; the first matrix-multiplication flattening has rank `l*m` for
  `n > 0`. Together with the elementary rank bound `l*m*n`, this proves
  `2 ≤ omega K ≤ 3` over every field.
- Matrix-multiplication dimension restrictions and product/power equivalences.
  The three special shapes in Definition 2.4 are identified by explicit
  coordinate bijections, including size zero.
  The paper's `eq:omega-log-n` holds in its power formulation:
  `asymptoticRank (matrixMul K n n n) = (n : ℝ) ^ omega K` for every `n ≥ 1`,
  including scalar multiplication, over every field. The explicit floor/ceiling
  tensor-power sandwich is also checked as `eq:n-matmul-to-2`.
- Lemma 2.7, the equal-block asymptotic sum identity:
  `asymptoticRank (directSumCopies (matrixMul K b b b) a) = a * b ^ omega K`
  for all `a,b ≥ 1`. The proof uses integer capacities and ceiling logarithms
  to make the manuscript's asymptotic rounding step explicit.
- Kronecker symmetrization over all six permutations, with invariance under
  `S₃`, compatibility with products and repeated blocks, the matrix-multiplication
  formula, and `asymptoticRank (symmetrize T) ≤ asymptoticRank T ^ 6`.
- Fractional-value witnesses and an extended nonnegative real supremum, with
  exact equality between the polynomial and rational-function definitions.
  The definition uses the same supremum for every tensor: the zero tensor
  has no witnesses, so its value is zero by the empty-supremum identity.
  Every witness is bounded by asymptotic
  rank for `2/3 ≤ τ ≤ omega K/3`; consequently the value is finite there.
  Nonzero tensors have a score-one witness and value at least one, and the
  unit diagonal has value exactly one in the admissible interval.
- All six properties in Lemma 4.6: degeneration monotonicity, invariance under
  `S₃`, exact tensor-power multiplicativity, product supermultiplicativity,
  and exact diagonal and matrix-multiplication scaling. Monotonicity follows
  from degeneration of the symmetrizations; their equivalence gives permutation
  invariance directly. The positive-power and scaling laws
  hold for every real parameter, including infinite values.
- Corollary 4.8: `Vτ(diagonal r) = r` and
  `Vτ(matrixMul l m n) = (l*m*n)^τ` in the admissible interval, including zero
  diagonal size and all positive matrix dimensions.
- Lemma 4.5: a nonzero tensor has finite value exactly on
  `2/3 ≤ τ ≤ omega K/3`. Finiteness forces unit normalization and the upper
  endpoint. The explicit degeneration from matrix multiplication of size
  `2q` to a diagonal of size `q^2` gives the lower endpoint. This avoids the
  sharper cited border-subrank estimate and asymptotic algorithm notation;
  the blueprint documents this alternative proof.
- The full Corollary 4.9: `asymptoticSubrank T ≤ Vτ(T) ≤ asymptoticRank T`
  in the admissible interval, both in extended nonnegative reals and as finite
  real inequalities. Taking the supremum of the subrank roots proves the
  lower bound directly; no subrank convergence theorem is needed.
- Polynomial multiplication is a degeneration of the diagonal of size
  `a+b-1` over every field, using interpolation over the rational function
  field and the checked specialization comparison. For positive `a,b`, its
  third flattening has rank `a+b-1`, so its border rank and asymptotic rank
  are both exactly `a+b-1`, including over finite fields.
- All ordinary-rank claims in Lemma 2.6: evaluation at `a+b-2` finite nodes
  and at infinity gives rank exactly `a+b-1` at the sharp field-size
  threshold. Rank descends through an extension of degree `k` with a factor
  of at most `k^2`. A finite extension of the checked logarithmic degree
  supplies the manuscript's small-field bound, with the exact ceiling-log formula
  under `q < a+b-2`. A generic rational-specialization theorem also proves
  `borderRank T ≤ rank (liftRational T)`.
- Partial direct sums of finite dependent families, their elementary
  calculus, and the separation theorem (Lemma 3.4). Selecting a multinomial
  type of size `Q` gives the exact `2Q-1` separation bound of Lemma 3.5.
  Independent block equivalences are used only after ordinary separation.
- Remark 3.3: a shared first-factor map assembles block restrictions, and
  common maps in both directions assemble equivalences. Explicit scalar
  blocks show why independent maps fail: the partial sums have first-flattening
  ranks one and two, although their corresponding blocks are equivalent.
- The partial-sum value inequalities (Lemmas 4.10 and 4.12), including zero
  block values and zero probabilities. The proof first sums the finite type
  bounds using the multinomial theorem, then removes the polynomial overhead
  by taking roots. Weighted AM–GM supplies the entropy bound afterward.
  This avoids multinomial entropy limits and rational approximation; the
  blueprint records this alternative proof.
- Remark 4.11: Strassen's tensor is an explicit partial sum with border rank
  and asymptotic rank exactly `n+1` for positive `n`, over every field.
  Binary value superadditivity proves `(2*n)^τ ≤ n+1` in the admissible
  interval. At `n=3` and `τ=omega K/3`, this gives
  `omega K ≤ 3*log 4/log 6 < 2.32112`, with exact rational logarithm
  certificates and independently of the main nine-quarters theorem.
- The full entropy variational identity (Lemma 2.8), with an attained maximum.
  Normalized coordinates attain the bound when their sum is positive; a point
  mass handles the all-zero case, with the convention `0^0 = 1` throughout.
- The multinomial entropy limit used in the manuscript's proof of
  Lemma 4.10, including zero symbol counts. Rational probability vectors
  approximate every probability vector with exactly the same support.
  Entropy and the weighted products pass to the limit even when block values
  vanish, so bounds for normalized integer counts extend to all probabilities.
- The polynomial-multiplication concavity degeneration, using explicit
  multiplication-by-`x-y`, boundary-section, and diagonal-tail coefficient
  maps. Three compatible block identities suffice for the split degeneration.
- The compatible-map degeneration (Lemma 5.1), for bilinear maps in arbitrary
  finite bases. Its hypotheses are an injective output inclusion, a surjective
  input quotient, a zero output composite, and bilinear compatibility.
  Short exact sequences remain a special case. Remark 5.2 is also checked:
  the bilinear map on the two quotients exists uniquely and gives the stated
  degeneration.
- The three-block polynomial-multiplication degeneration and its tripling
  specialization. The middle block exchanges the second and third factors;
  every block keeps the same first-factor map.
- The resulting value concavity and tripling inequalities, input-size
  symmetry, and scalar-multiplication normalization. These supply all four
  `GrowthHypotheses` for polynomial-multiplication value.
- Section 6's recurrence and the elementary `a^(4/3)` lower bound. Together
  with the uniform upper bound from the diagonal degeneration, they prove
  `omega K ≤ 9/4` over every field.
- Lemma 6.1's exact Gamma-function lower bound, its uniform lower bound by
  `a^(4/3)`, and its asymptotic coefficient `3/(2*Gamma(4/3))`. The Gamma
  recurrence proves the exact bound directly. The finite-product/Gamma identity
  in `eq:PM-Gamma` and the combined uniform inequalities in `eq:lem4/3` are
  exposed as checked declarations. Euler's limit formula supplies the
  asymptotic without Stirling's approximation.
- Remark 6.2's rigorous coefficient enclosure
  `1.67976 < 3/(2*Gamma(4/3)) < 1.67977`, proved with monotone rational
  product bounds and exact arithmetic checked by Lean.

Every mathematical entry in the audited blueprint is formalized.
The manuscript correspondence tracks all 34 active numbered
environments, all 14 labelled equations, and the tracked background assertions.
The degeneration lemma, quotient-map remark, exact coefficient count,
rational-specialization inequality, and finite-product identities have explicit
Lean correspondences. Elementary growth is part of the proof of Lemma 6.1 and supplies a
Gamma-independent route to the main theorem.

The exponent-convention remark, arithmetic-operation interpretation, and
historical comparisons are expository. The blueprint distinguishes manuscript
proofs from alternative formal proofs.

The checked library contains no `sorry` or project axioms. The axiom audit
checks all imported project declarations, including private helpers, against
`propext`, `Classical.choice`, and `Quot.sound` only.

## Module map

| Path | Purpose |
| --- | --- |
| [material/main.tex](../material/main.tex) | Manuscript with stable result labels |
| [blueprint/manifest.json](../blueprint/manifest.json) | Canonical correspondence, statements, proof plans, dependencies, and status |
| [blueprint/src/content.tex](../blueprint/src/content.tex) | Generated blueprint; edit the manifest instead |
| [Omega/Tensor/](../Omega/Tensor/) | Tensor operations, examples, rank, and degeneration |
| [Omega/LinearAlgebra/MatrixRank.lean](../Omega/LinearAlgebra/MatrixRank.lean) | Matrix Kronecker-rank multiplicativity |
| [Omega/LinearAlgebra/MatrixExtension.lean](../Omega/LinearAlgebra/MatrixExtension.lean) | Extending a rank-preserving matrix action to an invertible one |
| [Omega/Tensor/InvertibleEquivalence.lean](../Omega/Tensor/InvertibleEquivalence.lean) | Mutual restriction and invertible changes of tensor factors |
| [Omega/Exponent.lean](../Omega/Exponent.lean) | Asymptotic rank and the exponent over an arbitrary field |
| [Omega/ExponentInfimum.lean](../Omega/ExponentInfimum.lean) | Equality with the infimum of ordinary-rank logarithmic bounds |
| [Omega/External/Prove2MeDefinitions.lean](../Omega/External/Prove2MeDefinitions.lean) | Downloaded Prove2Me tensor, rank, and exponent definitions |
| [Omega/External/Prove2MeTensor.lean](../Omega/External/Prove2MeTensor.lean) | Equality of the tensor ranks in the two representations |
| [Omega/External/Prove2Me.lean](../Omega/External/Prove2Me.lean) | Exact Prove2Me statement as a corollary of our main theorem |
| [material/prove2me/](../material/prove2me/) | Original external statement and definitions, with provenance hashes |
| [Omega/ExponentBounds.lean](../Omega/ExponentBounds.lean) | Elementary bounds `2 ≤ omega K ≤ 3` over every field |
| [Omega/ExponentSize.lean](../Omega/ExponentSize.lean) | The paper's power identity for every `n ≥ 1` |
| [Omega/Tensor/MatrixShapes.lean](../Omega/Tensor/MatrixShapes.lean) | The three special matrix-multiplication shapes |
| [Omega/Tensor/MatrixBilinear.lean](../Omega/Tensor/MatrixBilinear.lean) | Matrix multiplication's coefficient and structure-tensor identities |
| [Omega/Tensor/Strassen.lean](../Omega/Tensor/Strassen.lean) | Strassen's tensor and its exact border and asymptotic ranks |
| [Omega/Tensor/MatrixSubrankSharp.lean](../Omega/Tensor/MatrixSubrankSharp.lean) | The sharp matrix-multiplication border-subrank lower bound |
| [Omega/Combinatorics/CentralBand.lean](../Omega/Combinatorics/CentralBand.lean) | Exact cardinality of the central band of index pairs |
| [Omega/Tensor/PartialSumCompatibility.lean](../Omega/Tensor/PartialSumCompatibility.lean) | Shared-map transport and the partial-sum counterexample |
| [Omega/ValueStrassen.lean](../Omega/ValueStrassen.lean) | The Strassen value inequality and exponent corollary |
| [Omega/Analysis/StrassenBound.lean](../Omega/Analysis/StrassenBound.lean) | Exact logarithmic and certified decimal Strassen bounds |
| [Omega/AsymptoticSumInequality.lean](../Omega/AsymptoticSumInequality.lean) | Equal-block asymptotic sum identity over every field |
| [Omega/FractionalValue.lean](../Omega/FractionalValue.lean) | Polynomial degeneration witnesses and extended-real fractional value |
| [Omega/ValueWitnessUnit.lean](../Omega/ValueWitnessUnit.lean) | A score-one witness for every nonzero tensor |
| [Omega/ValueWitnessBounds.lean](../Omega/ValueWitnessBounds.lean) | Endpoint bounds, finiteness, and unit normalization |
| [Omega/Tensor/RationalDegeneration.lean](../Omega/Tensor/RationalDegeneration.lean) | Equivalence with rational-function specialization |
| [Omega/ValueRational.lean](../Omega/ValueRational.lean) | Equality of the two fractional-value definitions |
| [Omega/ValueMonotonicity.lean](../Omega/ValueMonotonicity.lean) | Monotonicity and invariance under all factor permutations |
| [Omega/ValueMultiplicativity.lean](../Omega/ValueMultiplicativity.lean) | Product supermultiplicativity and exact tensor-power laws |
| [Omega/ValueScaling.lean](../Omega/ValueScaling.lean) | Exact diagonal and matrix-multiplication scaling |
| [Omega/ValueNormalization.lean](../Omega/ValueNormalization.lean) | Values of diagonal and matrix-multiplication tensors |
| [Omega/ValueFiniteUnit.lean](../Omega/ValueFiniteUnit.lean) | Unit normalization from finiteness and the upper admissible endpoint |
| [Omega/Tensor/MatrixSubrank.lean](../Omega/Tensor/MatrixSubrank.lean) | Explicit quadratic diagonal degeneration of matrix multiplication |
| [Omega/ValueOutsideRange.lean](../Omega/ValueOutsideRange.lean) | Infinite value outside the admissible interval and exact finiteness criterion |
| [Omega/Tensor/Subrank.lean](../Omega/Tensor/Subrank.lean) | Attained subrank maxima and the asymptotic subrank supremum |
| [Omega/ValueSubrank.lean](../Omega/ValueSubrank.lean) | The complete subrank/value/rank sandwich |
| [Omega/Tensor/PolynomialDegeneration.lean](../Omega/Tensor/PolynomialDegeneration.lean) | Uniform diagonal-to-polynomial-multiplication degeneration |
| [Omega/Tensor/PolynomialRank.lean](../Omega/Tensor/PolynomialRank.lean) | Full third-flattening rank and exact border/asymptotic ranks |
| [Omega/Tensor/PolynomialInterpolation.lean](../Omega/Tensor/PolynomialInterpolation.lean) | Sharp ordinary rank using evaluation at infinity |
| [Omega/Tensor/ScalarExtensionRank.lean](../Omega/Tensor/ScalarExtensionRank.lean) | Rank descent with square-degree overhead |
| [Omega/Tensor/PolynomialFiniteField.lean](../Omega/Tensor/PolynomialFiniteField.lean) | Finite-extension construction and the small-field rank bound |
| [Omega/Tensor/PolynomialBilinear.lean](../Omega/Tensor/PolynomialBilinear.lean) | Polynomial multiplication's coefficient identity |
| [Omega/Tensor/PolynomialOperations.lean](../Omega/Tensor/PolynomialOperations.lean) | Shared-first-factor copies and coordinate equivalences |
| [Omega/Tensor/SplitDegeneration.lean](../Omega/Tensor/SplitDegeneration.lean) | Degeneration from three compatible block identities |
| [Omega/Tensor/ExactSequenceDegeneration.lean](../Omega/Tensor/ExactSequenceDegeneration.lean) | Compatible bilinear maps, quotient construction, and degeneration |
| [Omega/Tensor/BivariateGrid.lean](../Omega/Tensor/BivariateGrid.lean) | Edge, boundary-section, and diagonal-tail coefficient maps |
| [Omega/Tensor/PolynomialConcavity.lean](../Omega/Tensor/PolynomialConcavity.lean) | Polynomial-multiplication concavity degeneration |
| [Omega/Tensor/PolynomialTripling.lean](../Omega/Tensor/PolynomialTripling.lean) | Three-block degeneration with a transposed middle block |
| [Omega/Tensor/PartialSumSeparation.lean](../Omega/Tensor/PartialSumSeparation.lean) | Partial-direct-sum separation over every field |
| [Omega/Combinatorics/WordTypes.lean](../Omega/Combinatorics/WordTypes.lean) | Word counts and exact multinomial type cardinalities |
| [Omega/Tensor/TypeSeparation.lean](../Omega/Tensor/TypeSeparation.lean) | Separation of a multinomial type with the exact copy count |
| [Omega/ValuePartialSum.lean](../Omega/ValuePartialSum.lean) | Finite and binary partial-sum superadditivity and entropy bounds |
| [Omega/Analysis/TypeBounds.lean](../Omega/Analysis/TypeBounds.lean) | Summing finite type bounds and removing polynomial overhead |
| [Omega/Analysis/Entropy.lean](../Omega/Analysis/Entropy.lean) | Entropy, weighted AM–GM, and the attained variational maximum |
| [Omega/Analysis/MultinomialEntropy.lean](../Omega/Analysis/MultinomialEntropy.lean) | Logarithmic and root limits of multinomial coefficients |
| [Omega/Analysis/ProbabilityApproximation.lean](../Omega/Analysis/ProbabilityApproximation.lean) | Rational approximation with exactly unchanged support |
| [Omega/Analysis/EntropyContinuity.lean](../Omega/Analysis/EntropyContinuity.lean) | Entropy and weighted-product limits with zero coordinates |
| [Omega/Analysis/EntropyApproximation.lean](../Omega/Analysis/EntropyApproximation.lean) | Transfer of bounds from rational to real probability vectors |
| [Omega/ValuePolynomialSupport.lean](../Omega/ValuePolynomialSupport.lean) | Polynomial symmetry and copies scaling |
| [Omega/ValuePolynomial.lean](../Omega/ValuePolynomial.lean) | Polynomial value inequalities and verified growth hypotheses |
| [Omega/Analysis/Growth.lean](../Omega/Analysis/Growth.lean) | Independent numerical part of Section 6 |
| [Omega/Analysis/GammaGrowth.lean](../Omega/Analysis/GammaGrowth.lean) | Exact Gamma lower bound and its asymptotic coefficient |
| [Omega/Analysis/GammaCoefficient.lean](../Omega/Analysis/GammaCoefficient.lean) | Certified rational enclosure of the Gamma coefficient |
| [Omega/ValuePolynomialGamma.lean](../Omega/ValuePolynomialGamma.lean) | The sharper Gamma bound for polynomial-multiplication value |
| [Omega/Main.lean](../Omega/Main.lean) | The closed theorem `omega K ≤ 9/4` over every field |
| [Omega/Analysis/RankGrowth.lean](../Omega/Analysis/RankGrowth.lean) | Polynomial overhead and limits of rank roots |
| [Omega/Analysis/MonotonePowers.lean](../Omega/Analysis/MonotonePowers.lean) | Comparing integer bases to prove a real power law |
| [Omega/Analysis/ExponentialBounds.lean](../Omega/Analysis/ExponentialBounds.lean) | Uniform exponential bounds from root limits |
| [Omega/Analysis/CapacityGrowth.lean](../Omega/Analysis/CapacityGrowth.lean) | Integer capacities and ceiling-logarithm growth comparison |
| [Omega/Analysis/WitnessInterpolation.lean](../Omega/Analysis/WitnessInterpolation.lean) | Bounding witness scores between their endpoint exponents |
| [Omega.lean](../Omega.lean) | Public root importing every project module |
| [scripts/](../scripts/) | Blueprint rendering, coverage checks, declaration checks, and axiom audit |

