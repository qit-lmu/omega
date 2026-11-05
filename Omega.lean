module

public import Omega.Tensor.Basic
public import Omega.Tensor.InvertibleEquivalence
public import Omega.Tensor.Examples
public import Omega.Tensor.Rank
public import Omega.Tensor.RankOperations
public import Omega.Tensor.Degeneration
public import Omega.Tensor.DegenerationOperations
public import Omega.Tensor.RationalDegeneration
public import Omega.Tensor.CoefficientRank
public import Omega.Tensor.Powers
public import Omega.Tensor.Asymptotic
public import Omega.Tensor.PowerReindex
public import Omega.Tensor.AsymptoticOperations
public import Omega.Tensor.AsymptoticSum
public import Omega.Tensor.DirectSumCopies
public import Omega.Tensor.AsymptoticDegeneration
public import Omega.Tensor.BorderRank
public import Omega.Tensor.Subrank
public import Omega.Tensor.MatrixSubrank
public import Omega.Tensor.MatrixSubrankSharp
public import Omega.LinearAlgebra.MatrixRank
public import Omega.LinearAlgebra.MatrixExtension
public import Omega.Tensor.Flattening
public import Omega.Tensor.FlatteningBounds
public import Omega.Tensor.FlatteningExamples
public import Omega.Tensor.MatrixTensor
public import Omega.Tensor.MatrixShapes
public import Omega.Tensor.MatrixBilinear
public import Omega.Tensor.FlatteningDegeneration
public import Omega.Tensor.FlatteningCopies
public import Omega.Tensor.Strassen
public import Omega.Tensor.Nonzero
public import Omega.Tensor.FactorPermutations
public import Omega.Tensor.Symmetrization
public import Omega.Tensor.SymmetrizationOperations
public import Omega.Tensor.SymmetrizationMatrix
public import Omega.Tensor.PermutedSymmetrization
public import Omega.Tensor.SymmetrizationDegeneration
public import Omega.Tensor.ValueOperations
public import Omega.Tensor.ScalingOperations
public import Omega.Tensor.MatrixMultiplication
public import Omega.Tensor.MatrixCapacity
public import Omega.Exponent
public import Omega.ExponentBounds
public import Omega.ExponentSize
public import Omega.AsymptoticSumInequality
public import Omega.FractionalValue
public import Omega.ValueWitnessUnit
public import Omega.ValueWitnessBounds
public import Omega.ValueMonotonicity
public import Omega.ValueRational
public import Omega.ValueWitnessOperations
public import Omega.ValueScore
public import Omega.ValueMultiplicativity
public import Omega.ValueWitnessScaling
public import Omega.ValueScalingScore
public import Omega.ValueScaling
public import Omega.ValueNormalization
public import Omega.ValueFiniteUnit
public import Omega.ValueOutsideRange
public import Omega.ValueSubrank
public import Omega.Analysis.Growth
public import Omega.Analysis.GammaGrowth
public import Omega.Analysis.GammaCoefficient
public import Omega.Analysis.RankGrowth
public import Omega.Analysis.MonotonePowers
public import Omega.Analysis.ExponentialBounds
public import Omega.Analysis.CapacityGrowth
public import Omega.Analysis.WitnessInterpolation
public import Omega.Analysis.StrassenBound

public import Omega.Tensor.PartialSum
public import Omega.Tensor.PartialSumOperations
public import Omega.Tensor.PartialSumCompatibility
public import Omega.Tensor.PartialSumPowers
public import Omega.Tensor.PartialSumCalculus
public import Omega.Tensor.ProductFamily
public import Omega.Tensor.MonomialDegeneration
public import Omega.Tensor.PolynomialDegeneration
public import Omega.Tensor.PolynomialRank
public import Omega.Tensor.PolynomialInterpolation
public import Omega.Tensor.ScalarExtensionRank
public import Omega.Tensor.PolynomialFiniteField
public import Omega.Tensor.PartialSumSeparation
public import Omega.Combinatorics.WordTypes
public import Omega.Tensor.WordProducts
public import Omega.Tensor.TypeSeparation
public import Omega.Analysis.TypeBounds
public import Omega.Analysis.Entropy
public import Omega.Analysis.MultinomialEntropy
public import Omega.Analysis.ProbabilityApproximation
public import Omega.Analysis.EntropyContinuity
public import Omega.Analysis.EntropyApproximation
public import Omega.ValuePartialSum
public import Omega.ValueStrassen
public import Omega.Tensor.SplitDegeneration
public import Omega.Tensor.ExactSequenceDegeneration
public import Omega.Tensor.PolynomialOperations
public import Omega.Tensor.PolynomialBilinear
public import Omega.Tensor.BivariateGrid
public import Omega.Tensor.PolynomialConcavity
public import Omega.Tensor.PolynomialTripling
public import Omega.ValuePolynomialSupport
public import Omega.ValuePolynomial
public import Omega.ValuePolynomialGamma
public import Omega.Main
public import Omega.ExponentInfimum
public import Omega.External.Prove2MeDefinitions
public import Omega.External.Prove2MeTensor
public import Omega.External.Prove2Me

/-!
# Matrix multiplication over arbitrary fields

This is the root module of the formalization of `material/main.tex`.
The main theorem is proved in `Omega.Main`. The blueprint records the checked
manuscript correspondence. `Omega.External.Prove2Me` derives the public
Prove2Me statement from the main theorem through equality of the exponents.
-/
