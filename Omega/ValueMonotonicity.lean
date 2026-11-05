module

public import Omega.ValueWitnessUnit
public import Omega.Tensor.SymmetrizationDegeneration
public import Omega.Tensor.PermutedSymmetrization

/-!
# Fractional-value monotonicity and permutation invariance

Witnesses transfer whenever the symmetrized source degenerates to the
symmetrized target. This stronger hypothesis directly gives permutation
invariance, as well as ordinary degeneration monotonicity.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

/-- Transfer a value witness along a degeneration of symmetrizations. -/
def ValueWitness.ofSymmetrizeDegenerates {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness S) (h : Degenerates (symmetrize T) (symmetrize S)) : ValueWitness T where
  a := w.a
  b := w.b
  c := w.c
  d := w.d
  N := w.N
  ha := w.ha
  hb := w.hb
  hc := w.hc
  hd := w.hd
  hN := w.hN
  degeneration := ((Degenerates.refl _).kronecker (h.kroneckerPower w.N)).trans w.degeneration

@[simp]
theorem ValueWitness.score_ofSymmetrizeDegenerates
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness S) (h : Degenerates (symmetrize T) (symmetrize S)) (τ : ℝ) :
    (w.ofSymmetrizeDegenerates h).score τ = w.score τ := rfl

/-- Fractional value is monotone under degeneration of symmetrizations. -/
theorem fractionalValue_mono_of_symmetrize_degenerates
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Degenerates (symmetrize T) (symmetrize S)) (τ : ℝ) :
    fractionalValue S τ ≤ fractionalValue T τ := by
  rw [fractionalValue_eq_iSup S, fractionalValue_eq_iSup T]
  apply iSup_le
  intro w
  exact le_iSup_of_le (w.ofSymmetrizeDegenerates h) le_rfl

/-- Polynomial degeneration cannot increase fractional value, for any real parameter. -/
theorem fractionalValue_mono {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Degenerates T S) (τ : ℝ) : fractionalValue S τ ≤ fractionalValue T τ :=
  fractionalValue_mono_of_symmetrize_degenerates h.symmetrize τ

/-- Equivalent symmetrizations give equal fractional values. -/
theorem fractionalValue_eq_of_symmetrize_equivalent
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Equivalent (symmetrize T) (symmetrize S)) (τ : ℝ) :
    fractionalValue T τ = fractionalValue S τ :=
  le_antisymm (fractionalValue_mono_of_symmetrize_degenerates h.2.degenerates τ)
    (fractionalValue_mono_of_symmetrize_degenerates h.1.degenerates τ)

/-- Tensor equivalence preserves fractional value. -/
theorem fractionalValue_eq_of_equivalent
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Equivalent T S) (τ : ℝ) : fractionalValue T τ = fractionalValue S τ :=
  le_antisymm (fractionalValue_mono h.2.degenerates τ) (fractionalValue_mono h.1.degenerates τ)

universe u v

/-- Fractional value is invariant under every permutation of the three factors. -/
theorem fractionalValue_permute {K : Type v} [Field K] {I J L : Type u}
    [Fintype I] [Fintype J] [Fintype L]
    (p : FactorPermutation) (T : Tensor K I J L) (τ : ℝ) :
    fractionalValue (permute p T) τ = fractionalValue T τ :=
  fractionalValue_eq_of_symmetrize_equivalent (symmetrize_permute p T) τ

/-- The same invariance using the actual symmetric group on three letters. -/
theorem fractionalValue_permuteS3 {K : Type v} [Field K] {I J L : Type u}
    [Fintype I] [Fintype J] [Fintype L]
    (σ : Equiv.Perm (Fin 3)) (T : Tensor K I J L) (τ : ℝ) :
    fractionalValue (permuteS3 σ T) τ = fractionalValue T τ :=
  fractionalValue_eq_of_symmetrize_equivalent (symmetrize_permuteS3 σ T) τ

end MatrixMultiplication.Tensor
