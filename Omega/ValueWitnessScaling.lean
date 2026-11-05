module

public import Omega.FractionalValue
public import Omega.Tensor.ScalingOperations

/-!
# Removing and adding a matrix-block factor in value witnesses
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K I J L I' J' L' : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

/-- Absorb a symmetrized matrix-block factor into the denominator parameters. -/
@[simps a b c d N]
def ValueWitness.stripMatrixBlock {T : Tensor K I J L} {S : Tensor K I' J' L'}
    {r q : ℕ} (w : ValueWitness S)
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul K q q q) r) (symmetrize T)))
    (hr : 1 ≤ r) (hq : 1 ≤ q) : ValueWitness T where
  a := w.a
  b := w.b
  c := w.c * r ^ w.N
  d := w.d * q ^ w.N
  N := w.N
  ha := w.ha
  hb := w.hb
  hc := one_le_mul_of_one_le_of_one_le w.hc (one_le_pow₀ hr)
  hd := one_le_mul_of_one_le_of_one_le w.hd (one_le_pow₀ hq)
  hN := w.hN
  degeneration := (valueSource_matrixBlock_equivalent r q h w.c w.d w.N).2.degenerates.trans
    w.degeneration

/-- Tensoring both sides of a witness with a matrix block supplies the
corresponding numerator parameters for the tensor with that symmetrized factor. -/
@[simps a b c d N]
def ValueWitness.addMatrixBlock {T : Tensor K I J L} {S : Tensor K I' J' L'}
    {r q : ℕ} (w : ValueWitness T)
    (h : Equivalent (symmetrize S)
      (kronecker (directSumCopies (matrixMul K q q q) r) (symmetrize T)))
    (hr : 1 ≤ r) (hq : 1 ≤ q) : ValueWitness S where
  a := w.a * r ^ w.N
  b := w.b * q ^ w.N
  c := w.c
  d := w.d
  N := w.N
  ha := one_le_mul_of_one_le_of_one_le w.ha (one_le_pow₀ hr)
  hb := one_le_mul_of_one_le_of_one_le w.hb (one_le_pow₀ hq)
  hc := w.hc
  hd := w.hd
  hN := w.hN
  degeneration := by
    have hblocks := matrixMul_copies_kronecker_equivalent (R := K)
      w.c w.d (r ^ w.N) (q ^ w.N)
    have hsource := (valueSource_matrixBlock_equivalent r q h w.c w.d w.N).trans
      ((hblocks.symm.kronecker (Equivalent.refl _)).trans
        (kronecker_swap_last_equivalent _ _ _))
    exact (hsource.1.degenerates.trans
      (w.degeneration.kronecker (Degenerates.refl _))).trans
        (matrixMul_copies_kronecker_equivalent (R := K)
          w.a w.b (r ^ w.N) (q ^ w.N)).1.degenerates

end MatrixMultiplication.Tensor
