module

public import Omega.FractionalValue
public import Omega.Tensor.ValueOperations

/-!
# Products and powers of fractional-value witnesses

Witnesses combine through tensor products of their polynomial degenerations.
Cross-powering makes the symmetrized exponents agree. All integer parameters
remain explicit, allowing the score identities to be proved independently.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

variable {K : Type*} [Field K]
variable {I J L I' J' L' : Type*}
variable [Fintype I] [Fintype J] [Fintype L]
variable [Fintype I'] [Fintype J'] [Fintype L']

/-- Power a witness degeneration and normalize all repeated matrix blocks. -/
theorem ValueWitness.poweredDegeneration {T : Tensor K I J L}
    (w : ValueWitness T) (n : ℕ) :
    Degenerates
      (kronecker (directSumCopies (matrixMul K (w.d ^ n) (w.d ^ n) (w.d ^ n)) (w.c ^ n))
        (kroneckerPower (symmetrize T) (w.N * n)))
      (directSumCopies (matrixMul K (w.b ^ n) (w.b ^ n) (w.b ^ n)) (w.a ^ n)) :=
  ((valueSource_kroneckerPower_equivalent (symmetrize T) w.c w.d w.N n).2.degenerates.trans
    (w.degeneration.kroneckerPower n)).trans
      (matrixMul_copies_kroneckerPower_equivalent (R := K) w.a w.b n).1.degenerates

/-- Cross-power two witnesses to obtain a witness for the tensor product.
The symmetrized exponent is the product of the original exponents. -/
@[simps a b c d N]
def ValueWitness.product {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (w : ValueWitness T) (v : ValueWitness S) : ValueWitness (kronecker T S) where
  a := w.a ^ v.N * v.a ^ w.N
  b := w.b ^ v.N * v.b ^ w.N
  c := w.c ^ v.N * v.c ^ w.N
  d := w.d ^ v.N * v.d ^ w.N
  N := w.N * v.N
  ha := one_le_mul_of_one_le_of_one_le (one_le_pow₀ w.ha) (one_le_pow₀ v.ha)
  hb := one_le_mul_of_one_le_of_one_le (one_le_pow₀ w.hb) (one_le_pow₀ v.hb)
  hc := one_le_mul_of_one_le_of_one_le (one_le_pow₀ w.hc) (one_le_pow₀ v.hc)
  hd := one_le_mul_of_one_le_of_one_le (one_le_pow₀ w.hd) (one_le_pow₀ v.hd)
  hN := one_le_mul_of_one_le_of_one_le w.hN v.hN
  degeneration := by
    have hT := w.poweredDegeneration v.N
    have hS := v.poweredDegeneration w.N
    rw [Nat.mul_comm v.N w.N] at hS
    have hblocks := matrixMul_copies_kronecker_equivalent (R := K)
      (w.c ^ v.N) (w.d ^ v.N) (v.c ^ w.N) (v.d ^ w.N)
    have hsym := ((symmetrize_kronecker_equivalent T S).kroneckerPower (w.N * v.N)).trans
      (kroneckerPower_kronecker_equivalent (symmetrize T) (symmetrize S) (w.N * v.N))
    have hsource := (hblocks.symm.kronecker hsym).trans
      (kronecker_four_shuffle_equivalent _ _ _ _)
    exact (hsource.1.degenerates.trans (hT.kronecker hS)).trans
      (matrixMul_copies_kronecker_equivalent (R := K)
        (w.a ^ v.N) (w.b ^ v.N) (v.a ^ w.N) (v.b ^ w.N)).1.degenerates

/-- A witness for a positive tensor power is a witness for the original tensor,
with the power absorbed into the symmetrized exponent. -/
@[simps a b c d N]
def ValueWitness.ofPower {T : Tensor K I J L} (n : ℕ) (hn : 1 ≤ n)
    (w : ValueWitness (kroneckerPower T n)) : ValueWitness T where
  a := w.a
  b := w.b
  c := w.c
  d := w.d
  N := n * w.N
  ha := w.ha
  hb := w.hb
  hc := w.hc
  hd := w.hd
  hN := one_le_mul_of_one_le_of_one_le hn w.hN
  degeneration :=
    (((Equivalent.refl _).kronecker
      (symmetrize_kroneckerPower_iterated_equivalent T n w.N).symm).1.degenerates).trans
        w.degeneration

/-- Power all four matrix-block parameters while keeping the witness exponent;
this gives a witness for the corresponding positive tensor power. -/
@[simps a b c d N]
def ValueWitness.tensorPower {T : Tensor K I J L} (w : ValueWitness T)
    (n : ℕ) (_hn : 1 ≤ n) : ValueWitness (kroneckerPower T n) where
  a := w.a ^ n
  b := w.b ^ n
  c := w.c ^ n
  d := w.d ^ n
  N := w.N
  ha := one_le_pow₀ w.ha
  hb := one_le_pow₀ w.hb
  hc := one_le_pow₀ w.hc
  hd := one_le_pow₀ w.hd
  hN := w.hN
  degeneration := by
    have h := w.poweredDegeneration n
    rw [Nat.mul_comm w.N n] at h
    exact (((Equivalent.refl _).kronecker
      (symmetrize_kroneckerPower_iterated_equivalent T n w.N)).1.degenerates).trans h

end MatrixMultiplication.Tensor
