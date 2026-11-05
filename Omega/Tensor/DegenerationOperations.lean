module

public import Omega.Tensor.Degeneration
public import Omega.Tensor.RankOperations
public import Omega.Exponent
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Calculus of polynomial degenerations

Polynomial witnesses can be composed, tensored, and taken to tensor powers.
All constructions use formal polynomials, with no hypothesis about the
cardinality or characteristic of the coefficient field.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {R : Type*} {I J L I' J' L' I'' J'' L'' : Type*}

/-- The tensor power of a factor matrix, indexed by tuples of basis indices. -/
def matrixPower [CommMonoid R] (A : Matrix I' I R) (n : ℕ) :
    Matrix (Fin n → I') (Fin n → I) R :=
  fun i j => ∏ t, A (i t) (j t)

/-- Factor maps commute with Kronecker powers. -/
theorem map_kroneckerPower [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (T : Tensor R I J L) (n : ℕ) :
    map (matrixPower A n) (matrixPower B n) (matrixPower D n)
      (kroneckerPower T n) = kroneckerPower (map A B D T) n := by
  classical
  funext i j k
  simp only [map, matrixPower, kroneckerPower, Fintype.prod_sum,
    Finset.prod_mul_distrib]

@[simp]
theorem liftPolynomial_kroneckerPower [CommSemiring R]
    (T : Tensor R I J L) (n : ℕ) :
    liftPolynomial (kroneckerPower T n) = kroneckerPower (liftPolynomial T) n := by
  funext i j k
  simp [liftPolynomial, kroneckerPower]

private theorem product_leading_term [CommSemiring R] {α : Type*} [Fintype α]
    (d : ℕ) (s : α → R) (E : α → R[X]) :
    (∏ t, (X ^ d * C (s t) + X ^ (d + 1) * E t)) =
      X ^ (d * Fintype.card α) * C (∏ t, s t) +
        X ^ (d * Fintype.card α + 1) *
          (∏ t, (C (s t) + X * E t)).divX := by
  classical
  let P : R[X] := ∏ t, (C (s t) + X * E t)
  have hzero : P.coeff 0 = ∏ t, s t := by
    change constantCoeff P = _
    simp only [P, map_prod]
    apply Finset.prod_congr rfl
    intro t _
    change (C (s t) + X * E t).coeff 0 = _
    simp
  have hP : P = C (∏ t, s t) + X * P.divX := by
    rw [← hzero]
    exact (X_mul_divX_add P).symm.trans (add_comm _ _)
  calc
    _ = ∏ t, X ^ d * (C (s t) + X * E t) := by
      apply Finset.prod_congr rfl
      intro t _
      rw [pow_succ]
      ring
    _ = X ^ (d * Fintype.card α) * P := by
      simp [P, Finset.prod_mul_distrib, ← pow_mul]
    _ = _ := by rw [hP]; rw [pow_succ]; ring

/-- Tensor powers of a degeneration witness have order `order * n`.
The factor maps are explicit products of the original polynomial maps. -/
def DegenerationWitness.kroneckerPower [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (n : ℕ) :
    DegenerationWitness (kroneckerPower T n) (kroneckerPower S n) where
  order := w.order * n
  firstMap := matrixPower w.firstMap n
  secondMap := matrixPower w.secondMap n
  thirdMap := matrixPower w.thirdMap n
  remainder := fun i j k =>
    (∏ t, (C (S (i t) (j t) (k t)) + X * w.remainder (i t) (j t) (k t))).divX
  equation := by
    intro i j k
    rw [liftPolynomial_kroneckerPower, map_kroneckerPower]
    simp only [Tensor.kroneckerPower, w.equation]
    simpa using product_leading_term w.order
      (fun t => S (i t) (j t) (k t)) (fun t => w.remainder (i t) (j t) (k t))

@[simp]
theorem DegenerationWitness.kroneckerPower_order [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (n : ℕ) :
    (w.kroneckerPower n).order = w.order * n := rfl

/-- Degeneration is compatible with every nonnegative tensor power. -/
theorem Degenerates.kroneckerPower [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (h : Degenerates T S) (n : ℕ) :
    Degenerates (kroneckerPower T n) (kroneckerPower S n) := by
  obtain ⟨w⟩ := h
  exact ⟨w.kroneckerPower n⟩

/-- Applying factor maps is linear with respect to a common scalar. -/
theorem map_scale [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (a : R) (T : Tensor R I J L) :
    map A B D (fun i j k => a * T i j k) =
      fun i j k => a * map A B D T i j k := by
  funext i j k
  simp only [map, Finset.mul_sum, mul_left_comm, mul_comm]

/-- Changing the coefficient semiring commutes with the three factor maps. -/
theorem map_ringHom [CommSemiring R] {R₂ : Type*} [CommSemiring R₂]
    [Fintype I] [Fintype J] [Fintype L]
    (f : R →+* R₂) (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (T : Tensor R I J L) :
    (fun i j k => f (map A B D T i j k)) =
      map (A.map f) (B.map f) (D.map f) (fun i j k => f (T i j k)) := by
  funext i j k
  simp [map, Matrix.map_apply, map_mul]

/-- Factor maps preserve a two-term linear combination, written pointwise. -/
theorem map_linear_combination [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (a b : R) (T E : Tensor R I J L) :
    map A B D (fun i j k => a * T i j k + b * E i j k) =
      fun i j k => a * map A B D T i j k + b * map A B D E i j k := by
  funext i j k
  simp only [map, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    mul_left_comm, mul_comm]

/-- Substituting a power of the parameter expands all orders in a witness.
This equation, rather than a normalized witness, keeps the entire error gap. -/
theorem DegenerationWitness.expand_equation [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (m : ℕ) :
    map (w.firstMap.map (expand R m)) (w.secondMap.map (expand R m))
      (w.thirdMap.map (expand R m)) (liftPolynomial T) =
      fun i j k => X ^ (w.order * m) * C (S i j k) +
        X ^ ((w.order + 1) * m) * expand R m (w.remainder i j k) := by
  have h := map_ringHom (expand R m).toRingHom
    w.firstMap w.secondMap w.thirdMap (liftPolynomial T)
  have hlift : (fun i j k => expand R m (liftPolynomial T i j k)) =
      liftPolynomial T := by
    funext i j k
    simp [liftPolynomial]
  change (fun i j k => expand R m (map w.firstMap w.secondMap w.thirdMap
    (liftPolynomial T) i j k)) =
      map (w.firstMap.map (expand R m)) (w.secondMap.map (expand R m))
        (w.thirdMap.map (expand R m))
        (fun i j k => expand R m (liftPolynomial T i j k)) at h
  rw [hlift] at h
  rw [← h]
  funext i j k
  simp only [w.equation, _root_.map_add, map_mul, map_pow, expand_X, expand_C,
    ← pow_mul, Nat.mul_comm]

/-- Compose two polynomial witnesses, first opening an error gap large enough
for the second witness. The substitution is `X ↦ X^(v.order+1)`. -/
def DegenerationWitness.trans [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} {U : Tensor R I'' J'' L''}
    (w : DegenerationWitness T S) (v : DegenerationWitness S U) :
    DegenerationWitness T U where
  order := w.order * (v.order + 1) + v.order
  firstMap := v.firstMap * w.firstMap.map (expand R (v.order + 1))
  secondMap := v.secondMap * w.secondMap.map (expand R (v.order + 1))
  thirdMap := v.thirdMap * w.thirdMap.map (expand R (v.order + 1))
  remainder := v.remainder + map v.firstMap v.secondMap v.thirdMap
    (fun i j k => expand R (v.order + 1) (w.remainder i j k))
  equation := by
    intro i j k
    have hm := map_map (w.firstMap.map (expand R (v.order + 1)))
      (w.secondMap.map (expand R (v.order + 1)))
      (w.thirdMap.map (expand R (v.order + 1)))
      v.firstMap v.secondMap v.thirdMap (liftPolynomial T)
    rw [← hm, w.expand_equation (v.order + 1)]
    have hl := map_linear_combination v.firstMap v.secondMap v.thirdMap
      (X ^ (w.order * (v.order + 1))) (X ^ ((w.order + 1) * (v.order + 1)))
      (liftPolynomial S) (fun i j k => expand R (v.order + 1) (w.remainder i j k))
    dsimp only [liftPolynomial] at hl
    rw [hl]
    dsimp only
    have hv := v.equation i j k
    rw [hv]
    simp only [Pi.add_apply]
    rw [show (w.order + 1) * (v.order + 1) =
      w.order * (v.order + 1) + v.order + 1 by simp [Nat.add_mul, Nat.add_assoc]]
    simp only [pow_add, pow_one]
    ring

/-- Formal degeneration is transitive over any commutative semiring. -/
theorem Degenerates.trans [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'} {U : Tensor R I'' J'' L''}
    (hTS : Degenerates T S) (hSU : Degenerates S U) : Degenerates T U := by
  obtain ⟨w⟩ := hTS
  obtain ⟨v⟩ := hSU
  exact ⟨w.trans v⟩

@[simp]
theorem liftPolynomial_kronecker [CommSemiring R]
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    liftPolynomial (kronecker T S) = kronecker (liftPolynomial T) (liftPolynomial S) := by
  funext i j k
  simp [liftPolynomial, kronecker]

/-- Tensor products of two polynomial witnesses add their orders. -/
def DegenerationWitness.kronecker [CommSemiring R]
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (w : DegenerationWitness T T') (v : DegenerationWitness S S') :
    DegenerationWitness (kronecker T S) (kronecker T' S') where
  order := w.order + v.order
  firstMap := Matrix.kronecker w.firstMap v.firstMap
  secondMap := Matrix.kronecker w.secondMap v.secondMap
  thirdMap := Matrix.kronecker w.thirdMap v.thirdMap
  remainder := fun i j k => C (T' i.1 j.1 k.1) * v.remainder i.2 j.2 k.2 +
    w.remainder i.1 j.1 k.1 * C (S' i.2 j.2 k.2) +
    X * w.remainder i.1 j.1 k.1 * v.remainder i.2 j.2 k.2
  equation := by
    intro i j k
    rw [liftPolynomial_kronecker,
      map_kronecker w.firstMap w.secondMap w.thirdMap v.firstMap v.secondMap v.thirdMap]
    simp only [Tensor.kronecker, w.equation, v.equation, map_mul, pow_add, pow_one]
    ring

/-- Degeneration is compatible with binary Kronecker products. -/
theorem Degenerates.kronecker [CommSemiring R]
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (hT : Degenerates T T') (hS : Degenerates S S') :
    Degenerates (kronecker T S) (kronecker T' S') := by
  obtain ⟨w⟩ := hT
  obtain ⟨v⟩ := hS
  exact ⟨w.kronecker v⟩

/-- Scaling one factor map scales the resulting tensor. -/
theorem map_scale_first [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (a : R) (T : Tensor R I J L) :
    map (fun i j => a * A i j) B D T = fun i j k => a * map A B D T i j k := by
  funext i j k
  simp only [map, Finset.mul_sum, mul_assoc]

/-- Raise the order of a polynomial witness without changing its target. -/
def DegenerationWitness.shift [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    (w : DegenerationWitness T S) (n : ℕ) : DegenerationWitness T S where
  order := w.order + n
  firstMap := fun i j => X ^ n * w.firstMap i j
  secondMap := w.secondMap
  thirdMap := w.thirdMap
  remainder := w.remainder
  equation := by
    intro i j k
    rw [map_scale_first]
    dsimp only
    rw [w.equation]
    simp only [pow_add, pow_one]
    ring

@[simp]
theorem liftPolynomial_directSum [CommSemiring R]
    (T : Tensor R I J L) (S : Tensor R I' J' L') :
    liftPolynomial (directSum T S) = directSum (liftPolynomial T) (liftPolynomial S) := by
  funext i j k
  cases i <;> cases j <;> cases k <;> simp [liftPolynomial, directSum]

/-- Ordinary direct sums of witnesses, with orders aligned by scalar shifts. -/
def DegenerationWitness.directSum [CommSemiring R]
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (w : DegenerationWitness T T') (v : DegenerationWitness S S') :
    DegenerationWitness (directSum T S) (directSum T' S') where
  order := w.order + v.order
  firstMap := directSumMap (w.shift v.order).firstMap (v.shift w.order).firstMap
  secondMap := directSumMap (w.shift v.order).secondMap (v.shift w.order).secondMap
  thirdMap := directSumMap (w.shift v.order).thirdMap (v.shift w.order).thirdMap
  remainder := Tensor.directSum w.remainder v.remainder
  equation := by
    intro i j k
    have hm := map_directSum (w.shift v.order).firstMap (w.shift v.order).secondMap
      (w.shift v.order).thirdMap (v.shift w.order).firstMap
      (v.shift w.order).secondMap (v.shift w.order).thirdMap
      (liftPolynomial T) (liftPolynomial S)
    rw [liftPolynomial_directSum, hm]
    cases i <;> cases j <;> cases k <;>
      simp only [Tensor.directSum, _root_.map_zero, mul_zero, add_zero]
    · rename_i a b c
      exact (w.shift v.order).equation a b c
    · rename_i a b c
      simpa only [DegenerationWitness.shift, Nat.add_comm] using
        (v.shift w.order).equation a b c

/-- Degeneration is compatible with ordinary direct sums. -/
theorem Degenerates.directSum [CommSemiring R]
    {I₁ J₁ L₁ I₂ J₂ L₂ : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor R I J L} {S : Tensor R I' J' L'}
    {T' : Tensor R I₁ J₁ L₁} {S' : Tensor R I₂ J₂ L₂}
    (hT : Degenerates T T') (hS : Degenerates S S') :
    Degenerates (directSum T S) (directSum T' S') := by
  obtain ⟨w⟩ := hT
  obtain ⟨v⟩ := hS
  exact ⟨w.directSum v⟩

end MatrixMultiplication.Tensor
