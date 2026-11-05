module

public import Omega.Tensor.MonomialDegeneration
public import Omega.Tensor.Subrank
public import Omega.Tensor.FactorPermutations
import Mathlib.Tactic.Linarith

/-!
# Diagonal degenerations of matrix multiplication

The triples `(i,j,i+j)` with `i,j < q` provide `q²` diagonal terms in
matrix multiplication of size `2q`. Nonnegative monomial weights discard
all mixed terms. This weaker quadratic bound suffices for value divergence
below the parameter `2/3`.

More generally, pairs with `t ≤ i+j < t+n` give diagonal terms in size `n`
matrix multiplication. The central-band count gives the sharp bound in
`Omega.Tensor.MatrixSubrankSharp`.
-/

@[expose] public section

namespace MatrixMultiplication.Tensor

private theorem quadratic_weight_lower (i j u z q : ℕ)
    (hb : j ^ 2 ≤ q ^ 2 + u ^ 2) (hc : 2 * i * (i + z) ≤ 4 * q ^ 2)
    (hs : u + j = i + z) :
    5 * q ^ 2 ≤ (i + j) ^ 2 + (q ^ 2 + u ^ 2 - j ^ 2) +
      (4 * q ^ 2 - 2 * i * (i + z)) := by
  have hsubb := Nat.sub_add_cancel hb
  have hsubc := Nat.sub_add_cancel hc
  have hrel := congrArg (fun n => 2 * i * n) hs
  nlinarith [two_mul_le_add_sq i u]

private theorem quadratic_weight_eq_iff (i j u z q : ℕ)
    (hb : j ^ 2 ≤ q ^ 2 + u ^ 2) (hc : 2 * i * (i + z) ≤ 4 * q ^ 2)
    (hs : u + j = i + z) :
    (i + j) ^ 2 + (q ^ 2 + u ^ 2 - j ^ 2) +
      (4 * q ^ 2 - 2 * i * (i + z)) = 5 * q ^ 2 ↔ i = u := by
  have hsubb := Nat.sub_add_cancel hb
  have hsubc := Nat.sub_add_cancel hc
  have hrel := congrArg (fun n => 2 * i * n) hs
  constructor
  · intro heq
    have h : (i : ℤ) = u := by nlinarith [sq_nonneg ((i : ℤ) - u)]
    exact_mod_cast h
  · intro h
    subst u
    nlinarith

/-- Matrix multiplication of size `2q` degenerates to a diagonal of size `q²`.
The construction is valid over every commutative semiring, including `q=0`. -/
theorem matrixMul_degenerates_diagonal_quadratic (R : Type*) [CommSemiring R] (q : ℕ) :
    Degenerates (matrixMul R (2 * q) (2 * q) (2 * q)) (diagonal R (q ^ 2)) := by
  classical
  let H := Fin q × Fin q
  let inc (i : Fin q) : Fin (2 * q) := ⟨i.val, by omega⟩
  let out (x : H) : Fin (2 * q) := ⟨x.1.val + x.2.val, by
    have := x.1.isLt
    have := x.2.isLt
    omega⟩
  let D : Tensor R H H H := fun x y z => if x = y ∧ y = z then 1 else 0
  let a (x : H) := (x.1.val + x.2.val) ^ 2
  let b (y : H) := q ^ 2 + y.1.val ^ 2 - y.2.val ^ 2
  let c (z : H) := 4 * q ^ 2 - 2 * z.1.val * (z.1.val + z.2.val)
  let S (x y z : H) : Prop := x.1.val = z.1.val ∧ x.2.val = y.2.val ∧
    y.1.val + y.2.val = z.1.val + z.2.val
  have hcoeff (x y z : H) :
      matrixMul R (2 * q) (2 * q) (2 * q)
        (inc x.1, inc x.2) (inc y.2, out y) (inc z.1, out z) =
      if S x y z then 1 else 0 := by
    simp only [matrixMul, inc, out, Fin.mk.injEq]
    rfl
  have hb (y : H) : y.2.val ^ 2 ≤ q ^ 2 + y.1.val ^ 2 :=
    (Nat.pow_le_pow_left y.2.isLt.le 2).trans (Nat.le_add_right _ _)
  have hc (z : H) : 2 * z.1.val * (z.1.val + z.2.val) ≤ 4 * q ^ 2 := by
    calc
      _ ≤ 2 * q * (2 * q) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 z.1.isLt.le)
        (by have := z.1.isLt; have := z.2.isLt; omega)
      _ = _ := by ring
  have hdeg : Degenerates (matrixMul R (2 * q) (2 * q) (2 * q)) D := by
    apply degenerates_of_monomial_pullback _ D
      (fun x => (inc x.1, inc x.2)) (fun y => (inc y.2, out y))
      (fun z => (inc z.1, out z)) a b c (5 * q ^ 2)
    · intro x y z hlow
      rw [hcoeff]
      split_ifs with hs
      · obtain ⟨hi, hj, hk⟩ := hs
        have hw := quadratic_weight_lower z.1.val y.2.val y.1.val z.2.val q
          (hb y) (hc z) hk
        dsimp only [a, b, c] at hlow
        rw [hi, hj] at hlow
        omega
      · rfl
    · intro x y z
      rw [hcoeff]
      by_cases hs : S x y z
      · obtain ⟨hi, hj, hk⟩ := hs
        have hw := quadratic_weight_eq_iff z.1.val y.2.val y.1.val z.2.val q
          (hb y) (hc z) hk
        have heq : a x + b y + c z = 5 * q ^ 2 ↔ x = y ∧ y = z := by
          dsimp only [a, b, c]
          rw [hi, hj, hw]
          constructor
          · intro h
            have hyz : y = z := Prod.ext (Fin.ext h.symm) (Fin.ext (by omega))
            have hxy : x = y := Prod.ext (Fin.ext (by omega)) (Fin.ext hj)
            exact ⟨hxy, hyz⟩
          · rintro ⟨rfl, rfl⟩
            rfl
        simp only [D, ite_eq_left (show S x y z from ⟨hi, hj, hk⟩), heq]
      · have hdiag : ¬ (x = y ∧ y = z) := by
          rintro ⟨rfl, rfl⟩
          exact hs ⟨rfl, rfl, rfl⟩
        simp [D, hs, hdiag]
  let e : H ≃ Fin (q ^ 2) := finProdFinEquiv.trans (finCongr (by ring))
  have he : Equivalent D (diagonal R (q ^ 2)) := by
    apply equivalent_of_reindex e e e
    funext i j k
    simp [reindex, D, diagonal]
  exact hdeg.trans he.1.degenerates

/-- A band of sums selects independent diagonal coordinates of matrix
multiplication. Shifting the sum into `Fin n` permits a full central band,
while the same square-excess weights discard mixed coordinates. -/
theorem matrixMul_degenerates_diagonal_of_sumBand (R : Type*) [CommSemiring R]
    (n t : ℕ) :
    Degenerates (matrixMul R n n n)
      (diagonal R (Fintype.card {p : Fin n × Fin n //
        t ≤ p.1.val + p.2.val ∧ p.1.val + p.2.val < t + n})) := by
  classical
  let H := {p : Fin n × Fin n //
    t ≤ p.1.val + p.2.val ∧ p.1.val + p.2.val < t + n}
  let out (x : H) : Fin n := ⟨x.val.1.val + x.val.2.val - t, by
    have := x.property
    omega⟩
  let D : Tensor R H H H := fun x y z => if x = y ∧ y = z then 1 else 0
  let a (x : H) := (x.val.1.val + x.val.2.val) ^ 2
  let b (y : H) := n ^ 2 + y.val.1.val ^ 2 - y.val.2.val ^ 2
  let c (z : H) := 4 * n ^ 2 - 2 * z.val.1.val * (z.val.1.val + z.val.2.val)
  let S (x y z : H) : Prop := x.val.1.val = z.val.1.val ∧
    x.val.2.val = y.val.2.val ∧
    y.val.1.val + y.val.2.val = z.val.1.val + z.val.2.val
  have hcoeff (x y z : H) :
      matrixMul R n n n (x.val.1, x.val.2) (y.val.2, out y) (z.val.1, out z) =
      if S x y z then 1 else 0 := by
    have hy := y.property.1
    have hz := z.property.1
    simp only [matrixMul, out, Fin.ext_iff]
    congr 1
    dsimp only [S]
    apply propext
    omega
  have hb (y : H) : y.val.2.val ^ 2 ≤ n ^ 2 + y.val.1.val ^ 2 :=
    (Nat.pow_le_pow_left y.val.2.isLt.le 2).trans (Nat.le_add_right _ _)
  have hc (z : H) : 2 * z.val.1.val * (z.val.1.val + z.val.2.val) ≤ 4 * n ^ 2 := by
    calc
      _ ≤ 2 * n * (2 * n) := Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 z.val.1.isLt.le)
        (by have := z.val.1.isLt; have := z.val.2.isLt; omega)
      _ = _ := by ring
  have hdeg : Degenerates (matrixMul R n n n) D := by
    apply degenerates_of_monomial_pullback _ D
      (fun x => (x.val.1, x.val.2)) (fun y => (y.val.2, out y))
      (fun z => (z.val.1, out z)) a b c (5 * n ^ 2)
    · intro x y z hlow
      rw [hcoeff]
      split_ifs with hs
      · obtain ⟨hi, hj, hk⟩ := hs
        have hw := quadratic_weight_lower z.val.1.val y.val.2.val y.val.1.val z.val.2.val n
          (hb y) (hc z) hk
        dsimp only [a, b, c] at hlow
        rw [hi, hj] at hlow
        omega
      · rfl
    · intro x y z
      rw [hcoeff]
      by_cases hs : S x y z
      · obtain ⟨hi, hj, hk⟩ := hs
        have hw := quadratic_weight_eq_iff z.val.1.val y.val.2.val y.val.1.val z.val.2.val n
          (hb y) (hc z) hk
        have heq : a x + b y + c z = 5 * n ^ 2 ↔ x = y ∧ y = z := by
          dsimp only [a, b, c]
          rw [hi, hj, hw]
          constructor
          · intro h
            have hyz : y = z := Subtype.ext
              (Prod.ext (Fin.ext h.symm) (Fin.ext (by omega)))
            have hxy : x = y := Subtype.ext
              (Prod.ext (Fin.ext (by omega)) (Fin.ext hj))
            exact ⟨hxy, hyz⟩
          · rintro ⟨rfl, rfl⟩
            rfl
        simp only [D, ite_eq_left (show S x y z from ⟨hi, hj, hk⟩), heq]
      · have hdiag : ¬ (x = y ∧ y = z) := by
          rintro ⟨rfl, rfl⟩
          exact hs ⟨rfl, rfl, rfl⟩
        simp [D, hs, hdiag]
  let e := Fintype.equivFin H
  have he : Equivalent D (diagonal R (Fintype.card H)) := by
    apply equivalent_of_reindex e e e
    funext i j k
    simp [reindex, D, diagonal]
  exact hdeg.trans he.1.degenerates

/-- A convenient border-subrank consequence of the explicit degeneration. -/
theorem sq_le_borderSubrank_matrixMul_double (K : Type*) [Field K] (q : ℕ) :
    q ^ 2 ≤ borderSubrank (matrixMul K (2 * q) (2 * q) (2 * q)) :=
  le_borderSubrank_of_degenerates_diagonal (matrixMul_degenerates_diagonal_quadratic K q)

end MatrixMultiplication.Tensor
