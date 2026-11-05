module

public import Omega.Tensor.DegenerationOperations
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-!+# Rational functions and polynomial degeneration witnesses

The rational factor maps may have poles at zero. Only their tensor output is
required to be regular there. For finite tensors this definition agrees with
the polynomial leading-coefficient witnesses used throughout the project.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

open Polynomial

variable {K : Type*} [Field K]
variable {I J L I' J' L' : Type*}

/-- Extend the coefficients of a tensor to the rational function field. -/
def liftRational (T : Tensor K I J L) : Tensor (RatFunc K) I J L :=
  fun i j k => algebraMap K (RatFunc K) (T i j k)

/-- A rational function is regular at zero and takes the specified value there.
The denominator here is the reduced denominator, so removable poles are allowed. -/
def RegularAtZeroValue (f : RatFunc K) (s : K) : Prop :=
  f.denom.eval 0 ≠ 0 ∧ RatFunc.eval (RingHom.id K) 0 f = s

/-- Rational factor maps whose output is regular at zero with value `S`.
No regularity condition is imposed on the individual factor maps. -/
def RationalDegenerates [Fintype I] [Fintype J] [Fintype L]
    (T : Tensor K I J L) (S : Tensor K I' J' L') : Prop :=
  ∃ A : Matrix I' I (RatFunc K), ∃ B : Matrix J' J (RatFunc K),
    ∃ D : Matrix L' L (RatFunc K),
      ∀ i j k, RegularAtZeroValue (map A B D (liftRational T) i j k) (S i j k)

@[simp]
theorem regularAtZeroValue_algebraMap (p : K[X]) (s : K) :
    RegularAtZeroValue (algebraMap K[X] (RatFunc K) p) s ↔ p.eval 0 = s := by
  simp [RegularAtZeroValue, ← Polynomial.coeff_zero_eq_eval_zero]

private theorem exists_polynomial_denominator {α : Type*} [Fintype α]
    (f : α → RatFunc K) :
    ∃ q : K[X], q ≠ 0 ∧
      (∀ i, (f i).denom ∣ q) ∧
      ∃ p : α → K[X], ∀ i,
        algebraMap K[X] (RatFunc K) (p i) =
          algebraMap K[X] (RatFunc K) q * f i := by
  classical
  let q : K[X] := ∏ i, (f i).denom
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => RatFunc.denom_ne_zero _
  have hd : ∀ i, (f i).denom ∣ q := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hp : ∀ i, ∃ p : K[X],
      algebraMap K[X] (RatFunc K) p = algebraMap K[X] (RatFunc K) q * f i := by
    intro i
    obtain ⟨p, hp⟩ := (RatFunc.denom_dvd hq).mp (hd i)
    refine ⟨p, ?_⟩
    rw [eq_div_iff (RatFunc.algebraMap_ne_zero hq)] at hp
    exact hp.symm.trans (mul_comm _ _)
  choose p hp using hp
  exact ⟨q, hq, hd, p, hp⟩

private theorem exists_regular_polynomial_denominator {α : Type*} [Fintype α]
    (f : α → RatFunc K) (s : α → K)
    (hf : ∀ i, RegularAtZeroValue (f i) (s i)) :
    ∃ q : K[X], q.eval 0 ≠ 0 ∧ ∃ p : α → K[X],
      (∀ i, algebraMap K[X] (RatFunc K) (p i) =
        algebraMap K[X] (RatFunc K) q * f i) ∧
      ∀ i, (p i).eval 0 = q.eval 0 * s i := by
  classical
  let q : K[X] := ∏ i, (f i).denom
  have hq0 : q.eval 0 ≠ 0 := by
    simp only [q, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hf i).1
  have hq : q ≠ 0 := by intro h; simp [h] at hq0
  have hp : ∀ i, ∃ p : K[X],
      algebraMap K[X] (RatFunc K) p = algebraMap K[X] (RatFunc K) q * f i := by
    intro i
    obtain ⟨p, hp⟩ := (RatFunc.denom_dvd hq).mp
      (Finset.dvd_prod_of_mem (fun i => (f i).denom) (Finset.mem_univ i))
    refine ⟨p, ?_⟩
    rw [eq_div_iff (RatFunc.algebraMap_ne_zero hq)] at hp
    exact hp.symm.trans (mul_comm _ _)
  choose p hp using hp
  refine ⟨q, hq0, p, hp, ?_⟩
  intro i
  have he := congrArg (RatFunc.eval (RingHom.id K) 0) (hp i)
  rw [RatFunc.eval_mul (RingHom.id K) 0 (by simp)
    (by simpa only [Polynomial.eval₂_id] using (hf i).1)] at he
  simpa [← Polynomial.coeff_zero_eq_eval_zero, (hf i).2] using he

private theorem exists_X_pow_factor (p : K[X]) (hp : p ≠ 0) :
    ∃ d : ℕ, ∃ u : K[X], u.eval 0 ≠ 0 ∧ p = X ^ d * u := by
  obtain ⟨u, hu⟩ := (Polynomial.X_pow_dvd_iff).mpr
    (fun n (hn : n < p.natTrailingDegree) => coeff_eq_zero_of_lt_natTrailingDegree hn)
  refine ⟨p.natTrailingDegree, u, ?_, hu⟩
  have hc := (coeff_natTrailingDegree_ne_zero).mpr hp
  have he := congrArg (fun v : K[X] => v.coeff p.natTrailingDegree) hu
  rw [he] at hc
  simpa [← Polynomial.coeff_zero_eq_eval_zero, coeff_X_pow_mul'] using hc

private theorem map_scale_factors {R : Type*} [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (D : Matrix L' L R)
    (a b c : R) (T : Tensor R I J L) :
    map (fun i j => a * A i j) (fun i j => b * B i j)
      (fun i j => c * D i j) T = fun i j k => (a * b * c) * map A B D T i j k := by
  funext i j k
  simp only [map, Finset.mul_sum, mul_left_comm, mul_comm]

private theorem liftRational_eq_liftPolynomial (T : Tensor K I J L) :
    liftRational T = fun i j k =>
      algebraMap K[X] (RatFunc K) (liftPolynomial T i j k) := by
  funext i j k
  simp [liftRational, liftPolynomial]

/-- Divide one polynomial factor map by its leading parameter power.
The resulting rational output is a polynomial with constant term `S`. -/
theorem Degenerates.rationalDegenerates
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Degenerates T S) : RationalDegenerates T S := by
  obtain ⟨w⟩ := h
  let φ := algebraMap K[X] (RatFunc K)
  have hx : φ (X ^ w.order) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  refine ⟨fun i j => (φ (X ^ w.order))⁻¹ * φ (w.firstMap i j),
    w.secondMap.map φ, w.thirdMap.map φ, ?_⟩
  intro i j k
  have hm := congrFun (congrFun (congrFun
    (map_ringHom φ w.firstMap w.secondMap w.thirdMap (liftPolynomial T)) i) j) k
  rw [← liftRational_eq_liftPolynomial] at hm
  change φ (map w.firstMap w.secondMap w.thirdMap (liftPolynomial T) i j k) = _ at hm
  have he : map (fun i j => (φ (X ^ w.order))⁻¹ * φ (w.firstMap i j))
      (w.secondMap.map φ) (w.thirdMap.map φ) (liftRational T) i j k =
      φ (C (S i j k) + X * w.remainder i j k) := by
    change map (fun i j => (φ (X ^ w.order))⁻¹ * (w.firstMap.map φ) i j)
      (w.secondMap.map φ) (w.thirdMap.map φ) (liftRational T) i j k = _
    rw [map_scale_first]
    dsimp only
    rw [← hm, w.equation]
    rw [pow_succ]
    simp only [_root_.map_add, _root_.map_mul]
    field_simp
  rw [he, regularAtZeroValue_algebraMap]
  simp

/-- Clear the finitely many rational denominators and remove the common power
of the parameter. The remaining nonzero constant is absorbed into one map. -/
theorem RationalDegenerates.degenerates
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : RationalDegenerates T S) : Degenerates T S := by
  obtain ⟨A, B, D, h⟩ := h
  let φ := algebraMap K[X] (RatFunc K)
  obtain ⟨da, hda, _, pa, hpa⟩ := exists_polynomial_denominator
    (fun ij : I' × I => A ij.1 ij.2)
  obtain ⟨db, hdb, _, pb, hpb⟩ := exists_polynomial_denominator
    (fun ij : J' × J => B ij.1 ij.2)
  obtain ⟨dc, hdc, _, pc, hpc⟩ := exists_polynomial_denominator
    (fun ij : L' × L => D ij.1 ij.2)
  let Ap : Matrix I' I K[X] := fun i j => pa (i, j)
  let Bp : Matrix J' J K[X] := fun i j => pb (i, j)
  let Dp : Matrix L' L K[X] := fun i j => pc (i, j)
  let P := map Ap Bp Dp (liftPolynomial T)
  let F := map A B D (liftRational T)
  have ha : Ap.map φ = fun i j => φ da * A i j := by
    funext i j; exact hpa (i, j)
  have hb : Bp.map φ = fun i j => φ db * B i j := by
    funext i j; exact hpb (i, j)
  have hc : Dp.map φ = fun i j => φ dc * D i j := by
    funext i j; exact hpc (i, j)
  have hP : ∀ i j k, φ (P i j k) = φ (da * db * dc) * F i j k := by
    have hm := map_ringHom φ Ap Bp Dp (liftPolynomial T)
    rw [← liftRational_eq_liftPolynomial, ha, hb, hc, map_scale_factors] at hm
    intro i j k
    simpa only [P, F, _root_.map_mul] using congrFun (congrFun (congrFun hm i) j) k
  obtain ⟨q, hq, p, hp, hp0⟩ := exists_regular_polynomial_denominator
    (fun ijk : I' × J' × L' => F ijk.1 ijk.2.1 ijk.2.2)
    (fun ijk : I' × J' × L' => S ijk.1 ijk.2.1 ijk.2.2)
    (fun ijk => h ijk.1 ijk.2.1 ijk.2.2)
  have hpoly : ∀ i j k, q * P i j k = (da * db * dc) * p (i, j, k) := by
    intro i j k
    apply RatFunc.algebraMap_injective K
    change φ _ = φ _
    rw [_root_.map_mul, _root_.map_mul, hP, hp]
    ring
  obtain ⟨d, u, hu, hdu⟩ := exists_X_pow_factor (da * db * dc)
    (mul_ne_zero (mul_ne_zero hda hdb) hdc)
  let c := u.eval 0 * q.eval 0
  have hc0 : c ≠ 0 := mul_ne_zero hu hq
  let V : Tensor K[X] I' J' L' := fun i j k => C c⁻¹ * (u * p (i, j, k))
  have hV : ∀ i j k, (V i j k).coeff 0 = S i j k := by
    intro i j k
    rw [coeff_zero_eq_eval_zero]
    simp only [V, Polynomial.eval_mul, Polynomial.eval_C, hp0]
    simpa only [c, mul_assoc] using inv_mul_cancel_left₀ hc0 (S i j k)
  have hm : map (fun i j => C c⁻¹ * (q * Ap i j)) Bp Dp (liftPolynomial T) =
      fun i j k => X ^ d * V i j k := by
    rw [map_scale_first (fun i j => q * Ap i j) Bp Dp (C c⁻¹) (liftPolynomial T)]
    funext i j k
    rw [map_scale_first Ap Bp Dp q (liftPolynomial T)]
    change C c⁻¹ * (q * P i j k) = _
    rw [hpoly, hdu]
    dsimp only [V]
    ring
  refine ⟨{
    order := d
    firstMap := fun i j => C c⁻¹ * (q * Ap i j)
    secondMap := Bp
    thirdMap := Dp
    remainder := fun i j k => (V i j k).divX
    equation := ?_
  }⟩
  intro i j k
  rw [hm]
  have hv : V i j k = C (S i j k) + X * (V i j k).divX := by
    rw [← hV]
    exact (X_mul_divX_add (V i j k)).symm.trans (add_comm _ _)
  change X ^ d * V i j k = _
  conv_lhs => rw [hv]
  rw [pow_succ]
  ring

/-- The manuscript's rational-function definition and polynomial witnesses
describe the same degeneration relation over every field. -/
theorem rationalDegenerates_iff_degenerates
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    (T : Tensor K I J L) (S : Tensor K I' J' L') :
    RationalDegenerates T S ↔ Degenerates T S :=
  ⟨RationalDegenerates.degenerates, Degenerates.rationalDegenerates⟩

/-- A restriction over the rational function field between constant tensors
specializes to a degeneration over the base field. Only the output must be
regular at zero; the individual factor maps may have poles. -/
theorem degenerates_of_restricts_liftRational
    [Fintype I] [Fintype J] [Fintype L]
    [Fintype I'] [Fintype J'] [Fintype L']
    {T : Tensor K I J L} {S : Tensor K I' J' L'}
    (h : Restricts (liftRational T) (liftRational S)) : Degenerates T S := by
  apply RationalDegenerates.degenerates
  obtain ⟨A, B, D, h⟩ := h
  refine ⟨A, B, D, ?_⟩
  intro i j k
  rw [h]
  simp [liftRational, RegularAtZeroValue]

end MatrixMultiplication.Tensor
