module

public import Omega.Analysis.SharpSubrankSize
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# The central band in a square grid

The integer pairs in an `n` by `n` square whose coordinate sum belongs to
the middle `n` diagonals. Its complement consists of two triangular corners.
-/

@[expose] public section

namespace MatrixMultiplication

/-- The middle `n` diagonals of the `n` by `n` grid. -/
def centralBand (n : ℕ) :=
  {p : Fin n × Fin n // n / 2 ≤ p.1.val + p.2.val ∧
    p.1.val + p.2.val < n / 2 + n}

instance (n : ℕ) : Fintype (centralBand n) := by
  unfold centralBand
  infer_instance

private theorem twice_card_lowerTriangle (n m : ℕ) (hm : m ≤ n) :
    2 * Fintype.card {p : Fin n × Fin n // p.1.val + p.2.val < m} =
      m * (m + 1) := by
  let e : {p : Fin n × Fin n // p.1.val + p.2.val < m} ≃
      (Σ s : Fin m, Fin (s.val + 1)) := {
    toFun := fun p => ⟨⟨p.val.1.val + p.val.2.val, p.property⟩,
      ⟨p.val.1.val, by dsimp; omega⟩⟩
    invFun := fun s => ⟨(⟨s.2.val, by have h := s.1.isLt; have h' := s.2.isLt; omega⟩,
      ⟨s.1.val - s.2.val, by have h := s.1.isLt; omega⟩), by
        have h := s.1.isLt
        have h' := s.2.isLt
        dsimp
        omega⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp
      omega
    right_inv := by
      rintro ⟨⟨s, hs⟩, ⟨i, hi⟩⟩
      dsimp
      dsimp at hi
      have hsum : i + (s - i) = s := by omega
      apply Sigma.ext (Fin.ext hsum)
      exact (Fin.heq_ext_iff (congrArg (· + 1) hsum)).mpr rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) m]
  have h := Finset.sum_range_id_mul_two (m + 1)
  rw [Finset.sum_range_succ'] at h
  simpa only [add_zero, Nat.add_sub_cancel, Nat.mul_comm] using h

/-- The central band is obtained by deleting the two triangular corners. -/
theorem card_centralBand_eq_sub (n : ℕ) :
    Fintype.card (centralBand n) = n ^ 2 - (n / 2) * ((n + 1) / 2) := by
  classical
  let low : Fin n × Fin n → Prop := fun p => p.1.val + p.2.val < n / 2
  let high : Fin n × Fin n → Prop := fun p => n / 2 + n ≤ p.1.val + p.2.val
  have hdisjoint : Disjoint low high := by
    rw [Pi.disjoint_iff]
    intro p
    apply disjoint_iff_inf_le.mpr
    rintro ⟨hp, hq⟩
    dsimp [low, high] at hp hq
    omega
  have hcorners := Fintype.card_subtype_or_disjoint low high hdisjoint
  have hband : Fintype.card (centralBand n) =
      n ^ 2 - (Fintype.card {p // low p} + Fintype.card {p // high p}) := by
    calc
      _ = Fintype.card {p : Fin n × Fin n // ¬(low p ∨ high p)} :=
        Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (by
          intro p
          dsimp [low, high]
          omega))
      _ = _ := by rw [Fintype.card_subtype_compl, hcorners]; simp [pow_two]
  rw [hband]
  congr 1
  have hlo := twice_card_lowerTriangle n (n / 2) (Nat.div_le_self _ _)
  have hhi : Fintype.card {p // high p} =
      Fintype.card {p : Fin n × Fin n // p.1.val + p.2.val < n - n / 2 - 1} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (Equiv.prodCongr Fin.revPerm Fin.revPerm)
    intro p
    have hi := p.1.isLt
    have hj := p.2.isLt
    change n / 2 + n ≤ p.1.val + p.2.val ↔
      (Fin.rev p.1).val + (Fin.rev p.2).val < n - n / 2 - 1
    simp only [Fin.val_rev]
    omega
  rw [hhi]
  have hhi' := twice_card_lowerTriangle n (n - n / 2 - 1) (by omega)
  change 2 * Fintype.card {p // low p} = (n / 2) * (n / 2 + 1) at hlo
  have hparity : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hparity with hn | hn
  · have hc : (n + 1) / 2 = n / 2 := by omega
    rw [hc]
    by_cases hz : n = 0
    · subst n
      simp [low]
    · have ht : n - n / 2 - 1 + 1 = n / 2 := by omega
      nlinarith
  · have hc : (n + 1) / 2 = n / 2 + 1 := by omega
    have ht : n - n / 2 - 1 = n / 2 := by omega
    rw [hc]
    rw [ht]
    rw [ht] at hhi'
    nlinarith

/-- The central band has the sharp diagonal size for matrix multiplication. -/
@[simp]
theorem card_centralBand (n : ℕ) :
    Fintype.card (centralBand n) = (3 * n ^ 2 + 3) / 4 := by
  rw [card_centralBand_eq_sub, square_sub_half_mul_half_eq_sharpSubrankSize]

end MatrixMultiplication
