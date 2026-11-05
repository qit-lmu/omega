module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Words with prescribed symbol counts

A word type fixes the multiplicity of every symbol in a finite alphabet.
Its cardinality is the corresponding multinomial coefficient. Words of the
same type differ only by a permutation of their positions.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication

variable {H : Type*} {N : ℕ}

/-- The number of positions of a word carrying the given symbol. -/
def wordCounts (w : Fin N → H) (h : H) : ℕ := by
  classical
  exact Fintype.card {i // w i = h}

/-- The words of length `N` with multiplicity function `c`. -/
def WordType (N : ℕ) (c : H → ℕ) := {w : Fin N → H // wordCounts w = c}

instance [Fintype H] (N : ℕ) (c : H → ℕ) : Fintype (WordType N c) := by
  classical
  unfold WordType
  infer_instance

/-- The multiplicities of all symbols sum to the word length. -/
theorem wordCounts_sum [Fintype H] (w : Fin N → H) : ∑ h, wordCounts w h = N := by
  classical
  calc
    _ = Fintype.card (Σ h, {i // w i = h}) := Fintype.card_sigma.symm
    _ = Fintype.card (Fin N) := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
    _ = N := Fintype.card_fin N

/-- Permuting positions preserves each symbol count. -/
theorem wordCounts_comp_perm (w : Fin N → H) (p : Equiv.Perm (Fin N)) :
    wordCounts (w ∘ p) = wordCounts w := by
  classical
  funext h
  exact Fintype.card_congr (Equiv.subtypeEquiv p (fun _ => Iff.rfl))

/-- Equal symbol counts give a permutation sending the positions of `w`
to positions carrying the same symbol in `v`. -/
theorem perm_of_wordCounts_eq {w v : Fin N → H} (h : wordCounts w = wordCounts v) :
    ∃ p : Equiv.Perm (Fin N), ∀ i, v (p i) = w i := by
  classical
  let e : ∀ a, {i // w i = a} ≃ {i // v i = a} := fun a =>
    Fintype.equivOfCardEq (congrFun h a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Every nonnegative multiplicity function of total `N` is realized by a word. -/
theorem wordType_nonempty [Fintype H] (c : H → ℕ) (hc : ∑ h, c h = N) :
    Nonempty (WordType N c) := by
  classical
  let e : Fin N ≃ Σ h, Fin (c h) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    exact hc.symm)
  refine ⟨⟨fun i => (e i).1, ?_⟩⟩
  funext h
  change Fintype.card {i // (e i).1 = h} = c h
  calc
    _ = Fintype.card {j : Σ h, Fin (c h) // j.1 = h} :=
      Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
    _ = Fintype.card (Fin (c h)) := Fintype.card_congr (Equiv.sigmaSubtype h)
    _ = c h := Fintype.card_fin _

/-- A prescribed word type is inhabited exactly when its counts sum to `N`. -/
theorem wordType_nonempty_iff [Fintype H] (c : H → ℕ) :
    Nonempty (WordType N c) ↔ ∑ h, c h = N := by
  constructor
  · rintro ⟨⟨w, hw⟩⟩
    rw [← hw]
    exact wordCounts_sum w
  · exact wordType_nonempty c

/-- The number of words with prescribed multiplicities is their multinomial
coefficient. This includes length zero and empty alphabets. -/
theorem card_wordType [Fintype H] (c : H → ℕ) (hc : ∑ h, c h = N) :
    Fintype.card (WordType N c) = Nat.multinomial Finset.univ c := by
  classical
  obtain ⟨⟨w, hw⟩⟩ := wordType_nonempty c hc
  let G := (Equiv.Perm (Fin N))ᵈᵐᵃ
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin N)) DomMulAct.mk
  have hmem : ∀ v : Fin N → H,
      v ∈ MulAction.orbit G w ↔ wordCounts v = c := by
    intro v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      change wordCounts (w ∘ (DomMulAct.mk.symm g : Equiv.Perm (Fin N))) = c
      rw [wordCounts_comp_perm, hw]
    · intro hv
      obtain ⟨p, hp⟩ := perm_of_wordCounts_eq (hv.trans hw.symm)
      refine ⟨DomMulAct.mk p, ?_⟩
      funext i
      exact hp i
  have horbit : Fintype.card (MulAction.orbit G w) = Fintype.card (WordType N c) :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) hmem)
  have hstab : Fintype.card (MulAction.stabilizer G w) = ∏ h, (c h).factorial := by
    calc
      _ = Fintype.card {p : Equiv.Perm (Fin N) // w ∘ p = w} :=
        Fintype.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm
          (fun _ => DomMulAct.mem_stabilizer_iff))
      _ = ∏ h, (wordCounts w h).factorial := DomMulAct.stabilizer_card w
      _ = ∏ h, (c h).factorial := by rw [hw]
  have hgroup : Fintype.card G = N.factorial := by
    rw [Fintype.card_congr (DomMulAct.mk.symm : G ≃ Equiv.Perm (Fin N)),
      Fintype.card_perm, Fintype.card_fin]
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [horbit, hstab, hgroup] at hcard
  have hprod : (∏ h, (c h).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ hprod
  rw [Nat.multinomial_spec, hc]
  exact (mul_comm _ _).trans hcard

end MatrixMultiplication
