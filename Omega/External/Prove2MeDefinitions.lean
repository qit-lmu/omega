module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Lattice.Nat

/-!
# Prove2Me matrix-multiplication statement definitions

Downloaded from the public `mme_omega` definition on 2026-11-02.
The original is preserved in `material/prove2me/Def_mme_omega.lean`, with
source URLs and hashes in `material/prove2me/provenance.json`. Only the
Lean module visibility wrapper and renamed mathlib import paths differ;
the definitions are unchanged.
-/

@[expose] public section

universe u

open PiTensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K]

/-! ## Mode spaces for `MM(n,m,p)`

The three mode spaces for the matrix-multiplication tensor are
`Fin n × Fin m → K`, `Fin m × Fin p → K`, `Fin p × Fin n → K`. -/

@[reducible] def MMSpace (K : Type u) (n m p : ℕ) : Fin 3 → Type u
  | ⟨0, _⟩ => Fin n × Fin m → K
  | ⟨1, _⟩ => Fin m × Fin p → K
  | ⟨2, _⟩ => Fin p × Fin n → K

@[reducible] instance MMSpace_addCommGroup (n m p : ℕ) (i : Fin 3) :
    AddCommGroup (MMSpace K n m p i) :=
  match i with
  | ⟨0, _⟩ => Pi.addCommGroup
  | ⟨1, _⟩ => Pi.addCommGroup
  | ⟨2, _⟩ => Pi.addCommGroup

@[reducible] instance MMSpace_module (n m p : ℕ) (i : Fin 3) :
    Module K (MMSpace K n m p i) :=
  match i with
  | ⟨0, _⟩ => Pi.module _ _ _
  | ⟨1, _⟩ => Pi.module _ _ _
  | ⟨2, _⟩ => Pi.module _ _ _

/-! ## The matrix-multiplication tensor

`MMTensor n m p = ∑_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}`. -/

noncomputable def MMTensor (K : Type u) [Field K] (n m p : ℕ) :
    PiTensorProduct K (MMSpace K n m p) :=
  ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
    tprod K (fun s =>
      match s with
      | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
      | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
      | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

/-! ## Textbook tensor rank

`tensorRank T` is the smallest `r` such that `T` can be written as a sum of
`r` pure tensors `u_1 ⊗ … ⊗ u_d`. For `T = 0` we have `tensorRank T = 0`
(empty decomposition). -/

noncomputable def tensorRank
    {d : ℕ} {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : PiTensorProduct K V) : ℕ :=
  sInf { r | ∃ f : Fin r → ∀ i, V i, T = ∑ j, tprod K (f j) }

/-! ## The matrix-multiplication exponent ω

`ω = inf_{n ≥ 2} log(tensorRank (MMTensor n n n)) / log n`.

Here `tensorRank` is the standard tensor rank `R(T)` (Wigderson–Zuiddam,
footnote 10: "the smallest number of rank-1 tensors which add up to `T`").
The `else 3` branch handles `n ≤ 1` where the formula is ill-defined; the
choice of `3` is the trivial naive-algorithm upper bound and does not affect
the infimum. -/

noncomputable def matMulExp (K : Type u) [Field K] : ℝ :=
  iInf (fun n : ℕ =>
    if 1 < n then
      Real.log (tensorRank (MMTensor K n n n) : ℝ) / Real.log n
    else 3)

end MME
