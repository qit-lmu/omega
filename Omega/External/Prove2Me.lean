module

public import Omega.External.Prove2MeTensor
public import Omega.ExponentInfimum
public import Omega.Main
import Mathlib.Tactic.NormNum

/-!
# The Prove2Me matrix-multiplication statement as a corollary

The target is the exact public statement `mme_omega_le_225`, using the
downloaded `MME.matMulExp` definition. Its source and preamble are archived
in `material/prove2me/`; no proof from that platform is imported.

The equality of exponents identifies both the tensor-rank representation and
the infimum convention. The final theorem then applies our manuscript result.
-/

@[expose] public section

namespace MME

/-- Prove2Me's ordinary-rank exponent equals the manuscript's asymptotic-rank
exponent, including the fallback value at matrix sizes zero and one. -/
theorem matMulExp_eq_omega (K : Type*) [Field K] :
    matMulExp K = MatrixMultiplication.omega K := by
  unfold matMulExp
  convert MatrixMultiplication.iInf_log_rank_matrixMul_eq_omega K using 1
  apply iInf_congr
  intro n
  rw [tensorRank_MMTensor_eq_rank]
  have hn : (1 < n) = (2 ≤ n) := propext (by omega)
  simp only [hn]

end MME

universe u

open MME

/-- The exact Prove2Me target, proved from our all-fields main theorem. -/
theorem mme_omega_le_225 {K : Type u} [Field K] :
    matMulExp K ≤ (2.25 : ℝ) := by
  rw [matMulExp_eq_omega]
  convert MatrixMultiplication.omega_le_nine_quarters K using 1
  norm_num
