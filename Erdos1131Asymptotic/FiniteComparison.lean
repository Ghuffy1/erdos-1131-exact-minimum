/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.ChebyshevResolvent

/-!
# The finite comparison inequality

The root and interpolation calculations reduce the analytic functional to the
trace of the inverse of `modelGram`.  This file combines the exact resolvent
identity with the three scalar estimates used in the final disproof.
-/

namespace Erdos1131Asymptotic.FiniteComparison

open ChebyshevBound ChebyshevResolvent

noncomputable section

theorem trace_modelGram_inv_decomposition
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    Matrix.trace (chebH N * (modelGram N)⁻¹) =
      (2 / (N : ℝ)) *
          Matrix.trace (chebH N * chebDInv N) -
        (4 / (N : ℝ) ^ 2) *
          Matrix.trace
            (chebH N * (chebDInv N * chebK N * chebDInv N)) +
        Matrix.trace (chebH N * chebInverseRemainder N) := by
  rw [inv_modelGram_second_order hN hunit]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- Once the bounded first-order trace has its elementary lower bound, the
comparison trace has the explicit estimate needed by the disproof. -/
theorem trace_modelGram_inv_le
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (modelGram N).det)
    (hfirstOrder :
      (13 : ℝ) * N / 30 - 13 ≤
        Matrix.trace
          (chebH N * (chebDInv N * chebK N * chebDInv N))) :
    Matrix.trace (chebH N * (modelGram N)⁻¹) ≤
      2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hA := trace_chebH_mul_chebDInv_le hNpos
  have hunitY := isUnit_one_add_chebY_of_modelGram hNpos hunit
  have hE := abs_trace_chebH_inverseRemainder_le hN hK hunitY
  have hE' :
      Matrix.trace (chebH N * chebInverseRemainder N) ≤
        64 / (N : ℝ) ^ 2 :=
    (le_abs_self _).trans hE
  rw [trace_modelGram_inv_decomposition hNpos hunit]
  calc
    (2 / (N : ℝ)) *
          Matrix.trace (chebH N * chebDInv N) -
        (4 / (N : ℝ) ^ 2) *
          Matrix.trace
            (chebH N * (chebDInv N * chebK N * chebDInv N)) +
        Matrix.trace (chebH N * chebInverseRemainder N)
        ≤ (2 / (N : ℝ)) *
              ((N : ℝ) + 5 / 14 + 1 / N) -
            (4 / (N : ℝ) ^ 2) *
              ((13 : ℝ) * N / 30 - 13) +
            64 / (N : ℝ) ^ 2 := by
      have htwo : 0 ≤ (2 : ℝ) / N := by positivity
      have hfour : 0 ≤ (4 : ℝ) / N ^ 2 := by positivity
      gcongr
    _ = 2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
      field_simp
      ring

end

end Erdos1131Asymptotic.FiniteComparison
