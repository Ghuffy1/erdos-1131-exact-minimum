/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.DisproofBridge

/-!
# The explicit finite estimate implies the asymptotic contradiction

This file isolates the final elementary calculation.  The analytic and matrix
parts of the proof only need to supply the displayed upper bound on the
functional of an admissible comparison family.
-/

namespace Erdos1131Asymptotic

theorem scaled_comparison_of_functional_le
    {N : ℕ} (hN : 24780 ≤ N) (x : Fin (N + 1) ↪ ℝ)
    (hfunctional :
      functional x ≤
        2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2) :
    (106 : ℝ) / 105 ≤
      ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNrLarge : (24780 : ℝ) ≤ N := by exact_mod_cast hN
  have hdefect :
      107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2 ≤
        2 - functional x := by
    linarith
  have harithmetic :
      (106 : ℝ) / 105 ≤
        ((N + 1 : ℕ) : ℝ) *
          (107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2) := by
    rw [show (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 by norm_num]
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hNrLarge) (le_of_lt hNr)]
  calc
    (106 : ℝ) / 105
        ≤ ((N + 1 : ℕ) : ℝ) *
            (107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2) :=
      harithmetic
    _ ≤ ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
      gcongr

end Erdos1131Asymptotic
