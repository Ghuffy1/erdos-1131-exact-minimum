/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.AsymptoticConclusion
import Erdos1131Asymptotic.ChebyshevFirstOrder
import Erdos1131Asymptotic.ChebyshevGram
import Erdos1131Asymptotic.FiniteComparison

/-!
# Erdős Problem 1131

The explicit roots of `T_(N+1) - (1/6) T_(N-1)` have interpolation
functional at most

`2 - 107 / (105 N) + 118 / N²`.

Consequently the scaled defect is eventually at least `106 / 105`, so it
cannot converge to `1`.
-/

namespace Erdos1131Asymptotic

open ChebyshevBound ChebyshevFirstOrder ChebyshevGram FiniteComparison
open Filter

noncomputable section

/-- The complete finite estimate for the explicit admissible Chebyshev
comparison family. -/
theorem functional_chebNodes_le
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    functional (chebNodes (N + 1) hn) ≤
      2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
  let hn : 2 ≤ N + 1 := by omega
  dsimp only
  rw [functional_chebNodes_eq_modelTrace hN]
  exact trace_modelGram_inv_le hN
    (rowBound_chebK N)
    (modelGram_det_isUnit hN)
    (trace_firstOrder_lower_bound hN)

/-- For every sufficiently large index, the explicit nodes certify the
strictly larger first-order defect `106 / 105`. -/
theorem eventual_cheb_comparison :
    ∀ᶠ N : ℕ in atTop,
      ∃ x : Fin (N + 1) ↪ ℝ,
        Admissible x ∧
          (106 : ℝ) / 105 ≤
            ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
  filter_upwards [eventually_ge_atTop 24780] with N hN
  let hn : 2 ≤ N + 1 := by omega
  refine ⟨chebNodes (N + 1) hn, chebNodes_admissible hn, ?_⟩
  apply scaled_comparison_of_functional_le hN
  exact functional_chebNodes_le (by omega)

/-- A stronger eventual lower bound on the scaled extremal defect. -/
theorem eventually_scaledDefect_ge :
    ∀ᶠ N : ℕ in atTop, (106 : ℝ) / 105 ≤ scaledDefect N := by
  filter_upwards [eventual_cheb_comparison] with N hN
  obtain ⟨x, hx, hcomparison⟩ := hN
  exact scaledDefect_ge_of_comparison x hx hcomparison

/-- Erdős Problem 1131, as stated, is false. -/
theorem not_erdos_1131 :
    ¬ Tendsto scaledDefect atTop (nhds 1) :=
  not_erdos_1131_of_eventual_comparison eventual_cheb_comparison

end

end Erdos1131Asymptotic
