/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.Definitions

/-!
# From an explicit comparison family to the disproof

This file contains no asymptotic orthogonal-polynomial input.  It isolates the
order-theoretic step saying that an eventual admissible comparison family with
scaled defect at least `106 / 105` rules out convergence to `1`.
-/

open Filter Set

namespace Erdos1131Asymptotic

theorem scaledDefect_ge_of_comparison
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ) (hx : Admissible x)
    (hcomparison :
      (106 : ℝ) / 105 ≤
        ((N + 1 : ℕ) : ℝ) * (2 - functional x)) :
    (106 : ℝ) / 105 ≤ scaledDefect N := by
  rw [scaledDefect]
  calc
    (106 : ℝ) / 105
        ≤ ((N + 1 : ℕ) : ℝ) * (2 - functional x) := hcomparison
    _ ≤ ((N + 1 : ℕ) : ℝ) * (2 - M (N + 1)) := by
      gcongr
      exact M_le_functional x hx

theorem not_erdos_1131_of_eventual_comparison
    (hcomparison :
      ∀ᶠ N : ℕ in atTop,
        ∃ x : Fin (N + 1) ↪ ℝ,
          Admissible x ∧
            (106 : ℝ) / 105 ≤
              ((N + 1 : ℕ) : ℝ) * (2 - functional x)) :
    ¬ Tendsto scaledDefect atTop (nhds 1) := by
  intro hlimit
  have hupper : ∀ᶠ N : ℕ in atTop, scaledDefect N < (211 : ℝ) / 210 :=
    (tendsto_order.1 hlimit).2 _ (by norm_num)
  rw [eventually_atTop] at hcomparison hupper
  obtain ⟨N₁, hcomparison⟩ := hcomparison
  obtain ⟨N₂, hupper⟩ := hupper
  let N := max N₁ N₂
  have hN := hcomparison N (le_max_left _ _)
  have hNupper := hupper N (le_max_right _ _)
  obtain ⟨x, hx, hscaled⟩ := hN
  have hlower := scaledDefect_ge_of_comparison x hx hscaled
  norm_num at hlower hNupper
  linarith

end Erdos1131Asymptotic
