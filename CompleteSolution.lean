import RootSelection
import MinimumAttainment

/-! The full exact-minimum conclusion for every positive number of nodes. -/

noncomputable section

namespace Erdos1131

/-- The root-selection formula is achieved and bounds every admissible configuration. -/
theorem erdos1131_solution (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ,
      Admissible nodes ∧
      energy nodes = algebraicMinimum n hn ∧
      ∀ other : Fin n → ℝ, Admissible other → algebraicMinimum n hn ≤ energy other := by
  obtain ⟨nodes, hnodes, henergy⟩ := minimum_attained n hn
  refine ⟨nodes, hnodes, henergy.trans (algebraicMinimum_eq_minimum n hn).symm, ?_⟩
  intro other hother
  rw [algebraicMinimum_eq_minimum n hn]
  exact minimum_le_energy hother

end Erdos1131
