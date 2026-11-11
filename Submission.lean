import CompleteSolution
import Erdos1131Asymptotic.Main

/-!
# Complete statement for Erdős Problem 1131

The exact-minimum construction is this project's new contribution. The
asymptotic disproof is the previously published result of seanm27lol, included
with attribution and checked here against the same original functional.
-/

open Filter
open scoped Topology

namespace Erdos1131Submission

theorem energy_eq_reference_functional {n : ℕ} (nodes : Fin n ↪ ℝ) :
    Erdos1131.energy (nodes : Fin n → ℝ) =
      Erdos1131Asymptotic.functional nodes := rfl

theorem attainable_values_eq_reference (n : ℕ) :
    {v : ℝ | ∃ nodes : Fin n → ℝ,
      Erdos1131.Admissible nodes ∧ Erdos1131.energy nodes = v} =
      Erdos1131Asymptotic.values n := by
  ext v
  change (∃ nodes : Fin n → ℝ,
    Erdos1131.Admissible nodes ∧ Erdos1131.energy nodes = v) ↔
    ∃ nodes : Fin n ↪ ℝ,
      Erdos1131Asymptotic.Admissible nodes ∧ Erdos1131Asymptotic.functional nodes = v
  constructor
  · rintro ⟨nodes, hnodes, hvalue⟩
    exact ⟨⟨nodes, hnodes.1⟩, hnodes.2, hvalue⟩
  · rintro ⟨nodes, hnodes, hvalue⟩
    exact ⟨nodes, ⟨nodes.injective, hnodes⟩, hvalue⟩

theorem minimum_eq_reference (n : ℕ) :
    Erdos1131.minimum n = Erdos1131Asymptotic.M n := by
  unfold Erdos1131.minimum Erdos1131Asymptotic.M
  rw [attainable_values_eq_reference]

noncomputable def scaledDefect (n : ℕ) : ℝ :=
  (n : ℝ) * (2 - Erdos1131.minimum n)

theorem shifted_scaledDefect_eq_reference :
    (fun n : ℕ => scaledDefect (n + 1)) = Erdos1131Asymptotic.scaledDefect := by
  funext n
  simp only [scaledDefect, Erdos1131Asymptotic.scaledDefect, minimum_eq_reference]

theorem asymptotic_coefficient_one_false :
    ¬ Tendsto scaledDefect atTop (nhds 1) := by
  intro hlimit
  have hshift : Tendsto (fun n : ℕ => scaledDefect (n + 1)) atTop (nhds 1) :=
    hlimit.comp (tendsto_add_atTop_nat 1)
  rw [shifted_scaledDefect_eq_reference] at hshift
  exact Erdos1131Asymptotic.not_erdos_1131 hshift

theorem complete_problem :
    (∀ (n : ℕ) (hn : 0 < n),
      ∃ nodes : Fin n → ℝ,
        Erdos1131.Admissible nodes ∧
        Erdos1131.energy nodes = Erdos1131.algebraicMinimum n hn ∧
        ∀ other : Fin n → ℝ, Erdos1131.Admissible other →
          Erdos1131.algebraicMinimum n hn ≤ Erdos1131.energy other) ∧
      ¬ Tendsto scaledDefect atTop (nhds 1) :=
  ⟨Erdos1131.erdos1131_solution, asymptotic_coefficient_one_false⟩

end Erdos1131Submission

#print axioms Erdos1131Submission.minimum_eq_reference
#print axioms Erdos1131Submission.asymptotic_coefficient_one_false
#print axioms Erdos1131Submission.complete_problem
