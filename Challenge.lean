import Submission

/-!
# Original-source correspondence check

The cardinal product, ordinary integral, arbitrary distinct nodes, and infimum
are written directly from the original problem. The bridges below compare
these independent definitions with the submitted proof.
-/

open Filter
open scoped BigOperators Topology

namespace OriginalProblem1131

def admissible {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧ ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1

noncomputable def cardinal {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t - nodes j) / (nodes i - nodes j)

noncomputable def integral {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, ∑ i : Fin n, cardinal nodes i t ^ 2

noncomputable def infimum (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ, admissible nodes ∧ integral nodes = v}

theorem admissible_eq {n : ℕ} (nodes : Fin n → ℝ) :
    admissible nodes = Erdos1131.Admissible nodes := rfl

theorem integral_eq {n : ℕ} (nodes : Fin n → ℝ) :
    integral nodes = Erdos1131.energy nodes := by
  simp only [integral, Erdos1131.energy, Erdos1131.squareSum,
    Erdos1131.cardinal_eq_product, cardinal]

theorem infimum_eq (n : ℕ) : infimum n = Erdos1131.minimum n := by
  simp only [infimum, Erdos1131.minimum, admissible_eq, integral_eq]

theorem exact_original (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ,
      admissible nodes ∧ integral nodes = Erdos1131.algebraicMinimum n hn ∧
      ∀ other : Fin n → ℝ, admissible other →
        Erdos1131.algebraicMinimum n hn ≤ integral other := by
  simpa only [admissible_eq, integral_eq] using Erdos1131.erdos1131_solution n hn

theorem asymptotic_original :
    ¬ Tendsto (fun n : ℕ => (n : ℝ) * (2 - infimum n)) atTop (nhds 1) := by
  simp only [infimum_eq]
  exact Erdos1131Submission.asymptotic_coefficient_one_false

theorem full_original_problem :
    (∀ (n : ℕ) (hn : 0 < n),
      ∃ nodes : Fin n → ℝ,
        admissible nodes ∧ integral nodes = Erdos1131.algebraicMinimum n hn ∧
        ∀ other : Fin n → ℝ, admissible other →
          Erdos1131.algebraicMinimum n hn ≤ integral other) ∧
      ¬ Tendsto (fun n : ℕ => (n : ℝ) * (2 - infimum n)) atTop (nhds 1) :=
  ⟨exact_original, asymptotic_original⟩

end OriginalProblem1131

#print axioms OriginalProblem1131.integral_eq
#print axioms OriginalProblem1131.infimum_eq
#print axioms OriginalProblem1131.full_original_problem
