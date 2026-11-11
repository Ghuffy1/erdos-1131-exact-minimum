import PolynomialEnergy
import Fekete

/-! A closed coefficient-and-node description of admissible interpolation. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

abbrev InterpolationState (n : ℕ) := (Fin n → ℝ) × (Fin n → Fin n → ℝ)

def ValidInterpolationState {n : ℕ} (z : InterpolationState n) : Prop :=
  z.fst ∈ nodeBox n ∧ ∀ i j,
    (coefficientPolynomial (z.snd i)).eval (z.fst j) = if i = j then 1 else 0

theorem continuous_state_evaluation (n : ℕ) (i j : Fin n) :
    Continuous (fun z : InterpolationState n =>
      (coefficientPolynomial (z.snd i)).eval (z.fst j)) := by
  have hpair : Continuous (fun z : InterpolationState n => (z.snd i, z.fst j)) :=
    (((continuous_apply i).comp continuous_snd).prodMk
      ((continuous_apply j).comp continuous_fst))
  exact (continuous_coefficientPolynomial_eval n).comp hpair

theorem validInterpolationState_closed (n : ℕ) :
    IsClosed {z : InterpolationState n | ValidInterpolationState z} := by
  have hset : {z : InterpolationState n | ValidInterpolationState z} =
      (Prod.fst ⁻¹' nodeBox n) ∩ ⋂ i : Fin n, ⋂ j : Fin n, {z : InterpolationState n |
        (coefficientPolynomial (z.snd i)).eval (z.fst j) = if i = j then 1 else 0} := by
    ext z
    simp [ValidInterpolationState]
  rw [hset]
  apply IsClosed.inter ((isCompact_nodeBox n).isClosed.preimage continuous_fst)
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq (continuous_state_evaluation n i j) continuous_const

theorem validState_admissible {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) : Admissible z.fst := by
  constructor
  · intro i j hij
    by_contra hne
    have hself := hz.2 i i
    have hother := hz.2 i j
    rw [hij] at hself
    simp only [ite_eq_left, ite_eq_right hne] at hself hother
    linarith
  · intro i
    exact hz.1 i

theorem validState_polynomial {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) (i : Fin n) :
    coefficientPolynomial (z.snd i) = cardinalPolynomial z.fst i := by
  have hinj := (validState_admissible hz).1
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hinj.injOn
  · simpa only [Finset.card_univ, Fintype.card_fin] using coefficientPolynomial_degree_lt (z.snd i)
  · simpa only [Finset.card_univ, Fintype.card_fin] using cardinalPolynomial_degree_lt hinj i
  · intro j hj
    exact (hz.2 i j).trans (cardinal_at_node hinj i j).symm

theorem validState_energy {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) : coefficientEnergy z.snd = energy z.fst := by
  unfold coefficientEnergy rowEnergy energy squareSum
  simp_rw [validState_polynomial hz]
  rw [intervalIntegral.integral_finsetSum
    (f := fun i x => cardinal z.fst i x ^ 2) (fun i _ =>
      ((cardinalPolynomial z.fst i).continuous.pow 2).intervalIntegrable _ _)]
  rfl

def stateOfNodes {n : ℕ} (nodes : Fin n → ℝ) : InterpolationState n :=
  (nodes, fun i j => (cardinalPolynomial nodes i).coeff j.val)

theorem stateOfNodes_valid {n : ℕ} {nodes : Fin n → ℝ} (h : Admissible nodes) :
    ValidInterpolationState (stateOfNodes nodes) := by
  constructor
  · intro i
    exact h.2 i
  · intro i j
    change (coefficientPolynomial (fun a : Fin n => (cardinalPolynomial nodes i).coeff a.val)).eval
      (nodes j) = if i = j then 1 else 0
    rw [coefficientPolynomial_of_polynomial _ (cardinalPolynomial_degree_lt h.1 i)]
    exact cardinal_at_node h.1 i j

theorem validStates_nonempty {n : ℕ} (hn : 0 < n) :
    Set.Nonempty {z : InterpolationState n | ValidInterpolationState z} :=
  ⟨stateOfNodes (referenceNodes n), stateOfNodes_valid (referenceNodes_admissible hn)⟩

end Erdos1131
