import ParametricWeights
import QuotientCoordinates
import TraceConstruction

/-! Every parameter entry of the Hermite matrix has degree at most k times d. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem trace_monomial_eq_sum {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) :
    Algebra.trace ParameterRing (RelationQuotient m tails)
        (Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1)) =
      ∑ b : BoundedIndex k (m - 1),
        (normalMonomial tails htails (a + boundedExponent b)).coeff (boundedExponent b) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (quotientBasis hm tails htails), Matrix.trace]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, quotientBasis_apply,
    quotientMonomial, boundedMonomial, ← map_mul, MvPolynomial.monomial_mul_monomial,
    one_mul, quotientBasis_repr_mk, normalForm_monomial_one]

theorem trace_monomial_degree_le {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (hweight : ∀ i, WeightBound m (tails i)) (a : Fin k →₀ ℕ) :
    (Algebra.trace ParameterRing (RelationQuotient m tails)
      (Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1))).natDegree ≤
        a.degree / 2 := by
  classical
  rw [trace_monomial_eq_sum hm tails htails]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b hb
  by_cases hz : (normalMonomial tails htails (a + boundedExponent b)).coeff (boundedExponent b) = 0
  · simp [hz]
  · have h := normalMonomial_weightBound tails htails hweight (a + boundedExponent b)
      (boundedExponent b) hz
    rw [map_add] at h
    omega

end Erdos1131.MonomialReduction

namespace Erdos1131

theorem boundedExponent_degree_le {k d : ℕ} (a : BoundedIndex k d) :
    (boundedExponent a).degree ≤ k * d := by
  rw [Finsupp.degree_eq_sum]
  calc
    ∑ i, boundedExponent a i ≤ ∑ _ : Fin k, d :=
      Finset.sum_le_sum (fun i _ => boundedExponent_le a i)
    _ = k * d := by simp

theorem parametricHermiteMatrix_entry_degree (k : ℕ)
    (a b : BoundedIndex k (clearedDegree k)) :
    (parametricHermiteMatrix k a b).natDegree ≤ k * clearedDegree k := by
  rw [parametricHermiteMatrix, MonomialReduction.hermiteMatrix_apply]
  have h := MonomialReduction.trace_monomial_degree_le
    (Nat.zero_lt_succ (clearedDegree k)) (reductionTails k) (reductionTails_lower k)
    (reductionTails_weightBound k) (boundedExponent a + boundedExponent b)
  have ha := boundedExponent_degree_le a
  have hb := boundedExponent_degree_le b
  rw [map_add] at h
  omega

end Erdos1131
