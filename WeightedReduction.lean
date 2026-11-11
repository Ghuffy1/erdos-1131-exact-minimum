import QuotientBaseChange
import Mathlib.Algebra.Polynomial.BigOperators

/-! Parameter-degree bounds are preserved by the terminating monomial reduction. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

def WeightBound {k : ℕ} (bound : ℕ) (p : MvPolynomial (Fin k) ParameterRing) : Prop :=
  ∀ a, p.coeff a ≠ 0 → a.degree + 2 * (p.coeff a).natDegree ≤ bound

theorem weightBound_mono {k a b : ℕ} {p : MvPolynomial (Fin k) ParameterRing}
    (hab : a ≤ b) (hp : WeightBound a p) : WeightBound b p :=
  fun c hc => (hp c hc).trans hab

theorem weightBound_monomial {k : ℕ} (a : Fin k →₀ ℕ) :
    WeightBound a.degree (MvPolynomial.monomial a (1 : ParameterRing)) := by
  classical
  intro b hb
  by_cases h : b = a
  · subst b
    simp
  · simp [MvPolynomial.coeff_monomial] at hb
    exact (h hb.symm).elim

theorem weightBound_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin k) ParameterRing) (bound : ℕ)
    (hp : ∀ i ∈ s, WeightBound bound (p i)) : WeightBound bound (∑ i ∈ s, p i) := by
  classical
  intro a ha
  have hsum : ∑ i ∈ s, (p i).coeff a ≠ 0 := by
    simpa only [MvPolynomial.coeff_sum] using ha
  obtain ⟨i, hi, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdegree : a.degree ≤ bound := by
    have := hp i hi a hcoeff
    omega
  have hpieces : ∀ j ∈ s, ((p j).coeff a).natDegree ≤ (bound - a.degree) / 2 := by
    intro j hj
    by_cases hz : (p j).coeff a = 0
    · simp [hz]
    · have := hp j hj a hz
      omega
  have hbound := Polynomial.natDegree_sum_le_of_forall_le s
    (fun j => (p j).coeff a) hpieces
  rw [MvPolynomial.coeff_sum]
  omega

theorem weightBound_C_mul {k bound : ℕ} (q : ParameterRing)
    {p : MvPolynomial (Fin k) ParameterRing} (hp : WeightBound bound p) :
    WeightBound (bound + 2 * q.natDegree) (MvPolynomial.C q * p) := by
  intro a ha
  rw [MvPolynomial.coeff_C_mul] at ha ⊢
  have hnonzero : p.coeff a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  have hweight := hp a hnonzero
  have hdegree := Polynomial.natDegree_mul_le (p := q) (q := p.coeff a)
  omega

theorem normalMonomial_weightBound {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (hweight : ∀ i, WeightBound m (tails i)) (a : Fin k →₀ ℕ) :
    WeightBound a.degree (normalMonomial tails htails a) := by
  classical
  rw [normalMonomial]
  split_ifs with h
  · apply weightBound_sum
    intro b hb
    have hrec := normalMonomial_weightBound tails htails hweight
      (a - Finsupp.single h.choose m + b.val)
    have hcoefficient : (tails h.choose).coeff b.val ≠ 0 :=
      MvPolynomial.mem_support_iff.mp b.property
    have htail := hweight h.choose b.val hcoefficient
    have hsingle : Finsupp.single h.choose m ≤ a :=
      Finsupp.single_le_iff.mpr h.choose_spec
    have hdegree : (a - Finsupp.single h.choose m).degree + m = a.degree := by
      have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hsingle)
      simpa only [map_add, Finsupp.degree_single] using hd
    apply weightBound_mono _ (weightBound_C_mul ((tails h.choose).coeff b.val) hrec)
    rw [map_add]
    omega
  · exact weightBound_monomial a
termination_by a.degree
decreasing_by exact replacement_degree_lt h.choose_spec (htails h.choose b.val b.property)

end Erdos1131.MonomialReduction
