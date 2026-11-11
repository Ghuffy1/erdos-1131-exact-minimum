import WeightedReduction
import EncodingDegrees

/-! The normalized-gradient tails have the required parameter-weight bounds. -/

noncomputable section

namespace Erdos1131

theorem parametricThreshold_coefficient_degree (k : ℕ) (a : Fin k →₀ ℕ) :
    ((parametricThreshold k).coeff a).natDegree ≤ 1 := by
  unfold parametricThreshold liftRationalCoefficients
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem reductionTails_coefficient_degree (k : ℕ) (i : Fin k) (a : Fin k →₀ ℕ) :
    ((reductionTails k i).coeff a).natDegree ≤ 1 := by
  unfold reductionTails
  rw [MvPolynomial.coeff_neg, Polynomial.natDegree_neg, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_pderiv]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply Polynomial.natDegree_mul_le.trans
  have hp := parametricThreshold_coefficient_degree k (a + Finsupp.single i 1)
  simpa using hp

theorem reductionTails_weightBound (k : ℕ) (i : Fin k) :
    MonomialReduction.WeightBound (clearedDegree k + 1) (reductionTails k i) := by
  intro a ha
  have hdegree : a.degree ≤ (reductionTails k i).totalDegree :=
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr ha)
  have htail : (reductionTails k i).totalDegree ≤ clearedDegree k - 1 := by
    simpa only [reductionTails, MvPolynomial.totalDegree_neg]
      using normalizedGradient_tail_totalDegree_le k i
  have hparameter := reductionTails_coefficient_degree k i a
  have hk : 0 < k := by
    have hi := i.isLt
    omega
  have hd : 0 < clearedDegree k := by
    unfold clearedDegree
    positivity
  omega

theorem normalized_normalMonomial_weightBound (k : ℕ) (a : Fin k →₀ ℕ) :
    MonomialReduction.WeightBound a.degree
      (MonomialReduction.normalMonomial (reductionTails k) (reductionTails_lower k) a) :=
  MonomialReduction.normalMonomial_weightBound _ _ (reductionTails_weightBound k) _

end Erdos1131
