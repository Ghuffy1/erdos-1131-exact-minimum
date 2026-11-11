import QuotientBasis
import EncodingDegrees

/-! The fixed monomial basis over the parameter ring and after specialization. -/

open Module

noncomputable section

namespace Erdos1131

def reductionTails (k : ℕ) (i : Fin k) : MvPolynomial (Fin k) ParameterRing :=
  -(MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
    MvPolynomial.pderiv i (parametricThreshold k))

theorem reductionTails_lower (k : ℕ) :
    MonomialReduction.LowerDegree (clearedDegree k + 1) (reductionTails k) := by
  intro i a ha
  have hdegree := MvPolynomial.le_totalDegree ha
  change a.degree ≤ (-(_ : MvPolynomial (Fin k) ParameterRing)).totalDegree at hdegree
  rw [MvPolynomial.totalDegree_neg] at hdegree
  have htail := normalizedGradient_tail_totalDegree_le k i
  omega

theorem reduction_relation_eq_gradient (k : ℕ) :
    MonomialReduction.relation (clearedDegree k + 1) (reductionTails k) = normalizedGradient k := by
  funext i
  simp only [MonomialReduction.relation, reductionTails, normalizedGradient, sub_neg_eq_add]

theorem reductionIdeal_eq_gradientIdeal (k : ℕ) :
    MonomialReduction.relationIdeal (clearedDegree k + 1) (reductionTails k) = gradientIdeal k := by
  rw [MonomialReduction.relationIdeal, reduction_relation_eq_gradient, gradientIdeal]

def normalizedGradientBasis (k : ℕ) :
    Basis (BoundedIndex k (clearedDegree k)) ParameterRing (GradientQuotient k) :=
  (MonomialReduction.quotientBasis (Nat.zero_lt_succ (clearedDegree k))
    (reductionTails k) (reductionTails_lower k)).map
      (Ideal.quotientEquivAlgOfEq ParameterRing (reductionIdeal_eq_gradientIdeal k)).toLinearEquiv

theorem normalizedGradientBasis_apply (k : ℕ) (a : BoundedIndex k (clearedDegree k)) :
    normalizedGradientBasis k a = Ideal.Quotient.mk (gradientIdeal k) (boundedMonomial a) := by
  simp [normalizedGradientBasis, MonomialReduction.quotientBasis_apply,
    MonomialReduction.quotientMonomial]

instance normalizedGradient_free (k : ℕ) : Module.Free ParameterRing (GradientQuotient k) :=
  Module.Free.of_basis (normalizedGradientBasis k)

instance normalizedGradient_finite (k : ℕ) : Module.Finite ParameterRing (GradientQuotient k) :=
  Module.Finite.of_basis (normalizedGradientBasis k)

theorem lowerDegree_map {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) {tails : Fin k → MvPolynomial (Fin k) R}
    (htails : MonomialReduction.LowerDegree m tails) :
    MonomialReduction.LowerDegree m (fun i => (tails i).map φ) := by
  intro i a ha
  have hcoefficient : ((tails i).map φ).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
  have horiginal : (tails i).coeff a ≠ 0 := by
    intro hz
    apply hcoefficient
    simp [MvPolynomial.coeff_map, hz]
  exact htails i a (MvPolynomial.mem_support_iff.mpr horiginal)

def specializedTails {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S)
    (i : Fin k) : MvPolynomial (Fin k) S :=
  (reductionTails k i).map φ

theorem specializedTails_lower {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    MonomialReduction.LowerDegree (clearedDegree k + 1) (specializedTails k φ) :=
  lowerDegree_map φ (reductionTails_lower k)

abbrev SpecializedQuotient {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :=
  MonomialReduction.RelationQuotient (clearedDegree k + 1) (specializedTails k φ)

def specializedGradientBasis {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Basis (BoundedIndex k (clearedDegree k)) S (SpecializedQuotient k φ) :=
  MonomialReduction.quotientBasis (Nat.zero_lt_succ (clearedDegree k))
    (specializedTails k φ) (specializedTails_lower k φ)

instance specializedGradient_free {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.Free S (SpecializedQuotient k φ) :=
  Module.Free.of_basis (specializedGradientBasis k φ)

instance specializedGradient_finite {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.Finite S (SpecializedQuotient k φ) :=
  Module.Finite.of_basis (specializedGradientBasis k φ)

theorem specializedGradient_finrank {S : Type*} [Field S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.finrank S (SpecializedQuotient k φ) = (clearedDegree k + 1) ^ k := by
  rw [Module.finrank_eq_card_basis (specializedGradientBasis k φ), card_boundedIndex]

end Erdos1131
