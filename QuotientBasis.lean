import MonomialQuotient

/-! The bounded monomials form a basis over every coefficient ring. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem normalMonomial_quotient {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) :
    Ideal.Quotient.mk (relationIdeal m tails) (normalMonomial tails htails a) =
      Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1) := by
  classical
  let projection := Ideal.Quotient.mk (relationIdeal m tails)
  change projection (normalMonomial tails htails a) = projection (MvPolynomial.monomial a 1)
  rw [normalMonomial]
  split_ifs with h
  · have hsum := Finset.sum_coe_sort (tails h.choose).support
      (fun b : Fin k →₀ ℕ => MvPolynomial.C ((tails h.choose).coeff b) *
        normalMonomial tails htails (a - Finsupp.single h.choose m + b))
    rw [hsum, map_sum]
    have hrelation : projection (MvPolynomial.X h.choose ^ m) = projection (tails h.choose) := by
      have hmem : relation m tails h.choose ∈ relationIdeal m tails :=
        Ideal.subset_span ⟨h.choose, rfl⟩
      have hz : projection (relation m tails h.choose) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa only [relation, map_sub, sub_eq_zero] using hz
    calc
      (∑ b ∈ (tails h.choose).support, projection
          (MvPolynomial.C ((tails h.choose).coeff b) *
            normalMonomial tails htails (a - Finsupp.single h.choose m + b))) =
          ∑ b ∈ (tails h.choose).support, projection
            (MvPolynomial.C ((tails h.choose).coeff b) *
              MvPolynomial.monomial (a - Finsupp.single h.choose m + b) 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [map_mul, map_mul, normalMonomial_quotient tails htails]
      _ = projection (MvPolynomial.monomial (a - Finsupp.single h.choose m) 1 * tails h.choose) := by
        rw [monomial_mul_expand, map_sum]
      _ = projection (MvPolynomial.monomial a 1) := by
        rw [map_mul, ← hrelation, ← map_mul, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul_monomial, one_mul,
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h.choose_spec)]
  · rfl
termination_by a.degree
decreasing_by exact replacement_degree_lt h.choose_spec (htails h.choose b hb)

theorem normalForm_quotient {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) :
    Ideal.Quotient.mk (relationIdeal m tails) (normalForm tails htails p) =
      Ideal.Quotient.mk (relationIdeal m tails) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial a coefficient =>
    rw [normalForm_monomial, map_mul, normalMonomial_quotient, ← map_mul,
      MvPolynomial.C_mul_monomial, mul_one]

def quotientMonomial {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (a : Erdos1131.BoundedIndex k (m - 1)) :
    RelationQuotient m tails :=
  Ideal.Quotient.mk (relationIdeal m tails) (Erdos1131.boundedMonomial a)

theorem quotientMonomials_linearIndependent {R : Type*} [CommRing R] {k m : ℕ}
    (hm : 0 < m) (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    LinearIndependent R (quotientMonomial (m := m) tails) := by
  have hcomp : LinearIndependent R
      (fun a => quotientNormalForm tails htails (quotientMonomial (m := m) tails a)) := by
    simpa only [quotientMonomial, quotientNormalForm_mk, normalForm_boundedMonomial hm]
      using Erdos1131.boundedMonomials_linearIndependent R k (m - 1)
  exact LinearIndependent.of_comp (quotientNormalForm tails htails) hcomp

theorem quotientMonomials_span {R : Type*} [CommRing R] {k m : ℕ}
    (hm : 0 < m) (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Submodule.span R (Set.range (quotientMonomial (m := m) tails)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← normalForm_quotient tails htails p]
  let projection := (Ideal.Quotient.mkₐ R (relationIdeal m tails)).toLinearMap
  have hmem : projection (normalForm tails htails p) ∈
      Submodule.map projection (normalSpace R k m) :=
    ⟨normalForm tails htails p, normalForm_mem hm tails htails p, rfl⟩
  rw [normalSpace, Submodule.map_span] at hmem
  rw [← Set.range_comp] at hmem
  exact hmem

def quotientBasis {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Basis (Erdos1131.BoundedIndex k (m - 1)) R (RelationQuotient m tails) :=
  Basis.mk (quotientMonomials_linearIndependent hm tails htails)
    (by rw [quotientMonomials_span hm tails htails])

theorem quotientBasis_apply {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Erdos1131.BoundedIndex k (m - 1)) :
    quotientBasis hm tails htails a = quotientMonomial tails a := by
  simp [quotientBasis]

end Erdos1131.MonomialReduction
