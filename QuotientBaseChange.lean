import NormalizedBasis

/-! Coefficient specialization preserves the bounded monomial coordinates. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem relation_map {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) (i : Fin k) :
    (relation m tails i).map φ = relation m (fun j => (tails j).map φ) i := by
  simp [relation]

theorem relationIdeal_le_comap {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) :
    relationIdeal m tails ≤
      (relationIdeal m (fun i => (tails i).map φ)).comap (MvPolynomial.map φ) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change (relation m tails i).map φ ∈ relationIdeal m (fun j => (tails j).map φ)
  rw [relation_map]
  exact Ideal.subset_span ⟨i, rfl⟩

def quotientBaseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) :
    RelationQuotient m tails →+* RelationQuotient m (fun i => (tails i).map φ) :=
  Ideal.quotientMap _ (MvPolynomial.map φ) (relationIdeal_le_comap φ tails)

theorem quotientBaseChange_mk {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (p : MvPolynomial (Fin k) R) :
    quotientBaseChange (m := m) φ tails (Ideal.Quotient.mk (relationIdeal m tails) p) =
      Ideal.Quotient.mk (relationIdeal m (fun i => (tails i).map φ)) (p.map φ) := by
  rfl

theorem quotientBaseChange_algebraMap {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) (r : R) :
    quotientBaseChange (m := m) φ tails (algebraMap R (RelationQuotient m tails) r) =
      algebraMap S (RelationQuotient m (fun i => (tails i).map φ)) (φ r) := by
  change Ideal.Quotient.mk _ ((MvPolynomial.C r).map φ) =
    Ideal.Quotient.mk _ (MvPolynomial.C (φ r))
  rw [MvPolynomial.map_C]

theorem quotientBaseChange_smul {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (r : R) (q : RelationQuotient m tails) :
    quotientBaseChange φ tails (r • q) = φ r • quotientBaseChange φ tails q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hsource := (Ideal.Quotient.mkₐ R (relationIdeal m tails)).toLinearMap.map_smul r p
  have htarget := (Ideal.Quotient.mkₐ S
    (relationIdeal m (fun i => (tails i).map φ))).toLinearMap.map_smul (φ r) (p.map φ)
  erw [← hsource, quotientBaseChange_mk, ← htarget]
  have hp : (r • p).map φ = φ r • p.map φ := by
    rw [← MvPolynomial.C_mul', map_mul, MvPolynomial.map_C, MvPolynomial.C_mul']
  exact congrArg (Ideal.Quotient.mk _) hp

theorem quotientBaseChange_basis {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (a : BoundedIndex k (m - 1)) :
    quotientBaseChange φ tails (quotientBasis hm tails htails a) =
      quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) a := by
  simp only [quotientBasis_apply, quotientMonomial, quotientBaseChange_mk,
    boundedMonomial, MvPolynomial.map_monomial, map_one]

theorem quotientBaseChange_repr {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails)
    (a : BoundedIndex k (m - 1)) :
    (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails)).repr
        (quotientBaseChange φ tails q) a =
      φ ((quotientBasis hm tails htails).repr q a) := by
  classical
  have hrep : quotientBaseChange φ tails q =
      ∑ b, φ ((quotientBasis hm tails htails).repr q b) •
        quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) b := by
    conv_lhs => rw [← (quotientBasis hm tails htails).sum_repr q]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [quotientBaseChange_smul, quotientBaseChange_basis]
  rw [hrep]
  exact congrFun ((quotientBasis hm (fun i => (tails i).map φ)
    (lowerDegree_map φ htails)).repr_sum_self
      (fun b => φ ((quotientBasis hm tails htails).repr q b))) a

end Erdos1131.MonomialReduction
