import QuotientBasis

/-! Quotient coordinates are the coefficients of the unique reduced representative. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem quotientBasis_repr_mk {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) (b : BoundedIndex k (m - 1)) :
    (quotientBasis hm tails htails).repr (Ideal.Quotient.mk (relationIdeal m tails) p) b =
      (normalForm tails htails p).coeff (boundedExponent b) := by
  classical
  have hlinear : (quotientBasis hm tails htails).coord b =
      (MvPolynomial.lcoeff R (boundedExponent b)).comp (quotientNormalForm tails htails) := by
    apply (quotientBasis hm tails htails).ext
    intro a
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [LinearMap.comp_apply,
      quotientBasis_apply, quotientMonomial, quotientNormalForm_mk,
      normalForm_boundedMonomial hm, MvPolynomial.lcoeff_apply, boundedMonomial_coeff]
    simp only [eq_comm]
  exact LinearMap.congr_fun hlinear (Ideal.Quotient.mk (relationIdeal m tails) p)

end Erdos1131.MonomialReduction
