import MonomialConfluence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The normal-form map and the quotient by the pure-power relations. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

def relation {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) (i : Fin k) : MvPolynomial (Fin k) R :=
  MvPolynomial.X i ^ m - tails i

def relationIdeal {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range (relation m tails))

abbrev RelationQuotient {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) :=
  (MvPolynomial (Fin k) R) ⧸ relationIdeal m tails

theorem normalForm_monomial_mul_relation {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (i : Fin k) :
    normalForm tails htails (MvPolynomial.monomial a 1 * relation m tails i) = 0 := by
  unfold relation
  rw [mul_sub, map_sub, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, one_mul, normalForm_monomial_one]
  apply sub_eq_zero.mpr
  have hi : m ≤ (a + Finsupp.single i m) i := by simp
  have h := normalMonomial_rule tails htails (a + Finsupp.single i m) i hi
  simpa only [add_tsub_cancel_right] using h

theorem normalForm_mul_relation {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) (i : Fin k) :
    normalForm tails htails (p * relation m tails i) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, add_zero]
  | monomial a coefficient =>
    have hmonomial : MvPolynomial.monomial a coefficient =
        coefficient • (MvPolynomial.monomial a 1 : MvPolynomial (Fin k) R) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hmonomial, smul_mul_assoc, map_smul, normalForm_monomial_mul_relation, smul_zero]

theorem normalForm_zero_of_mem_ideal {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    {p : MvPolynomial (Fin k) R} (hp : p ∈ relationIdeal m tails) :
    normalForm tails htails p = 0 := by
  change p ∈ Ideal.span (Set.range (relation m tails)) at hp
  obtain ⟨coefficients, hcoefficients⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  rw [← hcoefficients, map_sum]
  exact Finset.sum_eq_zero (fun i hi => normalForm_mul_relation tails htails (coefficients i) i)

def quotientNormalForm {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    RelationQuotient m tails →ₗ[R] MvPolynomial (Fin k) R :=
  ((relationIdeal m tails).restrictScalars R).liftQ (normalForm tails htails)
    (fun p hp => normalForm_zero_of_mem_ideal tails htails hp) |>.comp
      (Submodule.Quotient.restrictScalarsEquiv R (relationIdeal m tails)).symm.toLinearMap

theorem quotientNormalForm_mk {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) :
    quotientNormalForm tails htails (Ideal.Quotient.mk (relationIdeal m tails) p) =
      normalForm tails htails p := by
  rfl

theorem monomial_mul_expand {R : Type*} [CommRing R] {k : ℕ}
    (a : Fin k →₀ ℕ) (p : MvPolynomial (Fin k) R) :
    MvPolynomial.monomial a 1 * p =
      ∑ b ∈ p.support, MvPolynomial.C (p.coeff b) * MvPolynomial.monomial (a + b) 1 := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.C_mul_monomial, mul_one]

end Erdos1131.MonomialReduction
