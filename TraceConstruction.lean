import QuotientBaseChange
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Multiplication and Hermite trace matrices in the fixed quotient basis. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem leftMulMatrix_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails) :
    Algebra.leftMulMatrix
        (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails))
        (quotientBaseChange φ tails q) =
      (Algebra.leftMulMatrix (quotientBasis hm tails htails) q).map φ := by
  classical
  ext a b
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply]
  rw [← quotientBaseChange_basis hm φ tails htails b, ← map_mul,
    quotientBaseChange_repr]

theorem trace_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails) :
    Algebra.trace S (RelationQuotient m (fun i => (tails i).map φ))
        (quotientBaseChange φ tails q) =
      φ (Algebra.trace R (RelationQuotient m tails) q) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (quotientBasis hm tails htails),
    Algebra.trace_eq_matrix_trace
      (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails)),
    leftMulMatrix_baseChange, AddMonoidHom.map_trace]

def hermiteMatrix {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Matrix (BoundedIndex k (m - 1)) (BoundedIndex k (m - 1)) R :=
  (Algebra.traceForm R (RelationQuotient m tails)).toMatrix (quotientBasis hm tails htails)

theorem hermiteMatrix_apply {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a b : BoundedIndex k (m - 1)) :
    hermiteMatrix hm tails htails a b = Algebra.trace R (RelationQuotient m tails)
      (Ideal.Quotient.mk (relationIdeal m tails)
        (MvPolynomial.monomial (boundedExponent a + boundedExponent b) 1)) := by
  classical
  rw [hermiteMatrix, Algebra.traceForm_toMatrix]
  simp only [quotientBasis_apply, quotientMonomial, boundedMonomial, ← map_mul,
    MvPolynomial.monomial_mul_monomial, one_mul]

theorem hermiteMatrix_isSymm {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    (hermiteMatrix hm tails htails).IsSymm := by
  classical
  ext a b
  simp only [Matrix.transpose_apply, hermiteMatrix_apply, add_comm]

theorem hermiteMatrix_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) :
    hermiteMatrix hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) =
      (hermiteMatrix hm tails htails).map φ := by
  classical
  ext a b
  simp only [hermiteMatrix_apply, Matrix.map_apply]
  rw [← trace_baseChange hm φ tails htails, quotientBaseChange_mk,
    MvPolynomial.map_monomial]
  simp only [map_one]

end Erdos1131.MonomialReduction

namespace Erdos1131

def parametricHermiteMatrix (k : ℕ) :
    Matrix (BoundedIndex k (clearedDegree k)) (BoundedIndex k (clearedDegree k)) ParameterRing :=
  MonomialReduction.hermiteMatrix (Nat.zero_lt_succ (clearedDegree k))
    (reductionTails k) (reductionTails_lower k)

def specializedHermiteMatrix {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Matrix (BoundedIndex k (clearedDegree k)) (BoundedIndex k (clearedDegree k)) S :=
  MonomialReduction.hermiteMatrix (Nat.zero_lt_succ (clearedDegree k))
    (specializedTails k φ) (specializedTails_lower k φ)

theorem specializedHermiteMatrix_eq_map {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    specializedHermiteMatrix k φ = (parametricHermiteMatrix k).map φ :=
  MonomialReduction.hermiteMatrix_baseChange _ φ _ _

theorem parametricHermiteMatrix_isSymm (k : ℕ) : (parametricHermiteMatrix k).IsSymm :=
  MonomialReduction.hermiteMatrix_isSymm _ _ _

theorem specializedHermiteMatrix_isSymm {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) : (specializedHermiteMatrix k φ).IsSymm :=
  MonomialReduction.hermiteMatrix_isSymm _ _ _

def hermiteCharacteristicPolynomial (k : ℕ) : Polynomial ParameterRing :=
  (parametricHermiteMatrix k).charpoly

theorem specializedHermiteMatrix_charpoly {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    (specializedHermiteMatrix k φ).charpoly = (hermiteCharacteristicPolynomial k).map φ := by
  rw [specializedHermiteMatrix_eq_map, Matrix.charpoly_map]
  rfl

theorem hermiteCharacteristicPolynomial_monic (k : ℕ) :
    (hermiteCharacteristicPolynomial k).Monic := Matrix.charpoly_monic _

theorem hermiteCharacteristicPolynomial_natDegree (k : ℕ) :
    (hermiteCharacteristicPolynomial k).natDegree = (clearedDegree k + 1) ^ k := by
  rw [hermiteCharacteristicPolynomial, Matrix.charpoly_natDegree_eq_dim, card_boundedIndex]

end Erdos1131
