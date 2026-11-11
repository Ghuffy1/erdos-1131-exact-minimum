import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Tactic

/-! The finite monomial index set used for the normalized-gradient quotient. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

abbrev BoundedIndex (k d : ℕ) := Fin k → Fin (d + 1)

def boundedExponent {k d : ℕ} (a : BoundedIndex k d) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

theorem boundedExponent_apply {k d : ℕ} (a : BoundedIndex k d) (i : Fin k) :
    boundedExponent a i = (a i).val := by
  simp [boundedExponent]

theorem boundedExponent_injective (k d : ℕ) :
    Function.Injective (boundedExponent (k := k) (d := d)) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun f : Fin k →₀ ℕ => f i) hab
  simpa only [boundedExponent_apply] using h

theorem boundedExponent_le {k d : ℕ} (a : BoundedIndex k d) (i : Fin k) :
    boundedExponent a i ≤ d := by
  rw [boundedExponent_apply]
  exact Nat.le_of_lt_succ (a i).isLt

theorem exists_boundedIndex {k d : ℕ} (a : Fin k →₀ ℕ) (ha : ∀ i, a i ≤ d) :
    ∃ b : BoundedIndex k d, boundedExponent b = a := by
  refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, ?_⟩
  ext i
  simp only [boundedExponent_apply]

theorem card_boundedIndex (k d : ℕ) : Fintype.card (BoundedIndex k d) = (d + 1) ^ k := by
  simp only [BoundedIndex, Fintype.card_fun, Fintype.card_fin]

def boundedMonomial {R : Type*} [CommRing R] {k d : ℕ} (a : BoundedIndex k d) :
    MvPolynomial (Fin k) R := MvPolynomial.monomial (boundedExponent a) 1

theorem boundedMonomials_linearIndependent (R : Type*) [CommRing R] (k d : ℕ) :
    LinearIndependent R (boundedMonomial (R := R) (k := k) (d := d)) := by
  change LinearIndependent R
    (fun a : BoundedIndex k d => (MvPolynomial.basisMonomials (Fin k) R) (boundedExponent a))
  exact (MvPolynomial.basisMonomials (Fin k) R).linearIndependent.comp
    boundedExponent (boundedExponent_injective k d)

theorem boundedMonomial_coeff {R : Type*} [CommRing R] {k d : ℕ}
    (a b : BoundedIndex k d) :
    (boundedMonomial (R := R) b).coeff (boundedExponent a) =
      if a = b then 1 else 0 := by
  classical
  simp only [boundedMonomial, MvPolynomial.coeff_monomial,
    (boundedExponent_injective k d).eq_iff, eq_comm]

end Erdos1131
