import ParametricSystem
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Algebraic homogeneity of every coefficient in the Vandermonde construction. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

def HasHomogeneousCoefficients {σ R : Type*} [CommRing R]
    (p : Polynomial (MvPolynomial σ R)) (degree : ℕ) : Prop :=
  ∀ j, (p.coeff j).IsHomogeneous degree

namespace HasHomogeneousCoefficients

variable {σ R : Type*} [CommRing R]

theorem zero (degree : ℕ) :
    HasHomogeneousCoefficients (0 : Polynomial (MvPolynomial σ R)) degree := by
  intro j
  simpa using (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) degree)

theorem constant {p : MvPolynomial σ R} {degree : ℕ} (hp : p.IsHomogeneous degree) :
    HasHomogeneousCoefficients (Polynomial.C p) degree := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using hp
  · simpa [Polynomial.coeff_C, hj, Ne.symm hj] using
      (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) degree)

theorem one : HasHomogeneousCoefficients (1 : Polynomial (MvPolynomial σ R)) 0 := by
  simpa using constant (MvPolynomial.isHomogeneous_one (σ := σ) (R := R))

theorem indeterminate : HasHomogeneousCoefficients (Polynomial.X : Polynomial (MvPolynomial σ R)) 0 := by
  intro j
  by_cases hj : j = 1
  · subst j
    simpa using (MvPolynomial.isHomogeneous_one (σ := σ) (R := R))
  · simpa [Polynomial.coeff_X, hj, Ne.symm hj] using
      (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) 0)

theorem add {p q : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) (hq : HasHomogeneousCoefficients q degree) :
    HasHomogeneousCoefficients (p + q) degree := by
  intro j
  rw [Polynomial.coeff_add]
  exact (hp j).add (hq j)

theorem neg {p : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) : HasHomogeneousCoefficients (-p) degree := by
  intro j
  rw [Polynomial.coeff_neg]
  exact (hp j).neg

theorem sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R)) (degree : ℕ)
    (hp : ∀ i ∈ s, HasHomogeneousCoefficients (p i) degree) :
    HasHomogeneousCoefficients (∑ i ∈ s, p i) degree := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i hi => hp i hi j)

theorem mul {p q : Polynomial (MvPolynomial σ R)} {degreeP degreeQ : ℕ}
    (hp : HasHomogeneousCoefficients p degreeP) (hq : HasHomogeneousCoefficients q degreeQ) :
    HasHomogeneousCoefficients (p * q) (degreeP + degreeQ) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun pair _ => (hp pair.1).mul (hq pair.2))

theorem pow {p : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) (n : ℕ) :
    HasHomogeneousCoefficients (p ^ n) (degree * n) := by
  induction n with
  | zero => simpa using (one (σ := σ) (R := R))
  | succ n ih =>
    simpa only [pow_succ, Nat.mul_succ] using ih.mul hp

theorem prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R))
    (degree : ι → ℕ) (hp : ∀ i ∈ s, HasHomogeneousCoefficients (p i) (degree i)) :
    HasHomogeneousCoefficients (∏ i ∈ s, p i) (∑ i ∈ s, degree i) := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simpa using (one (σ := σ) (R := R))
  | @insert i s his ih =>
    intro hp
    simp only [Finset.prod_insert his, Finset.sum_insert his]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial (MvPolynomial σ R))) (degree : ι → ℕ)
    (hM : ∀ i j, HasHomogeneousCoefficients (M i j) (degree j)) :
    HasHomogeneousCoefficients M.det (∑ j, degree j) := by
  classical
  rw [Matrix.det_apply]
  apply sum
  intro permutation hpermutation
  have hprod := prod Finset.univ (fun j => M (permutation j) j) degree
    (fun j _ => hM (permutation j) j)
  rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with hsign | hsign
  · simpa [hsign] using hprod
  · simpa [hsign] using hprod.neg

end HasHomogeneousCoefficients

theorem coefficientMoment_homogeneous {σ : Type*}
    {p : Polynomial (MvPolynomial σ ℚ)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) : (coefficientMoment p).IsHomogeneous degree := by
  change (∑ j ∈ p.support, p.coeff j * algebraMap ℚ (MvPolynomial σ ℚ) (moment j)).IsHomogeneous degree
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  change (p.coeff j * MvPolynomial.C (moment j)).IsHomogeneous degree
  simpa only [mul_comm] using (hp j).C_mul (moment j)

end Erdos1131
