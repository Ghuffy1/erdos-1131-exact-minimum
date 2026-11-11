import GradedPolynomialEncoding

/-! Exact degrees of the rational forms and the lower-degree gradient tails. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem gapTotal_polynomial_homogeneous (k : ℕ) :
    (gapTotal (fun i : Fin k => (MvPolynomial.X i : MvPolynomial (Fin k) ℚ))).IsHomogeneous 2 := by
  unfold gapTotal
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_X_pow i 2)

theorem gapNodes_polynomial_homogeneous (k : ℕ) (i : Fin (k + 1)) :
    (gapNodes (fun j : Fin k => (MvPolynomial.X j : MvPolynomial (Fin k) ℚ)) i).IsHomogeneous 2 := by
  have hprefix : (gapPrefix (fun j : Fin k =>
      (MvPolynomial.X j : MvPolynomial (Fin k) ℚ) ^ 2) i).IsHomogeneous 2 := by
    unfold gapPrefix
    exact MvPolynomial.IsHomogeneous.sum _ _ _
      (fun j _ => MvPolynomial.isHomogeneous_X_pow j 2)
  unfold gapNodes
  convert! (gapTotal_polynomial_homogeneous k).neg.add (hprefix.C_mul 2) using 1

theorem vandermonde_homogeneousCoefficients {σ : Type*} {n : ℕ}
    (nodes : Fin n → Polynomial (MvPolynomial σ ℚ))
    (hnodes : ∀ i, HasHomogeneousCoefficients (nodes i) 2) :
    HasHomogeneousCoefficients (algebraicDelta nodes) (n * (n - 1)) := by
  have hdet := HasHomogeneousCoefficients.det (Matrix.vandermonde nodes)
    (fun j : Fin n => 2 * j.val) (fun i j => (hnodes i).pow j.val)
  change HasHomogeneousCoefficients (Matrix.vandermonde nodes).det (n * (n - 1))
  have hdegree : (∑ j : Fin n, 2 * j.val) = n * (n - 1) := by
    rw [← Finset.mul_sum, twice_sum_fin_val]
  rwa [hdegree] at hdet

theorem denominatorPolynomial_homogeneous (k : ℕ) :
    (denominatorPolynomial k).IsHomogeneous (clearedDegree k) := by
  let nodes := gapNodes (fun i : Fin k => (MvPolynomial.X i : MvPolynomial (Fin k) ℚ))
  have hdet : HasHomogeneousCoefficients
      (algebraicDelta (fun i => Polynomial.C (nodes i))) ((k + 1) * k) := by
    simpa only [Nat.add_sub_cancel] using vandermonde_homogeneousCoefficients
      (fun i => Polynomial.C (nodes i))
      (fun i => HasHomogeneousCoefficients.constant (gapNodes_polynomial_homogeneous k i))
  have hpow := hdet.pow 2 0
  have hmap := algebraicDelta_map Polynomial.C nodes
  rw [← hmap, ← Polynomial.C_pow, Polynomial.coeff_C_zero] at hpow
  change (algebraicDelta nodes ^ 2).IsHomogeneous (clearedDegree k)
  simpa only [clearedDegree, Nat.mul_comm] using hpow

theorem numeratorPolynomial_homogeneous (k : ℕ) :
    (numeratorPolynomial k).IsHomogeneous (clearedDegree k) := by
  unfold numeratorPolynomial encodingNumerator
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply coefficientMoment_homogeneous
  have hnodes : ∀ j : Fin (k + 1), HasHomogeneousCoefficients
      (Function.update
        (fun j => Polynomial.C (gapNodes (fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) ℚ)) j))
        i (Polynomial.C (gapTotal (fun a : Fin k => MvPolynomial.X a)) * Polynomial.X) j) 2 := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      simpa only [Nat.add_zero] using
        (HasHomogeneousCoefficients.constant (gapTotal_polynomial_homogeneous k)).mul
          HasHomogeneousCoefficients.indeterminate
    · rw [Function.update_of_ne hji]
      exact HasHomogeneousCoefficients.constant (gapNodes_polynomial_homogeneous k j)
  have hdet := vandermonde_homogeneousCoefficients _ hnodes
  simpa only [clearedDegree, Nat.add_sub_cancel, Nat.mul_comm] using hdet.pow 2

theorem parametricThreshold_homogeneous (k : ℕ) :
    (parametricThreshold k).IsHomogeneous (clearedDegree k) := by
  unfold parametricThreshold liftRationalCoefficients
  exact ((numeratorPolynomial_homogeneous k).map Polynomial.C).sub
    (((denominatorPolynomial_homogeneous k).map Polynomial.C).C_mul Polynomial.X)

theorem normalizedGradient_tail_homogeneous (k : ℕ) (i : Fin k) :
    (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)).IsHomogeneous (clearedDegree k - 1) :=
  (parametricThreshold_homogeneous k).pderiv.C_mul _

theorem normalizedGradient_tail_totalDegree_le (k : ℕ) (i : Fin k) :
    (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)).totalDegree ≤ clearedDegree k - 1 :=
  (normalizedGradient_tail_homogeneous k i).totalDegree_le

end Erdos1131
