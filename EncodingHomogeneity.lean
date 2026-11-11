import GapParametrization
import HomogeneousLift
import Mathlib.Algebra.BigOperators.Intervals

/-! Homogeneity and the critical-point reduction for the explicit rational polynomials. -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem twice_sum_fin_val (n : ℕ) :
    2 * (∑ i : Fin n, i.val) = n * (n - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
  have h := Finset.sum_range_id_mul_two n
  simpa only [mul_comm] using h

theorem algebraicDelta_mul {A : Type*} [CommRing A] {n : ℕ}
    (s : A) (nodes : Fin n → A) :
    algebraicDelta (fun i => s * nodes i) =
      s ^ (∑ i : Fin n, i.val) * algebraicDelta nodes := by
  have hmatrix : Matrix.vandermonde (fun i => s * nodes i) =
      Matrix.of (fun i j => s ^ j.val * Matrix.vandermonde nodes i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, mul_pow, Matrix.of_apply]
  unfold algebraicDelta
  rw [hmatrix, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]

theorem gapTotal_mul {A : Type*} [CommRing A] {k : ℕ} (s : A) (u : Fin k → A) :
    gapTotal (fun i => s * u i) = s ^ 2 * gapTotal u := by
  simp only [gapTotal, mul_pow, Finset.mul_sum]

theorem gapNodes_mul {A : Type*} [CommRing A] {k : ℕ}
    (s : A) (u : Fin k → A) (i : Fin (k + 1)) :
    gapNodes (fun j => s * u j) i = s ^ 2 * gapNodes u i := by
  have hprefix : gapPrefix (fun j => (s * u j) ^ 2) i =
      s ^ 2 * gapPrefix (fun j => u j ^ 2) i := by
    simp only [gapPrefix, mul_pow, Finset.mul_sum]
  change -gapTotal (fun j => s * u j) + 2 * gapPrefix (fun j => (s * u j) ^ 2) i =
    s ^ 2 * (-gapTotal u + 2 * gapPrefix (fun j => u j ^ 2) i)
  rw [gapTotal_mul, hprefix]
  ring

theorem scaled_updated_gapNodes {A : Type*} [CommRing A] {k : ℕ}
    (s : A) (u : Fin k → A) (i : Fin (k + 1)) (x : A) :
    Function.update (gapNodes (fun j => s * u j)) i (gapTotal (fun j => s * u j) * x) =
      fun j => s ^ 2 * Function.update (gapNodes u) i (gapTotal u * x) j := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, gapTotal_mul]
    ring
  · simp only [Function.update_of_ne hji, gapNodes_mul]

theorem gap_degree_identity (k : ℕ) :
    2 * ((∑ i : Fin (k + 1), i.val) * 2) = 2 * ((k + 1) * k) := by
  rw [← mul_assoc, twice_sum_fin_val]
  simp only [Nat.add_sub_cancel]
  omega

theorem updated_delta_homogeneous {k : ℕ} (s : ℝ) (u : Fin k → ℝ)
    (i : Fin (k + 1)) (x : ℝ) :
    delta (Function.update (gapNodes (s • u)) i (gapTotal (s • u) * x)) ^ 2 =
      s ^ (2 * ((k + 1) * k)) *
        delta (Function.update (gapNodes u) i (gapTotal u * x)) ^ 2 := by
  change delta (Function.update (gapNodes (fun j => s * u j)) i
    (gapTotal (fun j => s * u j) * x)) ^ 2 = _
  rw [scaled_updated_gapNodes]
  change algebraicDelta (fun j => s ^ 2 *
    Function.update (gapNodes u) i (gapTotal u * x) j) ^ 2 = _
  rw [algebraicDelta_mul, mul_pow, ← pow_mul, ← pow_mul, gap_degree_identity]
  rfl

theorem numerator_homogeneous (k : ℕ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k))
      (fun u : Fin k → ℝ => MvPolynomial.aeval u (numeratorPolynomial k)) := by
  intro s u
  dsimp only
  rw [numeratorPolynomial_eval, numeratorPolynomial_eval,
    encodingNumerator_real, encodingNumerator_real]
  simp_rw [updated_delta_homogeneous, intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]

theorem denominator_homogeneous (k : ℕ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k))
      (fun u : Fin k → ℝ => MvPolynomial.aeval u (denominatorPolynomial k)) := by
  intro s u
  dsimp only
  rw [denominatorPolynomial_eval, denominatorPolynomial_eval]
  change algebraicDelta (gapNodes (fun j => s * u j)) ^ 2 =
    s ^ (2 * ((k + 1) * k)) * algebraicDelta (gapNodes u) ^ 2
  have hnodes : gapNodes (fun j => s * u j) = fun j => s ^ 2 * gapNodes u j :=
    funext (gapNodes_mul s u)
  rw [hnodes, algebraicDelta_mul, mul_pow, ← pow_mul, ← pow_mul, gap_degree_identity]

theorem threshold_homogeneous (k : ℕ) (t : ℝ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k)) (thresholdExpression k t) := by
  intro s u
  dsimp [thresholdExpression]
  have hn := numerator_homogeneous k s u
  have hd := denominator_homogeneous k s u
  dsimp only at hn hd
  rw [hn, hd]
  ring

theorem differentiable_aeval (k : ℕ) (p : MvPolynomial (Fin k) ℚ) :
    Differentiable ℝ (fun u : Fin k → ℝ => MvPolynomial.aeval u p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    fun_prop
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (by fun_prop)

theorem threshold_differentiable (k : ℕ) (t : ℝ) :
    Differentiable ℝ (thresholdExpression k t) := by
  exact (differentiable_aeval k (numeratorPolynomial k)).sub
    ((differentiable_aeval k (denominatorPolynomial k)).const_mul t)

theorem critical_points_singleton_iff_endpoint_bound {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0} = {0} ↔
      ∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes := by
  rw [HomogeneousLift.critical_points_singleton_iff_nonnegative
    (Nat.mul_pos (Nat.succ_pos k) hk) (threshold_homogeneous k t)
    (threshold_differentiable k t)]
  exact thresholdExpression_globally_nonnegative_iff hk t

end Erdos1131
