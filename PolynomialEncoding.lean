import VandermondeMoment
import Mathlib.Algebra.MvPolynomial.Eval

/-! Rational coefficient rules for the cleared interpolation integral. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def coefficientMoment {A : Type*} [CommRing A] [Algebra ℚ A] (p : A[X]) : A :=
  p.sum fun k a => a * algebraMap ℚ A (moment k)

theorem coefficientMoment_add {A : Type*} [CommRing A] [Algebra ℚ A] (p q : A[X]) :
    coefficientMoment (p + q) = coefficientMoment p + coefficientMoment q :=
  Polynomial.sum_add_index p q (fun k a => a * algebraMap ℚ A (moment k))
    (fun _ => by simp) (fun _ _ _ => add_mul _ _ _)

theorem coefficientMoment_monomial {A : Type*} [CommRing A] [Algebra ℚ A]
    (k : ℕ) (a : A) :
    coefficientMoment (Polynomial.monomial k a) = a * algebraMap ℚ A (moment k) :=
  Polynomial.sum_monomial_index a (fun k a => a * algebraMap ℚ A (moment k)) (by simp)

theorem coefficientMoment_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (p : A[X]) :
    coefficientMoment (p.map φ.toRingHom) = φ (coefficientMoment p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, coefficientMoment_add, coefficientMoment_add,
      map_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.map_monomial, coefficientMoment_monomial, map_mul, φ.commutes]
    rfl

theorem coefficientMoment_real (p : ℝ[X]) :
    coefficientMoment p = ∫ x in (-1 : ℝ)..1, p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [coefficientMoment_add, hp, hq]
    simp only [Polynomial.eval_add]
    exact (intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
      (q.continuous.intervalIntegrable _ _)).symm
  | monomial k a =>
    rw [coefficientMoment_monomial]
    simp only [Polynomial.eval_monomial]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [moment]

def algebraicDelta {A : Type*} [CommRing A] {n : ℕ} (nodes : Fin n → A) : A :=
  (Matrix.vandermonde nodes).det

theorem algebraicDelta_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A) :
    φ (algebraicDelta nodes) = algebraicDelta (fun i => φ (nodes i)) := by
  unfold algebraicDelta
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

def encodingDenominator {A : Type*} [CommRing A] {n : ℕ} (nodes : Fin n → A) : A :=
  algebraicDelta nodes ^ 2

def encodingNumerator {A : Type*} [CommRing A] [Algebra ℚ A]
    {n : ℕ} (nodes : Fin n → A) (scale : A) : A :=
  ∑ i, coefficientMoment (algebraicDelta
    (Function.update (fun j => Polynomial.C (nodes j)) i (Polynomial.C scale * Polynomial.X)) ^ 2)

theorem encodingDenominator_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A) :
    φ (encodingDenominator nodes) = encodingDenominator (fun i => φ (nodes i)) := by
  simp only [encodingDenominator, map_pow, algebraicDelta_map]

theorem polynomial_algebraicDelta_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A[X]) :
    (algebraicDelta nodes).map φ = algebraicDelta (fun i => (nodes i).map φ) :=
  algebraicDelta_map (Polynomial.mapRingHom φ) nodes

theorem encodingNumerator_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (φ : A →ₐ[ℚ] B)
    {n : ℕ} (nodes : Fin n → A) (scale : A) :
    φ (encodingNumerator nodes scale) =
      encodingNumerator (fun i => φ (nodes i)) (φ scale) := by
  unfold encodingNumerator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← coefficientMoment_map φ, Polynomial.map_pow, polynomial_algebraicDelta_map]
  apply congrArg coefficientMoment
  apply congrArg (fun p : B[X] => p ^ 2)
  apply congrArg algebraicDelta
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

theorem polynomial_delta_eval {n : ℕ} (nodes : Fin n → ℝ)
    (i : Fin n) (scale x : ℝ) :
    (algebraicDelta (Function.update (fun j => Polynomial.C (nodes j)) i
      (Polynomial.C scale * Polynomial.X))).eval x =
      delta (Function.update nodes i (scale * x)) := by
  have h := algebraicDelta_map (Polynomial.evalRingHom x)
    (Function.update (fun j => Polynomial.C (nodes j)) i (Polynomial.C scale * Polynomial.X))
  change _ = algebraicDelta _
  refine h.trans ?_
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

theorem encodingNumerator_real {n : ℕ} (nodes : Fin n → ℝ) (scale : ℝ) :
    encodingNumerator nodes scale =
      ∑ i, ∫ x in (-1 : ℝ)..1, delta (Function.update nodes i (scale * x)) ^ 2 := by
  unfold encodingNumerator
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficientMoment_real]
  simp only [Polynomial.eval_pow, polynomial_delta_eval]

theorem encodingNumerator_nonneg {n : ℕ} (nodes : Fin n → ℝ) (scale : ℝ) :
    0 ≤ encodingNumerator nodes scale := by
  rw [encodingNumerator_real]
  exact Finset.sum_nonneg (fun i hi =>
    intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _))

theorem encodingNumerator_affine {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) {scale : ℝ} (hscale : scale ≠ 0) :
    encodingNumerator (affineNodes nodes scale 0) scale =
      encodingDenominator (affineNodes nodes scale 0) * energy nodes := by
  have haffine : Function.Injective (affineNodes nodes scale 0) := by
    intro i j hij
    apply hinj
    exact mul_left_cancel₀ hscale (by simpa only [affineNodes, add_zero] using hij)
  have hcard (i : Fin n) (x : ℝ) :
      cardinal (affineNodes nodes scale 0) i (scale * x) = cardinal nodes i x := by
    simpa only [add_zero] using cardinal_affine nodes hscale 0 x i
  rw [encodingNumerator_real]
  simp_rw [delta_update haffine, hcard, mul_pow, intervalIntegral.integral_mul_const]
  rw [← Finset.sum_mul]
  have hint : ∀ i : Fin n, IntervalIntegrable
      (fun x => cardinal nodes i x ^ 2) volume (-1 : ℝ) 1 := by
    intro i
    exact ((cardinalPolynomial nodes i).continuous.pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  exact mul_comm _ _

end Erdos1131
