import ParametricSystem
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Coordinate differentiation and the normalized-gradient equations. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def coordinateLine {k : ℕ} (u : Fin k → ℝ) (i : Fin k) (t : ℝ) : Fin k → ℝ :=
  u + t • Pi.single i 1

theorem coordinateLine_zero {k : ℕ} (u : Fin k → ℝ) (i : Fin k) :
    coordinateLine u i 0 = u := by simp [coordinateLine]

theorem coordinateLine_hasDerivAt {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) :
    HasDerivAt (fun t => coordinateLine u i t j) (if j = i then 1 else 0) 0 := by
  by_cases hji : j = i
  · subst j
    convert! (hasDerivAt_const (0 : ℝ) (u i)).add (hasDerivAt_id (0 : ℝ)) using 1 <;>
      simp [coordinateLine] <;> rfl
  · simpa [coordinateLine, Pi.single_apply, hji] using hasDerivAt_const (0 : ℝ) (u j)

theorem differentiable_eval₂ {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) :
    Differentiable ℝ (fun u : Fin k → ℝ => p.eval₂ φ u) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    fun_prop
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (by fun_prop)

theorem hasDerivAt_eval₂_coordinateLine {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) (i : Fin k) :
    HasDerivAt (fun t => p.eval₂ φ (coordinateLine u i t))
      ((MvPolynomial.pderiv i p).eval₂ φ u) 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero, MvPolynomial.eval₂_C]
      using hasDerivAt_const (0 : ℝ) (φ a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;>
      simp only [map_add, MvPolynomial.eval₂_add] <;> rfl
  | mul_X p j hp =>
    have hproduct := hp.mul (coordinateLine_hasDerivAt u i j)
    convert! hproduct using 1
    · ext t
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply]
    · by_cases hji : j = i
      · subst j
        simp [coordinateLine, mul_comm, add_comm]
      · simp [MvPolynomial.pderiv_X_of_ne hji, coordinateLine, hji, mul_comm]

theorem fderiv_eval₂_coordinate {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) (i : Fin k) :
    (fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u) (Pi.single i 1) =
      (MvPolynomial.pderiv i p).eval₂ φ u := by
  have hline := (differentiable_eval₂ φ p u).hasFDerivAt.hasLineDerivAt (Pi.single i 1)
  change HasDerivAt (fun t : ℝ => p.eval₂ φ (coordinateLine u i t))
    ((fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u) (Pi.single i 1)) 0 at hline
  exact hline.unique (hasDerivAt_eval₂_coordinateLine φ p u i)

theorem fderiv_eval₂_eq_zero_iff {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) :
    fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u = 0 ↔
      ∀ i, (MvPolynomial.pderiv i p).eval₂ φ u = 0 := by
  constructor
  · intro h i
    rw [← fderiv_eval₂_coordinate φ p u i, h]
    simp
  · intro h
    ext v
    have hv : v = ∑ i : Fin k, v i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply, smul_eq_mul]
    rw [hv, map_sum]
    simp [fderiv_eval₂_coordinate, h]

def augmentedPolynomial (k : ℕ) : MvPolynomial (Fin k) ParameterRing :=
  parametricThreshold k + ∑ i : Fin k, MvPolynomial.X i ^ (clearedDegree k + 2)

theorem evaluate_augmentedPolynomial {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    evaluateParametricSystem t u (augmentedPolynomial k) =
      HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t) u := by
  unfold augmentedPolynomial
  rw [map_add, evaluate_parametricThreshold, map_sum]
  have hdegree : clearedDegree k + 2 = 2 * ((k + 1) * k + 1) := by
    unfold clearedDegree
    omega
  simp only [map_pow, evaluateParametricSystem, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, HomogeneousLift.lift, HomogeneousLift.penalty, hdegree]

theorem pderiv_augmentedPolynomial {k : ℕ} (i : Fin k) :
    MvPolynomial.pderiv i (augmentedPolynomial k) =
      MvPolynomial.pderiv i (parametricThreshold k) +
        ((clearedDegree k + 2 : ℕ) : MvPolynomial (Fin k) ParameterRing) *
          MvPolynomial.X i ^ (clearedDegree k + 1) := by
  classical
  unfold augmentedPolynomial
  rw [map_add, map_sum]
  congr 1
  simp [MvPolynomial.pderiv_X, Pi.single_apply]

theorem evaluate_pderiv_augmentedPolynomial {k : ℕ} (t : ℝ) (u : Fin k → ℝ) (i : Fin k) :
    evaluateParametricSystem t u (MvPolynomial.pderiv i (augmentedPolynomial k)) =
      ((clearedDegree k + 2 : ℕ) : ℝ) * evaluateParametricSystem t u (normalizedGradient k i) := by
  have hcoefficient : evaluateParametricSystem t u
      (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹))) =
      (((clearedDegree k + 2 : ℕ) : ℝ)⁻¹) := by
    simp only [evaluateParametricSystem, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      specializeParameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    rw [map_inv₀, map_natCast]
  have hcoordinate : evaluateParametricSystem t u (MvPolynomial.X i) = u i := by
    simp [evaluateParametricSystem]
  rw [pderiv_augmentedPolynomial]
  unfold normalizedGradient
  simp only [map_add, map_mul, map_pow, map_natCast, hcoefficient, hcoordinate]
  have hdegree : ((clearedDegree k + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show clearedDegree k + 2 ≠ 0 by omega)
  field_simp
  ring

theorem normalizedGradient_zero_iff_critical {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    (∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0) ↔
      fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0 := by
  have hfunctions : (fun v : Fin k → ℝ => (augmentedPolynomial k).eval₂ (specializeParameter t) v) =
      HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t) := by
    funext v
    exact evaluate_augmentedPolynomial t v
  rw [← hfunctions, fderiv_eval₂_eq_zero_iff]
  have hdegree : (((clearedDegree k + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show clearedDegree k + 2 ≠ 0 by omega)
  change (∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0) ↔
    ∀ i, evaluateParametricSystem t u (MvPolynomial.pderiv i (augmentedPolynomial k)) = 0
  simp only [evaluate_pderiv_augmentedPolynomial, mul_eq_zero, hdegree, false_or]

theorem normalizedGradient_original_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | ∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0} = {0} ↔
      t ≤ minimum (k + 1) := by
  simp only [normalizedGradient_zero_iff_critical]
  exact original_critical_point_threshold hk t

end Erdos1131
