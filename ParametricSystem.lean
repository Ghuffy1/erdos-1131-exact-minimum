import OriginalThreshold
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Rational parameter coefficients and the normalized-gradient quotient. -/

open Polynomial

noncomputable section

namespace Erdos1131

abbrev ParameterRing := Polynomial ℚ

def clearedDegree (k : ℕ) : ℕ := 2 * ((k + 1) * k)

def liftRationalCoefficients {k : ℕ} :
    MvPolynomial (Fin k) ℚ →+* MvPolynomial (Fin k) ParameterRing :=
  MvPolynomial.map Polynomial.C

def parametricThreshold (k : ℕ) : MvPolynomial (Fin k) ParameterRing :=
  liftRationalCoefficients (numeratorPolynomial k) -
    MvPolynomial.C Polynomial.X * liftRationalCoefficients (denominatorPolynomial k)

def specializeParameter (t : ℝ) : ParameterRing →+* ℝ :=
  Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t

def evaluateParametricSystem {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    MvPolynomial (Fin k) ParameterRing →+* ℝ :=
  MvPolynomial.eval₂Hom (specializeParameter t) u

theorem evaluate_liftRationalCoefficients {k : ℕ} (t : ℝ) (u : Fin k → ℝ)
    (p : MvPolynomial (Fin k) ℚ) :
    evaluateParametricSystem t u (liftRationalCoefficients p) = MvPolynomial.aeval u p := by
  have hhom : (evaluateParametricSystem t u).comp liftRationalCoefficients =
      (MvPolynomial.aeval u).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evaluateParametricSystem, specializeParameter, liftRationalCoefficients]
    · intro i
      simp [evaluateParametricSystem, specializeParameter, liftRationalCoefficients]
  exact RingHom.congr_fun hhom p

theorem evaluate_parametricThreshold {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    evaluateParametricSystem t u (parametricThreshold k) = thresholdExpression k t u := by
  unfold parametricThreshold
  rw [map_sub, map_mul, evaluate_liftRationalCoefficients, evaluate_liftRationalCoefficients]
  simp [evaluateParametricSystem, specializeParameter, thresholdExpression]

def normalizedGradient (k : ℕ) (i : Fin k) : MvPolynomial (Fin k) ParameterRing :=
  MvPolynomial.X i ^ (clearedDegree k + 1) +
    MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)

def gradientIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) ParameterRing) :=
  Ideal.span (Set.range (normalizedGradient k))

abbrev GradientQuotient (k : ℕ) :=
  (MvPolynomial (Fin k) ParameterRing) ⧸ gradientIdeal k

end Erdos1131
