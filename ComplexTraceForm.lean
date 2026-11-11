import TraceNilpotents
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! A complex field factor contributes one positive and one negative square. -/

open Module

noncomputable section

namespace Erdos1131

def multiplicativeQuadratic {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (L : A →ₗ[R] R) : QuadraticForm R A :=
  LinearMap.BilinMap.toQuadraticMap (LinearMap.compr₂ (Algebra.lmul R A).toLinearMap L)

theorem multiplicativeQuadratic_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (L : A →ₗ[R] R) (x : A) : multiplicativeQuadratic L x = L (x * x) := rfl

theorem realLinear_complex_apply (L : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = L 1 * z.re + L Complex.I * z.im := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring

theorem complex_multiplicativeQuadratic_apply (L : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    multiplicativeQuadratic L z = L 1 * (z.re ^ 2 - z.im ^ 2) +
      2 * L Complex.I * z.re * z.im := by
  rw [multiplicativeQuadratic_apply, realLinear_complex_apply]
  simp only [Complex.mul_re, Complex.mul_im]
  ring

def complexDiagonalEquiv (a b : ℝ) : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.re + b / a * z.im, z.im]
  invFun u := ((u 0 - b / a * u 1 : ℝ) : ℂ) + (u 1 : ℂ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_add' z w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    ext i
    fin_cases i <;> simp <;> ring

def complexDiagonalWeights (a b : ℝ) : Fin 2 → ℝ := ![a, -(a + b ^ 2 / a)]

theorem complex_multiplicativeQuadratic_equivalent (L : ℂ →ₗ[ℝ] ℝ) (ha : L 1 ≠ 0) :
    QuadraticMap.Equivalent (multiplicativeQuadratic L)
      (QuadraticMap.weightedSumSquares ℝ (complexDiagonalWeights (L 1) (L Complex.I))) := by
  refine ⟨{ complexDiagonalEquiv (L 1) (L Complex.I) with map_app' := ?_ }⟩
  intro z
  rw [QuadraticMap.weightedSumSquares_apply, complex_multiplicativeQuadratic_apply]
  simp only [Fin.sum_univ_two, complexDiagonalWeights, complexDiagonalEquiv,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp
  ring

theorem complex_multiplicativeQuadratic_sigPos (L : ℂ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigPos (multiplicativeQuadratic L) = 1 := by
  classical
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (complex_multiplicativeQuadratic_equivalent L ha.ne')]
  have hnegative : -(L 1 + (L Complex.I) ^ 2 / L 1) < 0 := by
    have := div_nonneg (sq_nonneg (L Complex.I)) ha.le
    linarith
  have hset : {i : Fin 2 | 0 < complexDiagonalWeights (L 1) (L Complex.I) i} = {0} := by
    ext i
    fin_cases i <;> simp [complexDiagonalWeights, ha] <;> linarith
  rw [hset, Set.ncard_singleton]

theorem complex_multiplicativeQuadratic_sigNeg (L : ℂ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigNeg (multiplicativeQuadratic L) = 1 := by
  classical
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (complex_multiplicativeQuadratic_equivalent L ha.ne')]
  have hnegative : -(L 1 + (L Complex.I) ^ 2 / L 1) < 0 := by
    have := div_nonneg (sq_nonneg (L Complex.I)) ha.le
    linarith
  have hset : {i : Fin 2 | complexDiagonalWeights (L 1) (L Complex.I) i < 0} = {1} := by
    ext i
    fin_cases i <;> simp [complexDiagonalWeights, ha, not_lt_of_ge ha.le] <;> linarith
  rw [hset, Set.ncard_singleton]

end Erdos1131
