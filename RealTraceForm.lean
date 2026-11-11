import ComplexTraceForm

/-! A real field factor with positive trace weight contributes one positive square. -/

noncomputable section

namespace Erdos1131

theorem realLinear_real_apply (L : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : L x = L 1 * x := by
  have h := L.map_smul x 1
  simpa only [smul_eq_mul, mul_one, mul_comm] using h

theorem real_multiplicativeQuadratic_equivalent (L : ℝ →ₗ[ℝ] ℝ) :
    QuadraticMap.Equivalent (multiplicativeQuadratic L)
      (QuadraticMap.weightedSumSquares ℝ (fun _ : Unit => L 1)) := by
  refine ⟨{ (LinearEquiv.funUnique Unit ℝ ℝ).symm with map_app' := ?_ }⟩
  intro x
  rw [multiplicativeQuadratic_apply, realLinear_real_apply L (x * x)]
  simp [QuadraticMap.weightedSumSquares_apply, LinearEquiv.funUnique,
    mul_assoc]

theorem real_multiplicativeQuadratic_sigPos (L : ℝ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigPos (multiplicativeQuadratic L) = 1 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (real_multiplicativeQuadratic_equivalent L)]
  simp [ha]

theorem real_multiplicativeQuadratic_sigNeg (L : ℝ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigNeg (multiplicativeQuadratic L) = 0 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (real_multiplicativeQuadratic_equivalent L)]
  simp [not_lt_of_ge ha.le]

end Erdos1131
