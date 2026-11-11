import QuadraticContinuity

/-! A positive homogeneous quadratic function controls the coefficient norm. -/

noncomputable section

namespace Erdos1131

theorem positive_homogeneous_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : E → ℝ) (hcontinuous : Continuous p)
    (hhom : ∀ r : ℝ, ∀ x, p (r • x) = r ^ 2 * p x)
    (hpos : ∀ x, x ≠ 0 → 0 < p x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ p x := by
  have hzero : p 0 = 0 := by
    simpa using hhom 0 (0 : E)
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
    refine ⟨1, by norm_num, ?_⟩
    intro x
    rw [Subsingleton.elim x 0, norm_zero, hzero]
    norm_num
  | inr hnontrivial =>
    letI : ProperSpace E := FiniteDimensional.proper ℝ E
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    have hnormz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hzunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp [norm_smul, norm_inv, hnormz]
    obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      ⟨_, hzunit⟩ hcontinuous.continuousOn
    have hyne : y ≠ 0 := by
      intro h
      simp [h] at hy
    refine ⟨p y, hpos y hyne, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, hzero]
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let u : E := ‖x‖⁻¹ • x
      have hu : u ∈ Metric.sphere (0 : E) 1 := by
        simp [u, norm_smul, norm_inv, hnorm]
      have hscale : ‖x‖ • u = x := by
        simp [u, smul_smul, hnorm]
      have hpx : p x = ‖x‖ ^ 2 * p u := by
        rw [← hscale, hhom]
        rw [hscale]
      rw [hpx, mul_comm (p y)]
      exact mul_le_mul_of_nonneg_left (hmin hu) (sq_nonneg ‖x‖)

end Erdos1131
