import InterpolationStates
import HomogeneousLowerBound

/-! The original interpolation infimum is attained at distinct nodes. -/

noncomputable section

namespace Erdos1131

theorem coefficientEnergy_lower_bound {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin n → Fin n → ℝ, c * ‖v‖ ^ 2 ≤ coefficientEnergy v :=
  positive_homogeneous_lower_bound coefficientEnergy (continuous_coefficientEnergy n)
    coefficientEnergy_smul (fun v hv => coefficientEnergy_pos hn hv)

theorem minimum_validState_exists {n : ℕ} (hn : 0 < n) :
    ∃ z : InterpolationState n, ValidInterpolationState z ∧
      ∀ w : InterpolationState n, ValidInterpolationState w →
        coefficientEnergy z.snd ≤ coefficientEnergy w.snd := by
  obtain ⟨z₀, hz₀⟩ := validStates_nonempty hn
  obtain ⟨c, hc, hlower⟩ := coefficientEnergy_lower_bound hn
  let E₀ := coefficientEnergy z₀.snd
  let B := max ‖z₀.snd‖ (E₀ / c + 1)
  have hE₀ : 0 ≤ E₀ := coefficientEnergy_nonneg z₀.snd
  have hB : 0 ≤ B := (norm_nonneg z₀.snd).trans (le_max_left _ _)
  have hB₁ : 1 ≤ B := by
    have hratio : 0 ≤ E₀ / c := div_nonneg hE₀ hc.le
    have hmax := le_max_right ‖z₀.snd‖ (E₀ / c + 1)
    dsimp only [B]
    linarith
  have hstrict : E₀ < c * B ^ 2 := by
    have hratio : c * (E₀ / c) = E₀ := by field_simp [ne_of_gt hc]
    have hmax : E₀ / c + 1 ≤ B := le_max_right _ _
    have hCB := mul_le_mul_of_nonneg_left hmax hc.le
    have hsq : B ≤ B ^ 2 := by nlinarith
    have hCBsq := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  let K : Set (InterpolationState n) :=
    (nodeBox n ×ˢ Metric.closedBall 0 B) ∩ {z | ValidInterpolationState z}
  have hcompact : IsCompact K :=
    ((isCompact_nodeBox n).prod (isCompact_closedBall (0 : Fin n → Fin n → ℝ) B)).inter_right
      (validInterpolationState_closed n)
  have hz₀K : z₀ ∈ K := by
    refine ⟨⟨hz₀.1, ?_⟩, hz₀⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_left ‖z₀.snd‖ (E₀ / c + 1)
  obtain ⟨z, hzK, hzmin⟩ := hcompact.exists_isMinOn ⟨z₀, hz₀K⟩
    ((continuous_coefficientEnergy n).comp continuous_snd).continuousOn
  refine ⟨z, hzK.2, ?_⟩
  intro w hw
  by_cases hwK : w ∈ K
  · exact hzmin hwK
  · have hwBall : w.snd ∉ Metric.closedBall 0 B := by
      intro hball
      exact hwK ⟨⟨hw.1, hball⟩, hw⟩
    have hwNorm : B < ‖w.snd‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hwBall
    have hsq : B ^ 2 ≤ ‖w.snd‖ ^ 2 := by nlinarith [norm_nonneg w.snd]
    have hout : E₀ < coefficientEnergy w.snd :=
      hstrict.trans_le ((mul_le_mul_of_nonneg_left hsq hc.le).trans (hlower w.snd))
    exact (hzmin hz₀K).trans hout.le

theorem minimum_attained (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = minimum n := by
  obtain ⟨z, hz, hmin⟩ := minimum_validState_exists hn
  refine ⟨z.fst, validState_admissible hz, le_antisymm ?_ (minimum_le_energy (validState_admissible hz))⟩
  unfold minimum
  apply le_csInf (attainableValues_nonempty hn)
  rintro v ⟨nodes, hnodes, henergy⟩
  have h := hmin (stateOfNodes nodes) (stateOfNodes_valid hnodes)
  rw [validState_energy hz, validState_energy (stateOfNodes_valid hnodes)] at h
  simpa only [stateOfNodes, henergy] using h

end Erdos1131
