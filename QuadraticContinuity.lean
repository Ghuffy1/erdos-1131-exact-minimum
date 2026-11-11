import QuadraticSurjection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

/-! Positive-definite restrictions persist under a continuous perturbation. -/

open Filter
open scoped Topology

noncomputable section

namespace Erdos1131

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem posDef_eventually (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) {x₀ : X}
    (hpos : (Q x₀).PosDef) : ∀ᶠ x in 𝓝 x₀, (Q x).PosDef := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : E) 1, 0 < Q x v := by
    apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hvne : v ≠ 0 := by
      intro hz
      simp [hz] at hv
    exact (isOpen_lt continuous_const hQ).mem_nhds (hpos v hvne)
  filter_upwards [hunit] with x hx
  intro v hv
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hu : u ∈ Metric.sphere (0 : E) 1 := by
    simp [u, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, hnorm]
  have hscale : ‖v‖ • u = v := by
    simp [u, smul_smul, hnorm]
  rw [← hscale, QuadraticMap.map_smul]
  exact smul_pos (mul_pos hnormpos hnormpos) (hx u hu)

theorem sigPos_eventually_ge (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, sigPos (Q x₀) ≤ sigPos (Q x) := by
  obtain ⟨V, hdim, hpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q x₀)
  have hrestrict : Continuous (fun z : X × V => (Q z.fst).restrict V z.snd) := by
    exact hQ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := posDef_eventually (fun x => (Q x).restrict V) hrestrict hpos
  filter_upwards [hp] with x hx
  rw [← hdim]
  exact le_sigPos_of_posDef (Q x) hx

theorem sigNeg_eventually_ge (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, sigNeg (Q x₀) ≤ sigNeg (Q x) := by
  have hneg : Continuous (fun z : X × E => (-Q z.fst) z.snd) := hQ.neg
  exact sigPos_eventually_ge (fun x => -Q x) hneg x₀

end Erdos1131
