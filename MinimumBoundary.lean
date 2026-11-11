import SignatureContinuity
import NormalizedTrace
import BoundaryPolynomial

/-! The original minimum is a real root of the explicit boundary polynomial. -/

open Filter
open scoped Topology

noncomputable section

namespace Erdos1131

theorem continuous_specializeParameter (p : ParameterRing) :
    Continuous (fun t : ℝ => specializeParameter t p) := by
  convert (p.map (algebraMap ℚ ℝ)).continuous using 1
  ext t
  simp [specializeParameter, Polynomial.eval_map]

theorem continuous_specializedHermite_entry (k : ℕ)
    (a b : BoundedIndex k (clearedDegree k)) :
    Continuous (fun t : ℝ => specializedHermiteMatrix k (specializeParameter t) a b) := by
  simp only [specializedHermiteMatrix_eq_map, Matrix.map_apply]
  exact continuous_specializeParameter (parametricHermiteMatrix k a b)

theorem hermiteSignature_eventually_constant (k : ℕ) (t : ℝ) (ht : t ∉ boundaryRoots k) :
    ∀ᶠ s in 𝓝 t, matrixSignature (specializedHermiteMatrix k (specializeParameter s)) =
      matrixSignature (specializedHermiteMatrix k (specializeParameter t)) := by
  have hvalue : specializeParameter t (boundaryPolynomial k) ≠ 0 :=
    (mem_boundaryRoots k t).not.mp ht
  have hnonzero : ∀ᶠ s in 𝓝 t, specializeParameter s (boundaryPolynomial k) ≠ 0 :=
    (isOpen_ne.preimage (continuous_specializeParameter (boundaryPolynomial k))).mem_nhds hvalue
  apply matrixSignature_eventually_constant
    (fun s => specializedHermiteMatrix k (specializeParameter s))
    (continuous_specializedHermite_entry k)
    (fun s => specializedHermiteMatrix_isSymm k (specializeParameter s)) t
  filter_upwards [hnonzero] with s hs
  rw [specialized_charpoly_trailingDegree k (specializeParameter s) hs,
    specialized_charpoly_trailingDegree k (specializeParameter t) hvalue]

theorem minimum_mem_boundaryRoots {k : ℕ} (hk : 0 < k) :
    minimum (k + 1) ∈ boundaryRoots k := by
  by_contra hroot
  have hloc := hermiteSignature_eventually_constant k (minimum (k + 1)) hroot
  have hsig : matrixSignature
      (specializedHermiteMatrix k (specializeParameter (minimum (k + 1)))) = 1 :=
    (specializedHermite_signature_threshold hk _).mpr le_rfl
  have hle : ∀ᶠ s in 𝓝 (minimum (k + 1)), s ≤ minimum (k + 1) := by
    filter_upwards [hloc] with s hs
    exact (specializedHermite_signature_threshold hk s).mp (hs.trans hsig)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hle
  have hp : minimum (k + 1) + ε / 2 ∈ Metric.ball (minimum (k + 1)) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    rw [abs_of_pos (by positivity)]
    linarith
  have hbad := hball hp
  change minimum (k + 1) + ε / 2 ≤ minimum (k + 1) at hbad
  linarith

theorem minimum_in_open_interval {k : ℕ} (hk : 0 < k) :
    minimum (k + 1) ∈ Set.Ioo (0 : ℝ) 2 := by
  constructor
  · have hn : 0 < k + 1 := Nat.succ_pos _
    exact lt_of_lt_of_le (by positivity) (minimum_lower_bound hn)
  · exact minimum_lt_two (by omega)

end Erdos1131
