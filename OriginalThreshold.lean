import NodeReindexing
import FeketeUpper
import EndpointReduction
import EncodingHomogeneity

/-! Identification of the polynomial nonnegativity threshold with the original infimum. -/

noncomputable section

namespace Erdos1131

theorem orderedEndpoints_admissible {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) : Admissible nodes := by
  refine ⟨h.1.injective, fun i => ?_⟩
  constructor
  · have hi := h.1.monotone (Fin.zero_le i)
    simpa only [h.2.1] using hi
  · have hi := h.1.monotone (Fin.le_last i)
    simpa only [h.2.2] using hi

theorem expandedNodes_orderedEndpoints {k : ℕ} (hk : 0 < k)
    {nodes : Fin (k + 1) → ℝ} (hmono : StrictMono nodes) :
    OrderedEndpoints (expandedNodes nodes (nodes 0) (nodes (Fin.last k))) := by
  have hspan : nodes 0 < nodes (Fin.last k) := hmono (by exact_mod_cast hk)
  have hden : nodes (Fin.last k) - nodes 0 ≠ 0 := ne_of_gt (sub_pos.mpr hspan)
  have hscale : 0 < 2 / (nodes (Fin.last k) - nodes 0) :=
    div_pos (by norm_num) (sub_pos.mpr hspan)
  constructor
  · intro i j hij
    dsimp [expandedNodes, affineNodes]
    have hmul := mul_lt_mul_of_pos_left (hmono hij) hscale
    linarith
  constructor
  · dsimp [expandedNodes, affineNodes]
    ring
  · dsimp [expandedNodes, affineNodes]
    field_simp
    ring

theorem exists_orderedEndpoints_le_energy {k : ℕ} (hk : 0 < k)
    {nodes : Fin (k + 1) → ℝ} (hadm : Admissible nodes) (henergy : energy nodes < 2) :
    ∃ other : Fin (k + 1) → ℝ, OrderedEndpoints other ∧ energy other ≤ energy nodes := by
  obtain ⟨e, hmono⟩ := exists_strictMono_reindex hadm.1
  let ordered := nodes ∘ e
  have hordered : Admissible ordered := admissible_reindex hadm e
  have heq : energy ordered = energy nodes := energy_reindex hadm.1 e
  have hspan : ordered 0 < ordered (Fin.last k) := hmono (by exact_mod_cast hk)
  by_cases hshort : ordered (Fin.last k) - ordered 0 < 2
  · refine ⟨expandedNodes ordered (ordered 0) (ordered (Fin.last k)),
      expandedNodes_orderedEndpoints hk hmono, ?_⟩
    have hbetter := expandedNodes_improves_energy (by omega : 2 ≤ k + 1) hordered
      0 (Fin.last k) (fun i => hmono.monotone (Fin.zero_le i))
      (fun i => hmono.monotone (Fin.le_last i)) hspan hshort (heq ▸ henergy)
    exact hbetter.le.trans heq.le
  · have hleft : ordered 0 = -1 := by
      obtain ⟨h0lo, h0hi⟩ := hordered.2 0
      obtain ⟨h1lo, h1hi⟩ := hordered.2 (Fin.last k)
      linarith
    have hright : ordered (Fin.last k) = 1 := by
      obtain ⟨h0lo, h0hi⟩ := hordered.2 0
      obtain ⟨h1lo, h1hi⟩ := hordered.2 (Fin.last k)
      linarith
    exact ⟨ordered, ⟨hmono, hleft, hright⟩, heq.le⟩

def endpointValues (k : ℕ) : Set ℝ :=
  {v | ∃ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes ∧ energy nodes = v}

def endpointMinimum (k : ℕ) : ℝ := sInf (endpointValues k)

theorem exists_orderedEndpoints_energy_lt_two {k : ℕ} (hk : 0 < k) :
    ∃ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes ∧ energy nodes < 2 := by
  obtain ⟨nodes, hnodes⟩ := exists_fekete (Nat.succ_pos k)
  have henergy := fekete_energy_lt_two (by omega : 2 ≤ k + 1) hnodes
  obtain ⟨other, hother, hle⟩ := exists_orderedEndpoints_le_energy hk hnodes.1 henergy
  exact ⟨other, hother, lt_of_le_of_lt hle henergy⟩

theorem endpointValues_nonempty {k : ℕ} (hk : 0 < k) : (endpointValues k).Nonempty := by
  obtain ⟨nodes, hnodes, henergy⟩ := exists_orderedEndpoints_energy_lt_two hk
  exact ⟨energy nodes, nodes, hnodes, rfl⟩

theorem endpointValues_bddBelow (k : ℕ) : BddBelow (endpointValues k) := by
  refine ⟨0, ?_⟩
  rintro v ⟨nodes, hnodes, rfl⟩
  exact energy_nonneg nodes

theorem endpointMinimum_le_energy {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) : endpointMinimum k ≤ energy nodes :=
  csInf_le (endpointValues_bddBelow k) ⟨nodes, h, rfl⟩

theorem endpointMinimum_lt_two {k : ℕ} (hk : 0 < k) : endpointMinimum k < 2 := by
  obtain ⟨nodes, hnodes, henergy⟩ := exists_orderedEndpoints_energy_lt_two hk
  exact lt_of_le_of_lt (endpointMinimum_le_energy hnodes) henergy

theorem endpointMinimum_eq_minimum {k : ℕ} (hk : 0 < k) :
    endpointMinimum k = minimum (k + 1) := by
  apply le_antisymm
  · apply le_csInf (attainableValues_nonempty (Nat.succ_pos k))
    rintro value ⟨nodes, hnodes, rfl⟩
    by_cases hsmall : energy nodes < 2
    · obtain ⟨other, hother, hle⟩ := exists_orderedEndpoints_le_energy hk hnodes hsmall
      exact (endpointMinimum_le_energy hother).trans hle
    · exact (endpointMinimum_lt_two hk).le.trans (le_of_not_gt hsmall)
  · apply le_csInf (endpointValues_nonempty hk)
    rintro value ⟨nodes, hnodes, rfl⟩
    exact minimum_le_energy (orderedEndpoints_admissible hnodes)

theorem bound_all_orderedEndpoints_iff {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes) ↔
      t ≤ endpointMinimum k := by
  constructor
  · intro h
    apply le_csInf (endpointValues_nonempty hk)
    rintro value ⟨nodes, hnodes, rfl⟩
    exact h nodes hnodes
  · intro h nodes hnodes
    exact h.trans (endpointMinimum_le_energy hnodes)

theorem original_polynomial_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ u : Fin k → ℝ, 0 ≤ thresholdExpression k t u) ↔ t ≤ minimum (k + 1) := by
  rw [thresholdExpression_globally_nonnegative_iff hk t,
    bound_all_orderedEndpoints_iff hk t, endpointMinimum_eq_minimum hk]

theorem original_critical_point_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0} = {0} ↔
      t ≤ minimum (k + 1) := by
  rw [critical_points_singleton_iff_endpoint_bound hk t, bound_all_orderedEndpoints_iff hk t,
    endpointMinimum_eq_minimum hk]

end Erdos1131
