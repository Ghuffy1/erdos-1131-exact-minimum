import GapEncoding

/-! Surjectivity of the squared-gap parametrization and its exact sign condition. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def sqrtGaps {k : ℕ} (nodes : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  Real.sqrt ((nodes i.succ - nodes i.castSucc) / 2)

theorem sqrtGaps_pos {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin k) : 0 < sqrtGaps nodes i := by
  apply Real.sqrt_pos.mpr
  apply div_pos _ (by norm_num)
  exact sub_pos.mpr (hmono (by exact_mod_cast Nat.lt_succ_self i.val))

theorem sqrtGaps_sq {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin k) :
    sqrtGaps nodes i ^ 2 = (nodes i.succ - nodes i.castSucc) / 2 := by
  apply Real.sq_sqrt
  apply div_nonneg _ (by norm_num)
  exact sub_nonneg.mpr (hmono.monotone (by exact_mod_cast Nat.le_succ i.val))

theorem gapTotal_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    gapTotal (sqrtGaps nodes) = 1 := by
  unfold gapTotal
  simp_rw [sqrtGaps_sq hmono]
  rw [← Finset.sum_div, sum_gap_differences, hleft, hright]
  norm_num

theorem gapPrefix_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin (k + 1)) :
    gapPrefix (fun j => sqrtGaps nodes j ^ 2) i = (nodes i - nodes 0) / 2 := by
  unfold gapPrefix
  simp_rw [sqrtGaps_sq hmono]
  rw [← Finset.sum_div]
  change gapPrefix (fun j => nodes j.succ - nodes j.castSucc) i / 2 = _
  rw [gapPrefix_differences]

theorem gapNodes_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    gapNodes (sqrtGaps nodes) = nodes := by
  funext i
  unfold gapNodes
  rw [gapTotal_sqrtGaps hmono hleft hright, gapPrefix_sqrtGaps hmono, hleft]
  ring

theorem normalizedGapNodes_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    normalizedGapNodes (sqrtGaps nodes) = nodes := by
  funext i
  unfold normalizedGapNodes
  rw [gapTotal_sqrtGaps hmono hleft hright, gapNodes_sqrtGaps hmono hleft hright, div_one]

theorem normalizedGapNodes_strictMono {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : StrictMono (normalizedGapNodes u) := by
  intro i j hij
  exact div_lt_div_of_pos_right (gapNodes_strictMono hu hij) (gapTotal_pos hk hu)

def OrderedEndpoints {k : ℕ} (nodes : Fin (k + 1) → ℝ) : Prop :=
  StrictMono nodes ∧ nodes 0 = -1 ∧ nodes (Fin.last k) = 1

theorem normalizedGapNodes_orderedEndpoints {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : OrderedEndpoints (normalizedGapNodes u) :=
  ⟨normalizedGapNodes_strictMono hk hu, normalizedGapNodes_endpoints hk hu⟩

theorem squared_gap_parametrization_surjective {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) :
    ∃ u : Fin k → ℝ, (∀ i, u i ≠ 0) ∧ normalizedGapNodes u = nodes := by
  exact ⟨sqrtGaps nodes, fun i => ne_of_gt (sqrtGaps_pos h.1 i),
    normalizedGapNodes_sqrtGaps h.1 h.2.1 h.2.2⟩

def thresholdExpression (k : ℕ) (t : ℝ) (u : Fin k → ℝ) : ℝ :=
  MvPolynomial.aeval u (numeratorPolynomial k) -
    t * MvPolynomial.aeval u (denominatorPolynomial k)

theorem denominatorPolynomial_eval_nonneg {k : ℕ} (u : Fin k → ℝ) :
    0 ≤ MvPolynomial.aeval u (denominatorPolynomial k) := by
  rw [denominatorPolynomial_eval]
  exact sq_nonneg _

theorem thresholdExpression_nonneg_iff {k : ℕ} (hk : 0 < k) (t : ℝ)
    {u : Fin k → ℝ} (hu : ∀ i, u i ≠ 0) :
    0 ≤ thresholdExpression k t u ↔ t ≤ energy (normalizedGapNodes u) := by
  have hD := (denominatorPolynomial_eval_pos_iff u).2 hu
  have hratio := numerator_div_denominator_eq_energy hk hu
  apply Iff.trans (sub_nonneg : _)
  constructor
  · intro h
    rw [← hratio]
    exact (le_div_iff₀ hD).2 h
  · intro h
    rw [← hratio] at h
    exact (le_div_iff₀ hD).1 h

theorem thresholdExpression_collision_nonneg {k : ℕ} (t : ℝ) (u : Fin k → ℝ)
    (hcollision : ¬ ∀ i, u i ≠ 0) : 0 ≤ thresholdExpression k t u := by
  have hnotpos : ¬ 0 < MvPolynomial.aeval u (denominatorPolynomial k) := by
    simpa only [denominatorPolynomial_eval_pos_iff] using hcollision
  have hzero : MvPolynomial.aeval u (denominatorPolynomial k) = 0 :=
    le_antisymm (le_of_not_gt hnotpos) (denominatorPolynomial_eval_nonneg u)
  simpa only [thresholdExpression, hzero, mul_zero, sub_zero]
    using numeratorPolynomial_eval_nonneg u

theorem thresholdExpression_globally_nonnegative_iff {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ u : Fin k → ℝ, 0 ≤ thresholdExpression k t u) ↔
      ∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes := by
  constructor
  · intro h nodes hnodes
    obtain ⟨u, hu, hparam⟩ := squared_gap_parametrization_surjective hnodes
    have hbound := (thresholdExpression_nonneg_iff hk t hu).1 (h u)
    simpa only [hparam] using hbound
  · intro h u
    by_cases hu : ∀ i, u i ≠ 0
    · exact (thresholdExpression_nonneg_iff hk t hu).2
        (h _ (normalizedGapNodes_orderedEndpoints hk hu))
    · exact thresholdExpression_collision_nonneg t u hu

end Erdos1131
