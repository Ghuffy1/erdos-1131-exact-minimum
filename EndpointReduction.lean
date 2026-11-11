import Fekete

/-! Affine expansion of a node hull and the corresponding integral estimates. -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem squareSum_left_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    {x : ℝ} (hx : x ≤ nodes i) : 1 ≤ squareSum nodes x := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · have hcard := cardinal_left_of_hull hn hinj i hmin hlt
    have hsum : cardinal nodes i x ^ 2 ≤ squareSum nodes x :=
      Finset.single_le_sum (fun j hj => sq_nonneg (cardinal nodes j x)) (Finset.mem_univ i)
    nlinarith
  · rw [squareSum]
    simp [cardinal_at_node hinj]

theorem squareSum_right_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    {x : ℝ} (hx : nodes i ≤ x) : 1 ≤ squareSum nodes x := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · have hcard := cardinal_right_of_hull hn hinj i hmax hlt
    have hsum : cardinal nodes i x ^ 2 ≤ squareSum nodes x :=
      Finset.single_le_sum (fun j hj => sq_nonneg (cardinal nodes j x)) (Finset.mem_univ i)
    nlinarith
  · rw [← heq, squareSum]
    simp [cardinal_at_node hinj]

theorem outside_left_integral_lower {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    (ha : -1 ≤ nodes i) :
    nodes i + 1 ≤ ∫ x in (-1 : ℝ)..nodes i, squareSum nodes x := by
  have hbound := intervalIntegral.integral_mono_on ha
    (continuous_const.intervalIntegrable (-1) (nodes i))
    (intervalIntegrable_squareSum nodes (-1) (nodes i))
    (fun x hx => squareSum_left_of_hull hn hinj i hmin hx.2)
  simpa only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul, mul_one]
    using hbound

theorem outside_right_integral_lower {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    (hb : nodes i ≤ 1) :
    1 - nodes i ≤ ∫ x in nodes i..(1 : ℝ), squareSum nodes x := by
  have hbound := intervalIntegral.integral_mono_on hb
    (continuous_const.intervalIntegrable (nodes i) 1)
    (intervalIntegrable_squareSum nodes (nodes i) 1)
    (fun x hx => squareSum_right_of_hull hn hinj i hmax hx.1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hbound

theorem hull_energy_decomposition {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) :
    (∫ x in (-1 : ℝ)..a, squareSum nodes x) +
      (∫ x in a..b, squareSum nodes x) +
      (∫ x in b..(1 : ℝ), squareSum nodes x) = energy nodes := by
  rw [intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_squareSum nodes (-1) a) (intervalIntegrable_squareSum nodes a b)]
  rw [intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_squareSum nodes (-1) b) (intervalIntegrable_squareSum nodes b 1)]
  rfl

def expandedNodes {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) : Fin n → ℝ :=
  affineNodes nodes (2 / (b - a)) (-1 - (2 / (b - a)) * a)

theorem expandedNodes_energy {n : ℕ} (nodes : Fin n → ℝ) {a b : ℝ} (hab : a < b) :
    energy (expandedNodes nodes a b) =
      (2 / (b - a)) * ∫ x in a..b, squareSum nodes x := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hscale : 2 / (b - a) ≠ 0 := div_ne_zero (by norm_num) hne
  have hleft : (2 / (b - a)) * a + (-1 - (2 / (b - a)) * a) = -1 := by ring
  have hright : (2 / (b - a)) * b + (-1 - (2 / (b - a)) * a) = 1 := by
    field_simp
    ring
  have h := integral_squareSum_affine nodes hscale (-1 - (2 / (b - a)) * a) a b
  rw [hleft, hright] at h
  exact h

theorem expandedNodes_admissible {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) {a b : ℝ} (hab : a < b)
    (hbox : ∀ i, a ≤ nodes i ∧ nodes i ≤ b) : Admissible (expandedNodes nodes a b) := by
  have hscale : 0 < 2 / (b - a) := div_pos (by norm_num) (sub_pos.mpr hab)
  constructor
  · intro i j hij
    apply hinj
    dsimp [expandedNodes, affineNodes] at hij
    exact mul_left_cancel₀ hscale.ne' (add_right_cancel hij)
  · intro i
    have hlower := mul_le_mul_of_nonneg_left (hbox i).1 hscale.le
    have hupper := mul_le_mul_of_nonneg_left (hbox i).2 hscale.le
    have hlength : (2 / (b - a)) * (b - a) = 2 :=
      div_mul_cancel₀ 2 (ne_of_gt (sub_pos.mpr hab))
    dsimp [expandedNodes, affineNodes]
    constructor <;> nlinarith

theorem expandedNodes_improves_energy {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hadm : Admissible nodes) (left right : Fin n)
    (hmin : ∀ i, nodes left ≤ nodes i) (hmax : ∀ i, nodes i ≤ nodes right)
    (hspan : nodes left < nodes right) (hshort : nodes right - nodes left < 2)
    (henergy : energy nodes < 2) :
    energy (expandedNodes nodes (nodes left) (nodes right)) < energy nodes := by
  have hL : 0 < nodes right - nodes left := sub_pos.mpr hspan
  have hleft := outside_left_integral_lower hn hadm.1 left hmin (hadm.2 left).1
  have hright := outside_right_integral_lower hn hadm.1 right hmax (hadm.2 right).2
  have hsplit := hull_energy_decomposition nodes (nodes left) (nodes right)
  have hinside : (∫ x in nodes left..nodes right, squareSum nodes x) < nodes right - nodes left := by
    linarith
  have hproduct := mul_pos (sub_pos.mpr hshort) (sub_pos.mpr hinside)
  have houtside := mul_nonneg hL.le (show 0 ≤
    (∫ x in (-1 : ℝ)..nodes left, squareSum nodes x) +
    (∫ x in nodes right..(1 : ℝ), squareSum nodes x) -
    (2 - (nodes right - nodes left)) by linarith)
  rw [expandedNodes_energy nodes hspan, div_mul_eq_mul_div]
  apply (div_lt_iff₀ hL).2
  nlinarith

end Erdos1131
