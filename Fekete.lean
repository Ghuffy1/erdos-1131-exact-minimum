import VandermondeMoment
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.Compact

/-! The compact Vandermonde maximization used to obtain a strict upper bound. -/

open Polynomial
open scoped BigOperators Topology

noncomputable section

namespace Erdos1131

def nodeBox (n : ℕ) : Set (Fin n → ℝ) :=
  {nodes | ∀ i, nodes i ∈ Set.Icc (-1) 1}

theorem nodeBox_eq_Icc (n : ℕ) : nodeBox n = Set.Icc (-1) 1 := by
  ext nodes
  simp only [nodeBox, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def,
    Pi.neg_apply, Pi.one_apply]
  exact forall_and

theorem isCompact_nodeBox (n : ℕ) : IsCompact (nodeBox n) := by
  rw [nodeBox_eq_Icc]
  exact isCompact_Icc

theorem continuous_delta (n : ℕ) : Continuous (delta (n := n)) := by
  change Continuous (fun nodes : Fin n → ℝ => delta nodes)
  simp_rw [delta_eq_product]
  fun_prop

theorem continuous_denominator (n : ℕ) : Continuous (denominator (n := n)) :=
  (continuous_delta n).pow 2

def IsFekete {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Admissible nodes ∧ ∀ other ∈ nodeBox n, denominator other ≤ denominator nodes

theorem exists_fekete {n : ℕ} (hn : 0 < n) : ∃ nodes : Fin n → ℝ, IsFekete nodes := by
  have href : referenceNodes n ∈ nodeBox n := (referenceNodes_admissible hn).2
  obtain ⟨nodes, hnodes, hmax⟩ := (isCompact_nodeBox n).exists_isMaxOn
    ⟨referenceNodes n, href⟩ (continuous_denominator n).continuousOn
  have hpositive : 0 < denominator nodes :=
    lt_of_lt_of_le ((denominator_pos_iff _).2 (referenceNodes_admissible hn).1) (hmax href)
  exact ⟨nodes, ⟨(denominator_pos_iff _).1 hpositive, hnodes⟩, hmax⟩

theorem fekete_cardinal_sq_le_one {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    cardinal nodes i x ^ 2 ≤ 1 := by
  have hreplace : Function.update nodes i x ∈ nodeBox n := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hx
    · simpa only [Function.update_of_ne hji] using h.1.2 j
  have hmax := h.2 (Function.update nodes i x) hreplace
  have hpos := (denominator_pos_iff nodes).2 h.1.1
  simp only [denominator, delta_update h.1.1, mul_pow] at hmax hpos
  nlinarith

theorem one_lt_prod_real {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i ∈ s, f i := by
  simpa using Finset.prod_lt_prod_of_nonempty₀ (s := s) (f := fun _ => (1 : ℝ))
    (g := f) (fun _ _ => by norm_num) hf hs

theorem cardinal_left_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    {x : ℝ} (hx : x < nodes i) : 1 < cardinal nodes i x := by
  rw [cardinal_eq_product]
  apply one_lt_prod_real
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hlt : nodes i < nodes j := lt_of_le_of_ne (hmin j) (by
      intro heq
      exact hji (hinj heq).symm)
    apply (one_lt_div_of_neg (sub_neg.mpr hlt)).2
    linarith
  · apply Finset.card_pos.mp
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] using (show 0 < n - 1 by omega)

theorem cardinal_right_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    {x : ℝ} (hx : nodes i < x) : 1 < cardinal nodes i x := by
  rw [cardinal_eq_product]
  apply one_lt_prod_real
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hlt : nodes j < nodes i := lt_of_le_of_ne (hmax j) (by
      intro heq
      exact hji (hinj heq))
    apply (one_lt_div (sub_pos.mpr hlt)).2
    linarith
  · apply Finset.card_pos.mp
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] using (show 0 < n - 1 by omega)

theorem fekete_contains_endpoints {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) : (∃ i, nodes i = -1) ∧ (∃ i, nodes i = 1) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  constructor
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ nodes hnonempty
    refine ⟨i, le_antisymm ?_ (h.1.2 i).1⟩
    by_contra hle
    have houtside := cardinal_left_of_hull hn h.1.1 i
      (fun j => hmin j (Finset.mem_univ j)) (lt_of_not_ge hle)
    have hbound := fekete_cardinal_sq_le_one h i (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1)
    nlinarith
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ nodes hnonempty
    refine ⟨i, le_antisymm (h.1.2 i).2 ?_⟩
    by_contra hle
    have houtside := cardinal_right_of_hull hn h.1.1 i
      (fun j => hmax j (Finset.mem_univ j)) (lt_of_not_ge hle)
    have hbound := fekete_cardinal_sq_le_one h i (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1)
    nlinarith

theorem fekete_cardinal_derivative_zero {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) (hi : nodes i ∈ Set.Ioo (-1) 1) :
    (cardinalPolynomial nodes i).derivative.eval (nodes i) = 0 := by
  have hself : cardinal nodes i (nodes i) = 1 := by
    simpa using cardinal_at_node h.1.1 i i
  have hlocal : IsLocalMax (fun x => cardinal nodes i x ^ 2) (nodes i) := by
    filter_upwards [Icc_mem_nhds hi.1 hi.2] with x hx
    simpa only [hself, one_pow] using fekete_cardinal_sq_le_one h i hx
  have hlocal' : IsLocalMax
      (fun x => (cardinalPolynomial nodes i ^ 2).eval x) (nodes i) := by
    simpa only [Polynomial.eval_pow, cardinal] using hlocal
  have hzero := hlocal'.hasDerivAt_eq_zero
    ((cardinalPolynomial nodes i ^ 2).hasDerivAt (nodes i))
  have hself' : (cardinalPolynomial nodes i).eval (nodes i) = 1 := hself
  simpa [Polynomial.derivative_pow, hself'] using hzero

theorem squareSumPolynomial_derivative_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) :
    (squareSumPolynomial nodes).derivative.eval (nodes i) =
      2 * (cardinalPolynomial nodes i).derivative.eval (nodes i) := by
  classical
  simp only [squareSumPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  trans ∑ j, 2 * cardinal nodes j (nodes i) *
      (cardinalPolynomial nodes j).derivative.eval (nodes i)
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Polynomial.derivative_pow, cardinal]
  · simp [cardinal_at_node hinj]

theorem fekete_squareSum_derivative_zero {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) (hi : nodes i ∈ Set.Ioo (-1) 1) :
    (squareSumPolynomial nodes).derivative.eval (nodes i) = 0 := by
  rw [squareSumPolynomial_derivative_at_node h.1.1,
    fekete_cardinal_derivative_zero h i hi, mul_zero]

end Erdos1131
