import Fekete
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Order.Interval.Set.Infinite

/-! Polynomial factorization behind the Fekete upper bound. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem nodal_dvd_of_eval_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s : Finset (Fin n)) {p : ℝ[X]}
    (hroot : ∀ i ∈ s, p.eval (nodes i) = 0) : Lagrange.nodal s nodes ∣ p := by
  unfold Lagrange.nodal
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C hinj hij
  · intro i hi
    exact Polynomial.dvd_iff_isRoot.mpr (hroot i hi)

theorem nodal_derivative_eval_ne_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    (Lagrange.nodal s nodes).derivative.eval (nodes i) ≠ 0 := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq hi]
  simp only [Lagrange.nodal, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hinj hij).symm

theorem double_nodal_dvd_of_eval_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s t : Finset (Fin n)) (hts : t ⊆ s) {p : ℝ[X]}
    (hroot : ∀ i ∈ s, p.eval (nodes i) = 0)
    (hderiv : ∀ i ∈ t, p.derivative.eval (nodes i) = 0) :
    Lagrange.nodal s nodes * Lagrange.nodal t nodes ∣ p := by
  obtain ⟨q, hp⟩ := nodal_dvd_of_eval_zero hinj s hroot
  have hqroot : ∀ i ∈ t, q.eval (nodes i) = 0 := by
    intro i hi
    have hd := hderiv i hi
    simp only [hp, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Lagrange.eval_nodal_at_node (hts hi), zero_mul, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left (nodal_derivative_eval_ne_zero hinj s (hts hi))
  obtain ⟨r, hq⟩ := nodal_dvd_of_eval_zero hinj t hqroot
  refine ⟨r, ?_⟩
  rw [hp, hq, mul_assoc]

theorem squareSum_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) : squareSum nodes (nodes i) = 1 := by
  simp [squareSum, cardinal_at_node hinj]

theorem squareSumPolynomial_natDegree_le {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    (squareSumPolynomial nodes).natDegree ≤ 2 * (n - 1) := by
  unfold squareSumPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [Polynomial.natDegree_pow, cardinalPolynomial,
    Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem fekete_nodal_factorization {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {left right : Fin n} (hleft : nodes left = -1)
    (hright : nodes right = 1) :
    squareSumPolynomial nodes - 1 =
      Polynomial.C (squareSumPolynomial nodes - 1).leadingCoeff *
        (Lagrange.nodal Finset.univ nodes *
          Lagrange.nodal ((Finset.univ.erase left).erase right) nodes) := by
  have hlr : left ≠ right := by
    intro heq
    have : (-1 : ℝ) = 1 := hleft.symm.trans (heq ▸ hright)
    norm_num at this
  let inside := (Finset.univ.erase left).erase right
  have hright_mem : right ∈ (Finset.univ : Finset (Fin n)).erase left := by
    simp [hlr.symm]
  have hdvd : Lagrange.nodal Finset.univ nodes * Lagrange.nodal inside nodes ∣
      squareSumPolynomial nodes - 1 := by
    apply double_nodal_dvd_of_eval_zero h.1.1 _ _ (by intro i hi; simp)
    · intro i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_one, ← squareSum_eq_eval,
        squareSum_at_node h.1.1, sub_self]
    · intro i hi
      have hir : i ≠ right := (Finset.mem_erase.mp hi).1
      have hil : i ≠ left := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hvleft : nodes i ≠ -1 := by
        intro hv
        exact hil (h.1.1 (hv.trans hleft.symm))
      have hvright : nodes i ≠ 1 := by
        intro hv
        exact hir (h.1.1 (hv.trans hright.symm))
      have hinside : nodes i ∈ Set.Ioo (-1) 1 :=
        ⟨lt_of_le_of_ne (h.1.2 i).1 hvleft.symm, lt_of_le_of_ne (h.1.2 i).2 hvright⟩
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero]
      exact fekete_squareSum_derivative_zero h i hinside
  have hmonic := (Lagrange.nodal_monic (s := Finset.univ) (v := nodes)).mul
    (Lagrange.nodal_monic (s := inside) (v := nodes))
  apply Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmonic hdvd
  have hdeg : (Lagrange.nodal Finset.univ nodes * Lagrange.nodal inside nodes).natDegree =
      n + (n - 2) := by
    rw [Polynomial.natDegree_mul (Lagrange.nodal_monic.ne_zero) (Lagrange.nodal_monic.ne_zero),
      Lagrange.natDegree_nodal, Lagrange.natDegree_nodal]
    simp only [inside, Finset.card_erase_of_mem hright_mem,
      Finset.card_erase_of_mem (Finset.mem_univ left), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hdeg]
  have hs := squareSumPolynomial_natDegree_le h.1.1
  have hp := Polynomial.natDegree_sub_le (squareSumPolynomial nodes) (1 : ℝ[X])
  simp only [Polynomial.natDegree_one] at hp
  omega

theorem nodal_two_erase_factorization {n : ℕ} (nodes : Fin n → ℝ)
    (left right : Fin n) (hlr : left ≠ right) :
    Lagrange.nodal Finset.univ nodes =
      (Polynomial.X - Polynomial.C (nodes left)) *
      (Polynomial.X - Polynomial.C (nodes right)) *
      Lagrange.nodal ((Finset.univ.erase left).erase right) nodes := by
  have hleft := Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun i => Polynomial.X - Polynomial.C (nodes i)) (Finset.mem_univ left)
  have hright_mem : right ∈ (Finset.univ : Finset (Fin n)).erase left := by
    simp [hlr.symm]
  have hright := Finset.mul_prod_erase (Finset.univ.erase left)
    (fun i => Polynomial.X - Polynomial.C (nodes i)) hright_mem
  unfold Lagrange.nodal
  rw [← hleft, ← hright]
  ring

theorem fekete_squareSum_factorization {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {left right : Fin n} (hleft : nodes left = -1)
    (hright : nodes right = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ,
      squareSum nodes x - 1 = c * (x + 1) * (x - 1) *
        ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x) ^ 2 := by
  have hlr : left ≠ right := by
    intro heq
    have : (-1 : ℝ) = 1 := hleft.symm.trans (heq ▸ hright)
    norm_num at this
  let c := (squareSumPolynomial nodes - 1).leadingCoeff
  have hpoly := fekete_nodal_factorization hn h hleft hright
  rw [nodal_two_erase_factorization nodes left right hlr] at hpoly
  have hvalue (x : ℝ) : squareSum nodes x - 1 = c * (x + 1) * (x - 1) *
      ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x) ^ 2 := by
    have heval := congrArg (Polynomial.eval x) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, hleft, hright, ← squareSum_eq_eval] at heval
    dsimp [c]
    nlinarith [heval]
  refine ⟨c, ?_, hvalue⟩
  have hcard : 1 < cardinal nodes left (-2) := by
    apply cardinal_left_of_hull hn h.1.1 left
    · intro j
      rw [hleft]
      exact (h.1.2 j).1
    · rw [hleft]
      norm_num
  have hsum : cardinal nodes left (-2) ^ 2 ≤ squareSum nodes (-2) :=
    Finset.single_le_sum (fun i hi => sq_nonneg (cardinal nodes i (-2))) (Finset.mem_univ left)
  have hpositive : 0 < squareSum nodes (-2) - 1 := by nlinarith
  have hv := hvalue (-2)
  by_contra hc
  have hc0 : c ≤ 0 := le_of_not_gt hc
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hc0
    (sq_nonneg ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval (-2)))
  nlinarith

theorem fekete_squareSum_le_one {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : squareSum nodes x ≤ 1 := by
  obtain ⟨left, hleft⟩ := (fekete_contains_endpoints hn h).1
  obtain ⟨right, hright⟩ := (fekete_contains_endpoints hn h).2
  obtain ⟨c, hc, hvalue⟩ := fekete_squareSum_factorization hn h hleft hright
  have hleft_nonneg : 0 ≤ x + 1 := by linarith [hx.1]
  have hright_nonpos : x - 1 ≤ 0 := by linarith [hx.2]
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hleft_nonneg) hright_nonpos)
    (sq_nonneg ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x))
  have hv := hvalue x
  linarith

theorem fekete_squareSum_lt_one_off_nodes {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1)
    (hnotnode : ∀ i, x ≠ nodes i) : squareSum nodes x < 1 := by
  obtain ⟨left, hleft⟩ := (fekete_contains_endpoints hn h).1
  obtain ⟨right, hright⟩ := (fekete_contains_endpoints hn h).2
  obtain ⟨c, hc, hvalue⟩ := fekete_squareSum_factorization hn h hleft hright
  have hnodal : (Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x ≠ 0 := by
    exact Lagrange.eval_nodal_not_at_node (fun i hi => hnotnode i)
  have hleft_pos : 0 < x + 1 := by linarith [hx.1]
  have hright_neg : x - 1 < 0 := by linarith [hx.2]
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos hc hleft_pos) hright_neg)
    (sq_pos_of_ne_zero hnodal)
  have hv := hvalue x
  linarith

theorem fekete_energy_lt_two {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) : energy nodes < 2 := by
  obtain ⟨x, hx, hnot⟩ := (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).exists_notMem_finset
    (Finset.univ.image nodes)
  have hnotnode : ∀ i, x ≠ nodes i := by
    intro i heq
    exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩)
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (-1 : ℝ) < 1) (continuous_squareSum nodes).continuousOn
    (continuous_const (y := (1 : ℝ))).continuousOn
    (fun y hy => fekete_squareSum_le_one hn h ⟨hy.1.le, hy.2⟩)
    ⟨x, ⟨hx.1.le, hx.2.le⟩, fekete_squareSum_lt_one_off_nodes hn h hx hnotnode⟩
  simpa only [energy, intervalIntegral.integral_const, sub_neg_eq_add, one_add_one_eq_two,
    smul_eq_mul, mul_one] using hstrict

theorem minimum_lt_two {n : ℕ} (hn : 2 ≤ n) : minimum n < 2 := by
  obtain ⟨nodes, hnodes⟩ := exists_fekete (by omega : 0 < n)
  exact lt_of_le_of_lt (minimum_le_energy hnodes.1) (fekete_energy_lt_two hn hnodes)

end Erdos1131
