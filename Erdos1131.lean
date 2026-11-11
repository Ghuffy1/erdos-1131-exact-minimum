import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Erdős problem 1131

The definitions in this file use arbitrary distinct real nodes in `[-1, 1]`,
unit cardinal weights, and ordinary Lebesgue measure.

The all-degree algebraic value rule is proved in `CompleteSolution.lean`.
The accompanying paper gives the mathematical construction and proof.
-/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def Admissible {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1) 1

def cardinalPolynomial {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes i

def cardinal {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  (cardinalPolynomial nodes i).eval x

def squareSumPolynomial {n : ℕ} (nodes : Fin n → ℝ) : ℝ[X] :=
  ∑ i, cardinalPolynomial nodes i ^ 2

def squareSum {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, cardinal nodes i x ^ 2

def energy {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, squareSum nodes x

def minimum (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v}

theorem cardinal_eq_product {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    cardinal nodes i x =
      ∏ j ∈ Finset.univ.erase i, (x - nodes j) / (nodes i - nodes j) := by
  simp only [cardinal, cardinalPolynomial, Lagrange.basis, Polynomial.eval_prod,
    Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem cardinal_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i j : Fin n) :
    cardinal nodes i (nodes j) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [cardinal, cardinalPolynomial]
    exact Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ i)
  · simp [cardinal, cardinalPolynomial, hij]

theorem sum_cardinal {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (x : ℝ) : ∑ i, cardinal nodes i x = 1 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hpoly := Lagrange.sum_basis hinj.injOn hne
  have heval := congrArg (Polynomial.eval x) hpoly
  simpa [cardinal, cardinalPolynomial, Polynomial.eval_finsetSum] using heval

theorem squareSum_eq_eval {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) :
    squareSum nodes x = (squareSumPolynomial nodes).eval x := by
  simp only [squareSum, squareSumPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, cardinal]

theorem continuous_squareSum {n : ℕ} (nodes : Fin n → ℝ) :
    Continuous (squareSum nodes) := by
  simpa only [← squareSum_eq_eval] using (squareSumPolynomial nodes).continuous

theorem intervalIntegrable_squareSum {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) :
    IntervalIntegrable (squareSum nodes) volume a b :=
  (continuous_squareSum nodes).intervalIntegrable a b

theorem squareSum_nonneg {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) :
    0 ≤ squareSum nodes x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (cardinal nodes i x)

theorem energy_nonneg {n : ℕ} (nodes : Fin n → ℝ) : 0 ≤ energy nodes := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact squareSum_nonneg nodes x

theorem squareSum_lower_bound {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (x : ℝ) :
    1 / (n : ℝ) ≤ squareSum nodes x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) (fun i => cardinal nodes i x)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sum_cardinal hn hinj, one_pow] at h
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  simpa [squareSum, mul_comm] using h

theorem energy_lower_bound {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) : 2 / (n : ℝ) ≤ energy nodes := by
  have h := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1)
    (f := fun _ => 1 / (n : ℝ)) (g := squareSum nodes) (by norm_num)
    (continuous_const.intervalIntegrable _ _) (intervalIntegrable_squareSum nodes _ _)
    (fun x _ => squareSum_lower_bound hn hinj x)
  norm_num [energy, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] at h ⊢
  exact h

theorem energy_one (nodes : Fin 1 → ℝ) : energy nodes = 2 := by
  have hb : ∀ i : Fin 1, cardinalPolynomial nodes i = 1 := by
    intro i
    fin_cases i
    simp [cardinalPolynomial, Lagrange.basis]
  norm_num [energy, squareSum, cardinal, hb, intervalIntegral.integral_const]

def referenceNodes (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ) / n

theorem referenceNodes_admissible {n : ℕ} (hn : 0 < n) :
    Admissible (referenceNodes n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · intro i j hij
    apply Fin.ext
    have hc : (i.val : ℝ) = j.val := by
      apply (div_left_inj' (ne_of_gt hnR)).mp
      exact hij
    exact_mod_cast hc
  · intro i
    constructor
    · have : (0 : ℝ) ≤ referenceNodes n i := div_nonneg (Nat.cast_nonneg _) hnR.le
      linarith
    · apply le_of_lt
      exact (div_lt_one hnR).2 (by exact_mod_cast i.isLt)

theorem attainableValues_nonempty {n : ℕ} (hn : 0 < n) :
    Set.Nonempty {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v} :=
  ⟨energy (referenceNodes n), referenceNodes n, referenceNodes_admissible hn, rfl⟩

theorem attainableValues_bddBelow (n : ℕ) :
    BddBelow {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v} := by
  refine ⟨0, ?_⟩
  rintro v ⟨nodes, _, rfl⟩
  exact energy_nonneg nodes

theorem minimum_le_energy {n : ℕ} {nodes : Fin n → ℝ}
    (h : Admissible nodes) : minimum n ≤ energy nodes := by
  exact csInf_le (attainableValues_bddBelow n) ⟨nodes, h, rfl⟩

theorem minimum_lower_bound {n : ℕ} (hn : 0 < n) : 2 / (n : ℝ) ≤ minimum n := by
  apply le_csInf (attainableValues_nonempty hn)
  rintro v ⟨nodes, h, rfl⟩
  exact energy_lower_bound hn h.1

theorem minimum_one : minimum 1 = 2 := by
  apply le_antisymm
  · simpa [energy_one] using minimum_le_energy (referenceNodes_admissible (by decide : 0 < 1))
  · simpa using minimum_lower_bound (by decide : 0 < 1)

/-! ## Rational polynomial moments -/

def moment (k : ℕ) : ℚ :=
  (1 - (-1 : ℚ) ^ (k + 1)) / (k + 1)

def polynomialMoment (p : ℚ[X]) : ℚ :=
  p.sum fun k a => a * moment k

theorem polynomialMoment_add (p q : ℚ[X]) :
    polynomialMoment (p + q) = polynomialMoment p + polynomialMoment q := by
  exact Polynomial.sum_add_index p q (fun k a => a * moment k)
    (fun _ => by simp) (fun _ _ _ => add_mul _ _ _)

theorem polynomialMoment_monomial (k : ℕ) (a : ℚ) :
    polynomialMoment (Polynomial.monomial k a) = a * moment k := by
  exact Polynomial.sum_monomial_index a (fun j b => b * moment j) (by simp)

theorem integral_mapped_rational_polynomial (p : ℚ[X]) :
    (polynomialMoment p : ℝ) =
      ∫ x in (-1 : ℝ)..1, (p.map (algebraMap ℚ ℝ)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [polynomialMoment_add, Rat.cast_add, hp, hq, Polynomial.map_add]
    simp only [Polynomial.eval_add]
    exact (intervalIntegral.integral_add
      ((p.map (algebraMap ℚ ℝ)).continuous.intervalIntegrable _ _)
      ((q.map (algebraMap ℚ ℝ)).continuous.intervalIntegrable _ _)).symm
  | monomial k a =>
    rw [polynomialMoment_monomial]
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial, Rat.cast_mul]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [moment]

def rationalCardinalSquareSum {n : ℕ} (nodes : Fin n → ℚ) : ℚ[X] :=
  ∑ i, Lagrange.basis Finset.univ nodes i ^ 2

def rationalEnergy {n : ℕ} (nodes : Fin n → ℚ) : ℚ :=
  polynomialMoment (rationalCardinalSquareSum nodes)

theorem map_rational_cardinal {n : ℕ} (nodes : Fin n → ℚ) (i : Fin n) :
    (Lagrange.basis Finset.univ nodes i).map (algebraMap ℚ ℝ) =
      cardinalPolynomial (fun j => (nodes j : ℝ)) i := by
  simp [cardinalPolynomial, Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod]

theorem map_rational_squareSum {n : ℕ} (nodes : Fin n → ℚ) :
    (rationalCardinalSquareSum nodes).map (algebraMap ℚ ℝ) =
      squareSumPolynomial (fun j => (nodes j : ℝ)) := by
  simp only [rationalCardinalSquareSum, Polynomial.map_sum, Polynomial.map_pow,
    map_rational_cardinal, squareSumPolynomial]

theorem rationalEnergy_eq_energy {n : ℕ} (nodes : Fin n → ℚ) :
    (rationalEnergy nodes : ℝ) = energy (fun j => (nodes j : ℝ)) := by
  rw [rationalEnergy, integral_mapped_rational_polynomial, map_rational_squareSum]
  simp_rw [energy, squareSum_eq_eval]

/-! ## Affine covariance of the cardinal functions -/

def affineNodes {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) : Fin n → ℝ :=
  fun i => a * nodes i + b

theorem cardinal_affine {n : ℕ} (nodes : Fin n → ℝ) {a : ℝ} (ha : a ≠ 0)
    (b x : ℝ) (i : Fin n) :
    cardinal (affineNodes nodes a b) i (a * x + b) = cardinal nodes i x := by
  rw [cardinal_eq_product, cardinal_eq_product]
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [affineNodes]
  rw [show a * x + b - (a * nodes j + b) = a * (x - nodes j) by ring]
  rw [show a * nodes i + b - (a * nodes j + b) = a * (nodes i - nodes j) by ring]
  exact mul_div_mul_left _ _ ha

theorem squareSum_affine {n : ℕ} (nodes : Fin n → ℝ) {a : ℝ} (ha : a ≠ 0)
    (b x : ℝ) :
    squareSum (affineNodes nodes a b) (a * x + b) = squareSum nodes x := by
  simp only [squareSum, cardinal_affine nodes ha]

theorem integral_squareSum_affine {n : ℕ} (nodes : Fin n → ℝ)
    {a : ℝ} (ha : a ≠ 0) (b left right : ℝ) :
    (∫ x in (a * left + b)..(a * right + b), squareSum (affineNodes nodes a b) x) =
      a * ∫ x in left..right, squareSum nodes x := by
  rw [← intervalIntegral.mul_integral_comp_mul_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact squareSum_affine nodes ha b x

end Erdos1131
