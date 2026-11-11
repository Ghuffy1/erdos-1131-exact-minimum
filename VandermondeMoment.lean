import Erdos1131
import Mathlib.LinearAlgebra.Vandermonde

/-! Vandermonde identities linking the numerator construction to the original integral. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem lagrange_reproduces_monomial {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (j : Fin n) (x : ℝ) :
    x ^ j.val = ∑ i, cardinal nodes i x * nodes i ^ j.val := by
  have hdegree : ((X : ℝ[X]) ^ j.val).degree <
      (Finset.univ : Finset (Fin n)).card := by
    simp only [degree_X_pow, Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
      WithBot.coe_lt_coe]
    exact j.isLt
  have h := Lagrange.eq_interpolate hinj.injOn hdegree
  have heval := congrArg (Polynomial.eval x) h
  simpa [Lagrange.interpolate_apply, cardinal, cardinalPolynomial,
    Polynomial.eval_finsetSum, mul_comm] using heval

def delta {n : ℕ} (nodes : Fin n → ℝ) : ℝ := (Matrix.vandermonde nodes).det

theorem delta_eq_product {n : ℕ} (nodes : Fin n → ℝ) :
    delta nodes = ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (nodes j - nodes i) := by
  have hsets : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    intro i
    ext j
    simp
  simpa only [delta, hsets] using Matrix.det_vandermonde nodes

theorem delta_ne_zero_iff {n : ℕ} (nodes : Fin n → ℝ) :
    delta nodes ≠ 0 ↔ Function.Injective nodes := Matrix.det_vandermonde_ne_zero_iff

theorem delta_update {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (x : ℝ) :
    delta (Function.update nodes i x) = cardinal nodes i x * delta nodes := by
  have hrow : (fun j : Fin n => x ^ j.val) =
      ∑ k, cardinal nodes k x • Matrix.vandermonde nodes k := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vandermonde_apply]
      using lagrange_reproduces_monomial hinj j x
  have hmatrix : Matrix.vandermonde (Function.update nodes i x) =
      (Matrix.vandermonde nodes).updateRow i (fun j => x ^ j.val) := by
    ext a b
    by_cases hai : a = i
    · subst a
      rw [Matrix.updateRow_self]
      simp only [Matrix.vandermonde_apply, Function.update_self]
    · rw [Matrix.updateRow_ne hai]
      simp only [Matrix.vandermonde_apply, Function.update_of_ne hai]
  unfold delta
  rw [hmatrix, hrow, Matrix.det_updateRow_sum, smul_eq_mul]

def denominator {n : ℕ} (nodes : Fin n → ℝ) : ℝ := delta nodes ^ 2

def integralNumerator {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ x in (-1 : ℝ)..1, delta (Function.update nodes i x) ^ 2

theorem denominator_nonneg {n : ℕ} (nodes : Fin n → ℝ) :
    0 ≤ denominator nodes := sq_nonneg _

theorem denominator_pos_iff {n : ℕ} (nodes : Fin n → ℝ) :
    0 < denominator nodes ↔ Function.Injective nodes := by
  rw [denominator, sq_pos_iff, delta_ne_zero_iff]

theorem integralNumerator_nonneg {n : ℕ} (nodes : Fin n → ℝ) :
    0 ≤ integralNumerator nodes := by
  apply Finset.sum_nonneg
  intro i hi
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _)

theorem integralNumerator_eq_energy {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    integralNumerator nodes = denominator nodes * energy nodes := by
  unfold integralNumerator
  simp_rw [delta_update hinj, mul_pow]
  have hint : ∀ i : Fin n, IntervalIntegrable
      (fun x => cardinal nodes i x ^ 2) volume (-1 : ℝ) 1 := by
    intro i
    exact ((cardinalPolynomial nodes i).continuous.pow 2).intervalIntegrable _ _
  simp_rw [intervalIntegral.integral_mul_const]
  rw [← Finset.sum_mul]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  exact mul_comm _ _

end Erdos1131
