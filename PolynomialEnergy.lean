import NodeReindexing
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite coefficient coordinates for the interpolation energy. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def coefficientPolynomial {n : ℕ} (c : Fin n → ℝ) : ℝ[X] :=
  ∑ j, Polynomial.monomial j.val (c j)

theorem coefficientPolynomial_eval {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    (coefficientPolynomial c).eval x = ∑ j, c j * x ^ j.val := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem coefficientPolynomial_coeff {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    (coefficientPolynomial c).coeff j.val = c j := by
  classical
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

theorem coefficientPolynomial_degree_lt {n : ℕ} (c : Fin n → ℝ) :
    (coefficientPolynomial c).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ n).mpr
  intro j hj
  classical
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : i.val ≠ j := by
    have := i.isLt
    omega
  simp [Polynomial.coeff_monomial, hne]

theorem coefficientPolynomial_of_polynomial {n : ℕ} (p : ℝ[X]) (hp : p.degree < n) :
    coefficientPolynomial (fun j : Fin n => p.coeff j.val) = p := by
  ext j
  by_cases hj : j < n
  · exact coefficientPolynomial_coeff _ ⟨j, hj⟩
  · have hjn : n ≤ j := by omega
    rw [(Polynomial.degree_lt_iff_coeff_zero _ n).mp
      (coefficientPolynomial_degree_lt _) j hjn,
      (Polynomial.degree_lt_iff_coeff_zero _ n).mp hp j hjn]

theorem coefficientPolynomial_ne_zero {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) :
    coefficientPolynomial c ≠ 0 := by
  intro hp
  apply hc
  funext j
  have h := congrArg (fun p : ℝ[X] => p.coeff j.val) hp
  simpa only [coefficientPolynomial_coeff, Polynomial.coeff_zero, Pi.zero_apply] using h

theorem continuous_coefficientPolynomial_eval (n : ℕ) :
    Continuous (fun z : (Fin n → ℝ) × ℝ => (coefficientPolynomial z.fst).eval z.snd) := by
  simp only [coefficientPolynomial_eval]
  fun_prop

def rowEnergy {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (coefficientPolynomial c).eval x ^ 2

theorem rowEnergy_nonneg {n : ℕ} (c : Fin n → ℝ) : 0 ≤ rowEnergy c := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  positivity

theorem rowEnergy_pos {n : ℕ} (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) :
    0 < rowEnergy c := by
  have href := referenceNodes_admissible hn
  have hnonzero := coefficientPolynomial_ne_zero hc
  have hex : ∃ j : Fin n, (coefficientPolynomial c).eval (referenceNodes n j) ≠ 0 := by
    by_contra! h
    apply hnonzero
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ href.1.injOn
    · simpa only [Finset.card_univ, Fintype.card_fin] using coefficientPolynomial_degree_lt c
    · simp
    · intro j hj
      simp [h j]
  obtain ⟨j, hj⟩ := hex
  change 0 < ∫ x in (-1 : ℝ)..1, (coefficientPolynomial c).eval x ^ 2
  apply intervalIntegral.integral_pos (by norm_num)
    ((coefficientPolynomial c).continuous.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · exact ⟨referenceNodes n j, href.2 j, sq_pos_of_ne_zero hj⟩

theorem rowEnergy_eq_moments {n : ℕ} (c : Fin n → ℝ) :
    rowEnergy c = ∑ j, ∑ l, c j * c l *
      (∫ x in (-1 : ℝ)..1, x ^ (j.val + l.val)) := by
  classical
  have hterm (j l : Fin n) (x : ℝ) :
      (c j * x ^ j.val) * (c l * x ^ l.val) = c j * c l * x ^ (j.val + l.val) := by
    rw [pow_add]
    ring
  have hint (j l : Fin n) : IntervalIntegrable
      (fun x : ℝ => c j * c l * x ^ (j.val + l.val)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hintSum (j : Fin n) : IntervalIntegrable
      (fun x : ℝ => ∑ l, c j * c l * x ^ (j.val + l.val)) volume (-1) 1 := by
    have hfun : (∑ l : Fin n, fun x : ℝ => c j * c l * x ^ (j.val + l.val)) =
        (fun x : ℝ => ∑ l, c j * c l * x ^ (j.val + l.val)) := by
      funext x
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum Finset.univ (fun l _ => hint j l)
  unfold rowEnergy
  simp_rw [coefficientPolynomial_eval, pow_two, Finset.sum_mul_sum, hterm]
  rw [intervalIntegral.integral_finsetSum
    (f := fun j x => ∑ l, c j * c l * x ^ (j.val + l.val)) (fun j _ => hintSum j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_finsetSum
    (f := fun l x => c j * c l * x ^ (j.val + l.val)) (fun l _ => hint j l)]
  simp only [intervalIntegral.integral_const_mul]

def coefficientEnergy {n : ℕ} (c : Fin n → Fin n → ℝ) : ℝ := ∑ i, rowEnergy (c i)

theorem coefficientEnergy_nonneg {n : ℕ} (c : Fin n → Fin n → ℝ) :
    0 ≤ coefficientEnergy c := Finset.sum_nonneg (fun i _ => rowEnergy_nonneg (c i))

theorem coefficientEnergy_pos {n : ℕ} (hn : 0 < n) {c : Fin n → Fin n → ℝ} (hc : c ≠ 0) :
    0 < coefficientEnergy c := by
  have hi : ∃ i, c i ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => rowEnergy_nonneg (c j))
    ⟨i, Finset.mem_univ i, rowEnergy_pos hn hi⟩

theorem continuous_coefficientEnergy (n : ℕ) :
    Continuous (coefficientEnergy (n := n)) := by
  unfold coefficientEnergy
  simp_rw [rowEnergy_eq_moments]
  fun_prop

theorem coefficientEnergy_smul {n : ℕ} (r : ℝ) (c : Fin n → Fin n → ℝ) :
    coefficientEnergy (r • c) = r ^ 2 * coefficientEnergy c := by
  unfold coefficientEnergy
  simp_rw [rowEnergy_eq_moments, Pi.smul_apply, smul_eq_mul]
  have hterm (i j l : Fin n) (a : ℝ) :
      r * c i j * (r * c i l) * a = r ^ 2 * (c i j * c i l * a) := by ring
  simp_rw [hterm, ← Finset.mul_sum]

end Erdos1131
