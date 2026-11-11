/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.Definitions
import Erdos1131Asymptotic.ChebyshevMoment
import Erdos1131Asymptotic.ChebyshevBound

/-!
# Interpolation in the Chebyshev basis

This file connects the Lagrange functional to the finite Chebyshev matrices.
Rows of `chebEvalMatrix x` are nodes and columns are Chebyshev degrees.
-/

open scoped BigOperators Interval Matrix
open Polynomial

namespace Erdos1131Asymptotic

namespace InterpolationTrace

open Polynomial.Chebyshev

noncomputable section

/-- Evaluation of `T₀, ..., T_{n-1}` at the nodes `x`. -/
def chebEvalMatrix {n : ℕ} (x : Fin n ↪ ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (T ℝ (j.val : ℤ)).eval (x i)

/-- The actual (unweighted) integral Gram matrix of `T₀, ..., T_{n-1}`. -/
def integralGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    ∫ t in (-1 : ℝ)..1,
      (T ℝ (i.val : ℤ)).eval t * (T ℝ (j.val : ℤ)).eval t

/-- A coefficient vector interpreted in the Chebyshev basis. -/
def chebExpansion {n : ℕ} (c : Fin n → ℝ) : ℝ[X] :=
  ∑ j : Fin n, C (c j) * T ℝ (j.val : ℤ)

theorem chebEvalMatrix_det_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) :
    (chebEvalMatrix x).det ≠ 0 := by
  let p : Fin n → ℝ[X] := fun j ↦ T ℝ (j.val : ℤ)
  have hdeg : ∀ j, (p j).natDegree ≤ j.val := by
    intro j
    simp [p]
  have hfactor :=
    Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
      (x : Fin n → ℝ) p hdeg
  have hvander :
      (Matrix.vandermonde (x : Fin n → ℝ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr x.injective
  have hcoeff :
      (Matrix.of (fun (i j : Fin n) ↦ (p j).coeff i.val)).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular p hdeg)]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simp only [Matrix.of_apply]
    have hjdeg : (p j).natDegree = j.val := by simp [p]
    rw [← hjdeg, coeff_natDegree]
    simp only [p, leadingCoeff_T]
    positivity
  have hdet := congrArg Matrix.det hfactor
  change (chebEvalMatrix x).det =
    (Matrix.vandermonde (x : Fin n → ℝ) *
      Matrix.of (fun (i j : Fin n) ↦ (p j).coeff i.val)).det at hdet
  rw [Matrix.det_mul] at hdet
  rw [hdet]
  exact mul_ne_zero hvander hcoeff

/-- Distinct nodes make the Chebyshev evaluation matrix invertible. -/
theorem chebEvalMatrix_isUnit_det {n : ℕ} (x : Fin n ↪ ℝ) :
    IsUnit (chebEvalMatrix x).det :=
  isUnit_iff_ne_zero.mpr (chebEvalMatrix_det_ne_zero x)

/-- Every finite Chebyshev expansion indexed by `Fin n` has degree `< n`. -/
theorem degree_chebExpansion_lt {n : ℕ} (c : Fin n → ℝ) :
    (chebExpansion c).degree < (n : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 ?_
  intro j _
  calc
    (C (c j) * T ℝ (j.val : ℤ)).degree
        ≤ (C (c j)).degree + (T ℝ (j.val : ℤ)).degree :=
      degree_mul_le _ _
    _ ≤ 0 + (j.val : WithBot ℕ) := by
      gcongr
      · exact degree_C_le
      · simp
    _ < (n : WithBot ℕ) := by
      rw [zero_add]
      exact_mod_cast j.isLt

/-- The `k`th Lagrange polynomial has as its Chebyshev coefficients the
`k`th column of the inverse evaluation matrix. -/
theorem lagrange_basis_eq_chebExpansion {n : ℕ}
    (x : Fin n ↪ ℝ) (k : Fin n) :
    Lagrange.basis Finset.univ (x : Fin n → ℝ) k =
      chebExpansion (fun j ↦ (chebEvalMatrix x)⁻¹ j k) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨k⟩
  have hbdeg :
      (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).degree <
        (n : WithBot ℕ) := by
    rw [Lagrange.degree_basis x.injective.injOn (Finset.mem_univ k)]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
      WithBot.coe_lt_coe]
    exact Nat.sub_lt hn zero_lt_one
  have hedeg :
      (chebExpansion (fun j ↦ (chebEvalMatrix x)⁻¹ j k)).degree <
        (n : WithBot ℕ) :=
    degree_chebExpansion_lt (fun j ↦ (chebEvalMatrix x)⁻¹ j k)
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    x.injective.injOn (by simpa using hbdeg) (by simpa using hedeg) ?_
  intro i _
  have hmul := Matrix.mul_nonsing_inv (chebEvalMatrix x)
    (chebEvalMatrix_isUnit_det x)
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i k) hmul
  change (chebEvalMatrix x * (chebEvalMatrix x)⁻¹) i k =
    (1 : Matrix (Fin n) (Fin n) ℝ) i k at hentry
  have hbasis :
      (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x i) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i k := by
    simp only [Matrix.one_apply]
    by_cases hik : i = k
    · subst i
      rw [if_pos rfl, basis_eval_self]
    · rw [if_neg hik, basis_eval_of_ne x hik]
  rw [hbasis, ← hentry]
  simp only [Matrix.mul_apply, chebEvalMatrix, chebExpansion,
    eval_finset_sum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Squaring removes the orientation in `Nat.dist`. -/
lemma natCast_dist_sq (a b : ℕ) :
    ((a.dist b : ℕ) : ℝ) ^ 2 = ((a : ℝ) - (b : ℝ)) ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab]
    ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba, Nat.cast_sub hba]

lemma even_add_iff_sameParity (a b : ℕ) :
    Even (a + b) ↔ ChebyshevBound.SameParity a b := by
  simp [ChebyshevBound.SameParity, Nat.even_iff]
  omega

lemma two_mul_half_add_of_sameParity {a b : ℕ}
    (h : ChebyshevBound.SameParity a b) :
    2 * ((a + b) / 2) = a + b := by
  apply Nat.two_mul_div_two_of_even
  exact (even_add_iff_sameParity a b).mpr h

lemma two_mul_half_dist_of_sameParity {a b : ℕ}
    (h : ChebyshevBound.SameParity a b) :
    2 * (a.dist b / 2) = a.dist b := by
  apply Nat.two_mul_div_two_of_even
  have heab : Even a ↔ Even b := by
    simp [ChebyshevBound.SameParity, Nat.even_iff] at h ⊢
    omega
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.even_sub hab).2 heab.symm
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    exact (Nat.even_sub hba).2 heab

/-- The integral definition of the Gram matrix agrees with the closed form
used by `ChebyshevBound`. -/
theorem integralGram_eq_chebH (N : ℕ) :
    integralGram (N + 1) = ChebyshevBound.chebH N := by
  ext i j
  rw [integralGram, ChebyshevMoment.integral_eval_T_mul_T_nat,
    ChebyshevBound.chebH]
  have hparity :=
    even_add_iff_sameParity i.val j.val
  by_cases hsame : ChebyshevBound.SameParity i.val j.val
  · simp only [if_pos hsame, if_pos (hparity.mpr hsame)]
    have hsum := two_mul_half_add_of_sameParity hsame
    have hdist := two_mul_half_dist_of_sameParity hsame
    have hsum_real :
        (2 : ℝ) * (((i.val + j.val) / 2 : ℕ) : ℝ) =
          (i.val : ℝ) + (j.val : ℝ) := by
      exact_mod_cast hsum
    have hdist_real :
        (2 : ℝ) * ((i.val.dist j.val / 2 : ℕ) : ℝ) =
          (i.val.dist j.val : ℕ) := by
      exact_mod_cast hdist
    unfold ChebyshevBound.chebMoment
    rw [show
      4 * (((i.val + j.val) / 2 : ℕ) : ℝ) ^ 2 =
        ((i.val : ℝ) + (j.val : ℝ)) ^ 2 by nlinarith,
      show
      4 * ((i.val.dist j.val / 2 : ℕ) : ℝ) ^ 2 =
        ((i.val : ℝ) - (j.val : ℝ)) ^ 2 by
          calc
            4 * ((i.val.dist j.val / 2 : ℕ) : ℝ) ^ 2 =
                ((i.val.dist j.val : ℕ) : ℝ) ^ 2 := by nlinarith
            _ = ((i.val : ℝ) - (j.val : ℝ)) ^ 2 :=
              natCast_dist_sq i.val j.val]
    ring
  · simp only [if_neg hsame, if_neg (mt hparity.mp hsame)]

/-- The integral of the square of a Chebyshev expansion is its Gram
quadratic form. -/
theorem integral_sq_chebExpansion {n : ℕ} (c : Fin n → ℝ) :
    (∫ t in (-1 : ℝ)..1, (chebExpansion c).eval t ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * integralGram n i j * c j := by
  have hpoint (t : ℝ) :
      (chebExpansion c).eval t ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          c i *
            ((T ℝ (i.val : ℤ)).eval t *
              (T ℝ (j.val : ℤ)).eval t) *
            c j := by
    simp only [chebExpansion, eval_finset_sum, eval_mul, eval_C, pow_two]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (∫ t in (-1 : ℝ)..1, (chebExpansion c).eval t ^ 2) =
        ∫ t in (-1 : ℝ)..1,
          ∑ i : Fin n, ∑ j : Fin n,
            c i *
              ((T ℝ (i.val : ℤ)).eval t *
                (T ℝ (j.val : ℤ)).eval t) *
              c j :=
      intervalIntegral.integral_congr (fun t _ ↦ hpoint t)
    _ = ∑ i : Fin n,
          ∫ t in (-1 : ℝ)..1,
            ∑ j : Fin n,
              c i *
                ((T ℝ (i.val : ℤ)).eval t *
                  (T ℝ (j.val : ℤ)).eval t) *
                c j := by
      rw [intervalIntegral.integral_finset_sum]
      intro i _
      apply Continuous.intervalIntegrable
      fun_prop
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ∫ t in (-1 : ℝ)..1,
            c i *
              ((T ℝ (i.val : ℤ)).eval t *
                (T ℝ (j.val : ℤ)).eval t) *
              c j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finset_sum]
      intro j _
      apply Continuous.intervalIntegrable
      fun_prop
    _ = ∑ i : Fin n, ∑ j : Fin n,
        c i * integralGram n i j * c j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
      rfl

/-- The Lagrange functional is the trace of the integral Gram matrix times
the inverse discrete Gram matrix. -/
theorem functional_eq_trace {n : ℕ} (x : Fin n ↪ ℝ) :
    functional x =
      Matrix.trace
        (integralGram n *
          (((chebEvalMatrix x)ᵀ * chebEvalMatrix x)⁻¹)) := by
  let A := chebEvalMatrix x
  let B := A⁻¹
  let H := integralGram n
  have hfunctional :
      functional x =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := by
    unfold functional
    rw [intervalIntegral.integral_finset_sum]
    · simp_rw [lagrange_basis_eq_chebExpansion]
      simp_rw [integral_sq_chebExpansion]
      rfl
    · intro k _
      apply Continuous.intervalIntegrable
      fun_prop
  have htrace :
      Matrix.trace (Bᵀ * H * B) =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro k _
    change (Bᵀ * H * B) k k =
      ∑ i : Fin n, ∑ j : Fin n, B i k * H i j * B j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    functional x =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := hfunctional
    _ = Matrix.trace (Bᵀ * H * B) := htrace.symm
    _ = Matrix.trace (B * Bᵀ * H) :=
      Matrix.trace_mul_cycle Bᵀ H B
    _ = Matrix.trace (H * (B * Bᵀ)) := by
      rw [Matrix.trace_mul_comm (B * Bᵀ) H]
    _ = Matrix.trace
        (integralGram n *
          (((chebEvalMatrix x)ᵀ * chebEvalMatrix x)⁻¹)) := by
      dsimp only [H, B, A]
      rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

end

end InterpolationTrace

end Erdos1131Asymptotic
