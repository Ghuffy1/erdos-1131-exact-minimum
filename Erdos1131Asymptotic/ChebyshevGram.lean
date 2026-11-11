/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.ChebyshevRootSums
import Erdos1131Asymptotic.InterpolationTrace
import Erdos1131Asymptotic.ChebyshevResolvent

/-!
# The discrete Gram matrix of the Chebyshev comparison nodes

This file identifies the evaluation Gram matrix of the explicit roots of
`T_(N+1) - (1/6) T_(N-1)` with the finite model matrix used by the
resolvent estimate.
-/

open scoped BigOperators Matrix

namespace Erdos1131Asymptotic.ChebyshevGram

open Polynomial Polynomial.Chebyshev
open ChebyshevBound ChebyshevResolvent InterpolationTrace

noncomputable section

/-- The product formula for two Chebyshev polynomials, with the difference
index expressed as a natural-number distance. -/
theorem two_mul_eval_T_mul_eval_T_nat
    (a b : ℕ) (x : ℝ) :
    2 * (T ℝ (a : ℤ)).eval x * (T ℝ (b : ℤ)).eval x =
      (T ℝ ((a + b : ℕ) : ℤ)).eval x +
        (T ℝ ((a.dist b : ℕ) : ℤ)).eval x := by
  rcases le_total b a with hba | hab
  · have h := congrArg (fun p : ℝ[X] => p.eval x)
      (T_mul_T ℝ (a : ℤ) (b : ℤ))
    have hsub : (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) := by
      exact (Nat.cast_sub hba).symm
    rw [hsub] at h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    simpa only [eval_add, eval_mul, eval_ofNat, Nat.cast_add,
      mul_assoc] using h
  · have h := congrArg (fun p : ℝ[X] => p.eval x)
      (T_mul_T ℝ (b : ℤ) (a : ℤ))
    have hsub : (b : ℤ) - (a : ℤ) = ((b - a : ℕ) : ℤ) := by
      exact (Nat.cast_sub hab).symm
    rw [hsub] at h
    rw [Nat.dist_eq_sub_of_le hab]
    simpa only [eval_add, eval_mul, eval_ofNat, Nat.cast_add,
      mul_assoc, add_comm, mul_comm, add_left_comm, mul_left_comm] using h

/-- Entrywise reduction of the discrete Gram matrix to two Chebyshev root
sums.  This is the only polynomial-product calculation needed below. -/
theorem two_mul_chebEvalGram_apply
    {n : ℕ} (x : Fin n ↪ ℝ) (j k : Fin n) :
    2 * ((chebEvalMatrix x)ᵀ * chebEvalMatrix x) j k =
      (∑ i : Fin n,
          (T ℝ ((j.val + k.val : ℕ) : ℤ)).eval (x i)) +
        ∑ i : Fin n,
          (T ℝ ((j.val.dist k.val : ℕ) : ℤ)).eval (x i) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, chebEvalMatrix]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc] using
    two_mul_eval_T_mul_eval_T_nat j.val k.val (x i)

/-- Opposite parity makes both the sum and the distance odd. -/
private theorem odd_add_of_not_sameParity
    {a b : ℕ} (h : ¬SameParity a b) :
    Odd (a + b) := by
  rw [Nat.odd_iff]
  unfold SameParity at h
  omega

private theorem odd_dist_of_not_sameParity
    {a b : ℕ} (h : ¬SameParity a b) :
    Odd (a.dist b) := by
  rw [Nat.odd_iff]
  unfold SameParity at h
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    omega

/-- Abstract entrywise assembly of the model Gram matrix from the four root
sum formulas.  The hypotheses are arranged to match the public statements in
`ChebyshevRootSums`. -/
theorem evalGram_eq_modelGram_of_rootSums
    {N : ℕ} (hN : 6 ≤ N) (x : Fin (N + 1) ↪ ℝ)
    (hzero :
      (∑ i : Fin (N + 1), (T ℝ (0 : ℤ)).eval (x i)) =
        (N + 1 : ℕ))
    (hodd :
      ∀ m : ℕ, m ≤ 2 * N → Odd m →
        (∑ i : Fin (N + 1), (T ℝ (m : ℤ)).eval (x i)) = 0)
    (heven :
      ∀ r : ℕ, 1 ≤ r → r ≤ N - 1 →
        (∑ i : Fin (N + 1), (T ℝ ((2 * r : ℕ) : ℤ)).eval (x i)) =
          (1 / 6 : ℝ) ^ r)
    (htop :
      (∑ i : Fin (N + 1),
          (T ℝ ((2 * N : ℕ) : ℤ)).eval (x i)) =
        (1 / 6 : ℝ) ^ N + (N : ℝ) / 6) :
    (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N := by
  ext j k
  have htwo := two_mul_chebEvalGram_apply x j k
  have hjN : j.val ≤ N := by omega
  have hkN : k.val ≤ N := by omega
  by_cases hpar : SameParity j.val k.val
  · have hsum_even : Even (j.val + k.val) :=
      (even_add_iff_sameParity j.val k.val).mpr hpar
    have hdist_even : Even (j.val.dist k.val) := by
      refine ⟨j.val.dist k.val / 2, ?_⟩
      have hhalf := two_mul_half_dist_of_sameParity hpar
      omega
    by_cases hjk : j = k
    · subst k
      by_cases hj0 : j.val = 0
      · have hsum0 : j.val + j.val = 0 := by omega
        have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
        rw [hsum0, hdist0] at htwo
        norm_num only [Nat.cast_zero] at htwo
        rw [hzero] at htwo
        simp only [modelGram, chebD, chebK, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
          if_pos hpar]
        simp [chebDEntry, hj0]
        norm_num at htwo ⊢
        linarith
      · by_cases hjNtop : j.val = N
        · have hsumtop : j.val + j.val = 2 * N := by omega
          have hhalfN : (N + N) / 2 = N := by omega
          have hN0 : N ≠ 0 := by omega
          have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
          rw [hsumtop, hdist0, htop] at htwo
          norm_num only [Nat.cast_zero] at htwo
          rw [hzero] at htwo
          simp only [modelGram, chebD, chebK, Matrix.add_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
            if_pos hpar]
          simp [chebDEntry, hjNtop, hN0, hhalfN]
          rw [one_div_pow] at htwo
          norm_num at htwo ⊢
          linarith
        · have hjpos : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj0
          have hjbelow : j.val ≤ N - 1 := by omega
          have hhalf : (j.val + j.val) / 2 = j.val := by omega
          have hsum :
              j.val + j.val = 2 * j.val := by omega
          have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
          rw [hsum, hdist0, heven j.val hjpos hjbelow] at htwo
          norm_num only [Nat.cast_zero] at htwo
          rw [hzero] at htwo
          simp only [modelGram, chebD, chebK, Matrix.add_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
            if_pos hpar]
          simp [chebDEntry, hj0, hjNtop, hhalf]
          rw [one_div_pow] at htwo
          norm_num at htwo ⊢
          linarith
    · have hsum_pos : 1 ≤ (j.val + k.val) / 2 := by
        have hneval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        have hhalf :=
          two_mul_half_add_of_sameParity hpar
        omega
      have hsum_below : (j.val + k.val) / 2 ≤ N - 1 := by
        have hhalf := two_mul_half_add_of_sameParity hpar
        have hnotTop : ¬(j.val = N ∧ k.val = N) := by
          rintro ⟨hj, hk⟩
          apply hjk
          exact Fin.ext (hj.trans hk.symm)
        omega
      have hdist_pos : 1 ≤ j.val.dist k.val / 2 := by
        have hhalf := two_mul_half_dist_of_sameParity hpar
        have hneval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        have hdistne : j.val.dist k.val ≠ 0 := by
          intro hd
          rcases le_total j.val k.val with hjk' | hkj'
          · rw [Nat.dist_eq_sub_of_le hjk'] at hd
            omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj'] at hd
            omega
        omega
      have hdist_below : j.val.dist k.val / 2 ≤ N - 1 := by
        have hhalf := two_mul_half_dist_of_sameParity hpar
        have hdist_le : j.val.dist k.val ≤ N := by
          rcases le_total j.val k.val with hjk' | hkj'
          · rw [Nat.dist_eq_sub_of_le hjk']
            omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj']
            omega
        omega
      have hsum :
          j.val + k.val = 2 * ((j.val + k.val) / 2) :=
        (two_mul_half_add_of_sameParity hpar).symm
      have hdist :
          j.val.dist k.val = 2 * (j.val.dist k.val / 2) :=
        (two_mul_half_dist_of_sameParity hpar).symm
      rw [hsum, hdist,
        heven _ hsum_pos hsum_below,
        heven _ hdist_pos hdist_below] at htwo
      simp only [modelGram, chebD, chebK, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply, if_neg hjk, if_pos hpar]
      norm_num at htwo ⊢
      linarith
  · have hjk : j ≠ k := by
      intro h
      subst k
      exact hpar rfl
    have hsum_le : j.val + k.val ≤ 2 * N := by omega
    have hdist_le : j.val.dist k.val ≤ 2 * N := by
      rcases le_total j.val k.val with hjk' | hkj'
      · rw [Nat.dist_eq_sub_of_le hjk']
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj']
        omega
    rw [hodd _ hsum_le (odd_add_of_not_sameParity hpar),
      hodd _ hdist_le (odd_dist_of_not_sameParity hpar)] at htwo
    simp only [modelGram, chebD, chebK, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply, if_neg hjk, if_neg hpar]
    linarith

/-- The evaluation Gram matrix of the explicit comparison nodes is exactly
the model matrix used in the finite resolvent estimate. -/
theorem chebEvalGram_eq_modelGram
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    (chebEvalMatrix (chebNodes (N + 1) hn))ᵀ *
        chebEvalMatrix (chebNodes (N + 1) hn) = modelGram N := by
  let hn : 2 ≤ N + 1 := by omega
  apply evalGram_eq_modelGram_of_rootSums hN
    (chebNodes (N + 1) hn)
  · simp [T_zero]
  · intro m hm hodd
    exact sum_chebNodes_T_of_odd hn (by omega) hodd
  · intro r hrpos hrmax
    have h := sum_chebNodes_T_even (n := N + 1) (r := r) hn (by omega)
    rw [if_neg (Nat.ne_of_gt hrpos)] at h
    exact h
  · have h := sum_chebNodes_T_top (n := N + 1) hn
    simpa [show N + 1 - 1 = N by omega] using h

/-- Invertibility of an evaluation Gram matrix transfers to `modelGram`
once the two matrices have been identified. -/
theorem modelGram_det_isUnit_of_evalGram_eq
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ)
    (hgram :
      (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N) :
    IsUnit (modelGram N).det := by
  rw [← hgram, Matrix.det_mul, Matrix.det_transpose]
  exact (chebEvalMatrix_isUnit_det x).mul
    (chebEvalMatrix_isUnit_det x)

/-- The model Gram matrix is nonsingular for the explicit nodes. -/
theorem modelGram_det_isUnit
    {N : ℕ} (hN : 6 ≤ N) :
    IsUnit (modelGram N).det := by
  let hn : 2 ≤ N + 1 := by omega
  apply modelGram_det_isUnit_of_evalGram_eq
    (chebNodes (N + 1) hn)
  exact chebEvalGram_eq_modelGram hN

/-- The interpolation functional is the model trace once the discrete Gram
identity is known. -/
theorem functional_eq_modelTrace_of_evalGram_eq
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ)
    (hgram :
      (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N) :
    functional x =
      Matrix.trace (chebH N * (modelGram N)⁻¹) := by
  rw [functional_eq_trace, integralGram_eq_chebH, hgram]

/-- Exact trace representation of the functional for the explicit comparison
nodes. -/
theorem functional_chebNodes_eq_modelTrace
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    functional (chebNodes (N + 1) hn) =
      Matrix.trace (chebH N * (modelGram N)⁻¹) := by
  let hn : 2 ≤ N + 1 := by omega
  apply functional_eq_modelTrace_of_evalGram_eq
    (chebNodes (N + 1) hn)
  exact chebEvalGram_eq_modelGram hN

end

end Erdos1131Asymptotic.ChebyshevGram
