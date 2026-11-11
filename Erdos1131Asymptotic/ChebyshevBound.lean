/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# The finite Chebyshev comparison estimate

This file contains the purely finite matrix estimate used by the Chebyshev
comparison family for Erdős Problem 1131.  The construction and enumeration of
the roots of `T_{N+1} - (1 / 6) T_{N-1}` is deliberately kept separate.

The central matrices below are indexed by the Chebyshev degrees `0, ..., N`.
`chebH` is the Lebesgue Gram matrix of these polynomials, `chebK` is the
bounded part of the evaluation Gram matrix, and `chebDInv` is the inverse of
its diagonal part.
-/

open scoped BigOperators

namespace Erdos1131Asymptotic.ChebyshevBound

noncomputable section

/-- The even Chebyshev moment `∫ T_{2r}` divided by two. -/
def chebMoment (r : ℕ) : ℝ :=
  1 / (1 - 4 * (r : ℝ) ^ 2)

/-- Two natural numbers have the same parity. -/
def SameParity (j k : ℕ) : Prop :=
  j % 2 = k % 2

instance (j k : ℕ) : Decidable (SameParity j k) :=
  inferInstanceAs (Decidable (j % 2 = k % 2))

/-- The Lebesgue Gram matrix of `T_0, ..., T_N`, written in closed form. -/
def chebH (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun j k =>
    if SameParity j.val k.val then
      chebMoment ((j.val + k.val) / 2) + chebMoment (j.val.dist k.val / 2)
    else 0

/-- The bounded part of the evaluation Gram matrix for
`T_{N+1} - (1/6) T_{N-1}`. -/
def chebK (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun j k =>
    if SameParity j.val k.val then
      (((1 / 6 : ℝ) ^ ((j.val + k.val) / 2) +
        (1 / 6 : ℝ) ^ (j.val.dist k.val / 2)) / 2)
    else 0

/-- The inverse of the diagonal matrix whose entries are
`2, 1, ..., 1, 7/6`.  The definitions at `0` and `N` overlap only when
`N = 0`; all comparison estimates assume `6 ≤ N`. -/
def chebDInvEntry (N i : ℕ) : ℝ :=
  if i = 0 then 1 / 2 else if i = N then 6 / 7 else 1

def chebDInv (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun i => chebDInvEntry N i

/-- Relative perturbation in the factorization
`R = (N/2) D (1 + chebY N)`. -/
def chebY (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (2 / (N : ℝ)) • (chebDInv N * chebK N)

/-- The inverse relative factor. -/
def chebZ (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 + chebY N)⁻¹

/-- The exact second-order remainder after expanding the relative inverse. -/
def chebInverseRemainder (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  chebY N * chebY N * chebZ N * ((2 / (N : ℝ)) • chebDInv N)

/-- Absolute row sum.  We use this elementary quantity instead of invoking
operator-norm or spectral machinery. -/
def absRowSum {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (i : m) : ℝ :=
  ∑ j, |A i j|

/-- Every absolute row sum of `A` is at most `c`. -/
def RowBound {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (c : ℝ) : Prop :=
  ∀ i, absRowSum A i ≤ c

/-- Maximum absolute row sum for a nonempty finite row index type. -/
def maxAbsRowSum {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (absRowSum A)

theorem le_maxAbsRowSum {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) (i : m) :
    absRowSum A i ≤ maxAbsRowSum A :=
  Finset.le_sup' (absRowSum A) (Finset.mem_univ i)

theorem rowBound_maxAbsRowSum
    {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) :
    RowBound A (maxAbsRowSum A) :=
  le_maxAbsRowSum A

theorem maxAbsRowSum_le_iff
    {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) (c : ℝ) :
    maxAbsRowSum A ≤ c ↔ RowBound A c := by
  rw [maxAbsRowSum, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_const, RowBound]

theorem abs_chebMoment_le_one (r : ℕ) :
    |chebMoment r| ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    norm_num [chebMoment]
  · have hr_nat : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hr_real : (1 : ℝ) ≤ r := by exact_mod_cast hr_nat
    have hneg : 1 - 4 * (r : ℝ) ^ 2 ≤ 0 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
    have habs : 1 ≤ |1 - 4 * (r : ℝ) ^ 2| := by
      rw [abs_of_nonpos hneg]
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    rw [chebMoment, one_div, abs_inv]
    exact inv_le_one_of_one_le₀ habs

@[simp]
theorem chebMoment_zero : chebMoment 0 = 1 := by
  norm_num [chebMoment]

theorem chebMoment_succ (m : ℕ) :
    chebMoment (m + 1) =
      -(1 : ℝ) / ((2 * m + 1) * (2 * m + 3)) := by
  unfold chebMoment
  push_cast
  rw [show 1 - 4 * ((m : ℝ) + 1) ^ 2 =
      -((2 * m + 1) * (2 * m + 3)) by ring]
  simp only [one_div, inv_neg, neg_div]

/-- The elementary telescoping identity
`Σ_{r=1}^m (1 - 4r²)⁻¹ = -m/(2m+1)`. -/
theorem sum_chebMoment_succ (m : ℕ) :
    Finset.sum (Finset.range m) (fun r => chebMoment (r + 1)) =
      -(m : ℝ) / (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      rw [chebMoment_succ]
      push_cast
      have h₁ : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      have h₂ : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
      field_simp
      ring

theorem abs_chebH_entry_le_two (N : ℕ) (i j : Fin (N + 1)) :
    |chebH N i j| ≤ 2 := by
  rw [chebH]
  split_ifs
  · calc
      |chebMoment ((i.val + j.val) / 2) +
          chebMoment (i.val.dist j.val / 2)| ≤
          |chebMoment ((i.val + j.val) / 2)| +
            |chebMoment (i.val.dist j.val / 2)| := abs_add_le _ _
      _ ≤ 1 + 1 :=
        add_le_add (abs_chebMoment_le_one _) (abs_chebMoment_le_one _)
      _ = 2 := by norm_num
  · norm_num

theorem chebH_diag (N : ℕ) (i : Fin (N + 1)) :
    chebH N i i = 1 + chebMoment i.val := by
  have hii : (i.val + i.val) / 2 = i.val := by
    rw [← Nat.two_mul i.val, Nat.mul_div_cancel_left]
    norm_num
  rw [chebH, if_pos (show SameParity i.val i.val from rfl)]
  rw [hii, Nat.dist_self, Nat.zero_div, chebMoment_zero, add_comm]

theorem trace_chebH_mul_chebDInv_eq_sum (N : ℕ) :
    Matrix.trace (chebH N * chebDInv N) =
      ∑ i : Fin (N + 1),
        (1 + chebMoment i.val) * chebDInvEntry N i.val := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change (chebH N * chebDInv N) i i =
    (1 + chebMoment i.val) * chebDInvEntry N i.val
  rw [Matrix.mul_apply, chebDInv]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [chebH_diag]

theorem chebDInvEntry_fin_eq
    {N : ℕ} (hN : 0 < N) (i : Fin (N + 1)) :
    chebDInvEntry N i.val =
      1 - (if i = 0 then 1 / 2 else 0) -
        (if i = Fin.last N then 1 / 7 else 0) := by
  by_cases hi0 : i = 0
  · subst i
    simp [chebDInvEntry, hN.ne']
    norm_num
  · by_cases hiN : i = Fin.last N
    · subst i
      simp [chebDInvEntry, hN.ne']
      norm_num
    · have hival0 : i.val ≠ 0 := by
        intro h
        apply hi0
        exact Fin.ext h
      have hivalN : i.val ≠ N := by
        intro h
        apply hiN
        exact Fin.ext h
      simp [chebDInvEntry, hi0, hiN, hival0, hivalN]

theorem sum_mul_chebDInvEntry
    {N : ℕ} (hN : 0 < N) (f : Fin (N + 1) → ℝ) :
    (∑ i, f i * chebDInvEntry N i.val) =
      (∑ i, f i) - f 0 / 2 - f (Fin.last N) / 7 := by
  classical
  simp_rw [chebDInvEntry_fin_eq hN]
  calc
    (∑ i, f i *
        (1 - (if i = 0 then 1 / 2 else 0) -
          (if i = Fin.last N then 1 / 7 else 0))) =
        ∑ i, (f i - (if i = 0 then f i / 2 else 0) -
          (if i = Fin.last N then f i / 7 else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
    _ = (∑ i, f i) - f 0 / 2 - f (Fin.last N) / 7 := by
      simp only [Finset.sum_sub_distrib]
      simp

theorem sum_chebMoment_fin (N : ℕ) :
    (∑ i : Fin (N + 1), chebMoment i.val) =
      1 - (N : ℝ) / (2 * N + 1) := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ',
    sum_chebMoment_succ, chebMoment_zero]
  ring

theorem trace_chebH_mul_chebDInv_exact
    {N : ℕ} (hN : 0 < N) :
    Matrix.trace (chebH N * chebDInv N) =
      (N : ℝ) + 5 / 14 + 1 / (2 * (2 * N + 1)) -
        chebMoment N / 7 := by
  rw [trace_chebH_mul_chebDInv_eq_sum,
    sum_mul_chebDInvEntry hN, Fin.last]
  rw [show (∑ i : Fin (N + 1), (1 + chebMoment i.val)) =
      (N + 1 : ℝ) + ∑ i : Fin (N + 1), chebMoment i.val by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring,
    sum_chebMoment_fin]
  simp only [Fin.val_zero, chebMoment_zero]
  have hden : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem trace_chebH_mul_chebDInv_le
    {N : ℕ} (hN : 0 < N) :
    Matrix.trace (chebH N * chebDInv N) ≤
      (N : ℝ) + 5 / 14 + 1 / N := by
  rw [trace_chebH_mul_chebDInv_exact hN]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hden : (0 : ℝ) < 4 * (N : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have ha :
      (1 : ℝ) / (2 * (2 * N + 1)) ≤ 1 / (4 * N) := by
    apply (div_le_div_iff₀
      (by positivity : (0 : ℝ) < 2 * (2 * N + 1))
      (by positivity : (0 : ℝ) < 4 * N)).2
    nlinarith
  have hb :
      (1 : ℝ) / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤ 1 / (7 * N) := by
    rw [div_div]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hNpos)
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hinv : 0 ≤ (1 : ℝ) / N := by positivity
  unfold chebMoment
  rw [show (1 : ℝ) - 4 * (N : ℝ) ^ 2 =
    -(4 * (N : ℝ) ^ 2 - 1) by ring, div_neg, neg_div,
    sub_neg_eq_add]
  have herr :
      (1 : ℝ) / (2 * (2 * N + 1)) +
          1 / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤ 1 / N := by
    calc
      (1 : ℝ) / (2 * (2 * N + 1)) +
          1 / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤
          1 / (4 * N) + 1 / (7 * N) := add_le_add ha hb
      _ ≤ 1 / N := by
        ring_nf at *
        nlinarith
  linarith

/-- A finite subseries of the geometric series with ratio `1/6`. -/
theorem sum_one_sixth_pow_le
    {α : Type*} (s : Finset α) (e : α → ℕ)
    (he : Set.InjOn e s) :
    (∑ x ∈ s, (1 / 6 : ℝ) ^ e x) ≤ 6 / 5 := by
  classical
  rw [← Finset.sum_image he]
  calc
    (∑ r ∈ s.image e, (1 / 6 : ℝ) ^ r) ≤
        ∑' r : ℕ, (1 / 6 : ℝ) ^ r := by
      exact (summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 6 : ℝ)‖ < 1)).sum_le_tsum _
          (fun _ _ => by positivity)
    _ = 6 / 5 := by
      rw [tsum_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 6 : ℝ)‖ < 1)]
      norm_num

def sameParityIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j => SameParity i.val j.val

def sameParityLeftIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j =>
    SameParity i.val j.val ∧ j.val ≤ i.val

def sameParityRightIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j =>
    SameParity i.val j.val ∧ i.val < j.val

theorem injOn_dist_div_two_left
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => i.val.dist j.val / 2)
      (sameParityLeftIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityLeftIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  rw [Nat.dist_comm i.val a.val, Nat.dist_eq_sub_of_le ha.2,
    Nat.dist_comm i.val c.val, Nat.dist_eq_sub_of_le hc.2] at heq
  omega

theorem injOn_dist_div_two_sub_one_right
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => i.val.dist j.val / 2 - 1)
      (sameParityRightIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityRightIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt ha.2),
    Nat.dist_eq_sub_of_le (Nat.le_of_lt hc.2)] at heq
  omega

theorem injOn_add_div_two
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => (i.val + j.val) / 2)
      (sameParityIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  have hea : (i.val + a.val) % 2 = 0 := by omega
  have hec : (i.val + c.val) % 2 = 0 := by omega
  have hda : ((i.val + a.val) / 2) * 2 = i.val + a.val := by omega
  have hdc : ((i.val + c.val) / 2) * 2 = i.val + c.val := by omega
  omega

theorem sum_dist_div_two_left_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityLeftIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 6 / 5 :=
  sum_one_sixth_pow_le _ _ (injOn_dist_div_two_left i)

theorem sum_add_div_two_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityIndices N i,
      (1 / 6 : ℝ) ^ ((i.val + j.val) / 2)) ≤ 6 / 5 :=
  sum_one_sixth_pow_le _ _ (injOn_add_div_two i)

theorem sum_dist_div_two_right_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityRightIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 1 / 5 := by
  have hshift :
      (∑ j ∈ sameParityRightIndices N i,
        (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) =
      (1 / 6 : ℝ) *
        ∑ j ∈ sameParityRightIndices N i,
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := hj
    simp only [sameParityRightIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj'
    have hdist : 1 ≤ i.val.dist j.val / 2 := by
      rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hj'.2)]
      unfold SameParity at hj'
      omega
    have hexp :
        i.val.dist j.val / 2 =
          (i.val.dist j.val / 2 - 1) + 1 := by omega
    calc
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2) =
          (1 / 6 : ℝ) ^ ((i.val.dist j.val / 2 - 1) + 1) := by
            exact congrArg (fun e : ℕ => (1 / 6 : ℝ) ^ e) hexp
      _ = (1 / 6 : ℝ) *
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) := by
            rw [pow_succ]
            ring
  rw [hshift]
  have hgeom := sum_one_sixth_pow_le
    (sameParityRightIndices N i)
    (fun j : Fin (N + 1) => i.val.dist j.val / 2 - 1)
    (injOn_dist_div_two_sub_one_right i)
  calc
    (1 / 6 : ℝ) *
        ∑ j ∈ sameParityRightIndices N i,
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) ≤
        (1 / 6 : ℝ) * (6 / 5) := by gcongr
    _ = 1 / 5 := by norm_num

theorem sum_dist_div_two_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 7 / 5 := by
  have hleft :
      (sameParityIndices N i).filter (fun j => j.val ≤ i.val) =
        sameParityLeftIndices N i := by
    ext j
    simp only [sameParityIndices, sameParityLeftIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hright :
      (sameParityIndices N i).filter (fun j => ¬j.val ≤ i.val) =
        sameParityRightIndices N i := by
    ext j
    simp only [sameParityIndices, sameParityRightIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, hj⟩
      exact ⟨hp, Nat.lt_of_not_ge hj⟩
    · rintro ⟨hp, hj⟩
      exact ⟨hp, Nat.not_le_of_lt hj⟩
  rw [← Finset.sum_filter_add_sum_filter_not
      (sameParityIndices N i) (fun j => j.val ≤ i.val)
      (fun j => (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)),
    hleft, hright]
  linarith [sum_dist_div_two_left_le i, sum_dist_div_two_right_le i]

theorem chebK_nonneg (N : ℕ) (i j : Fin (N + 1)) :
    0 ≤ chebK N i j := by
  rw [chebK]
  split_ifs
  · positivity
  · norm_num

theorem rowBound_chebK (N : ℕ) :
    RowBound (chebK N) (13 / 10) := by
  intro i
  have hsum :
      absRowSum (chebK N) i =
        ∑ j ∈ sameParityIndices N i,
          (((1 / 6 : ℝ) ^ ((i.val + j.val) / 2) +
            (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) / 2) := by
    rw [absRowSum]
    simp_rw [abs_of_nonneg (chebK_nonneg N i _)]
    simp only [sameParityIndices, Finset.sum_filter, chebK]
  rw [hsum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  calc
    ((∑ x ∈ sameParityIndices N i,
        (1 / 6 : ℝ) ^ ((i.val + x.val) / 2)) +
      ∑ x ∈ sameParityIndices N i,
        (1 / 6 : ℝ) ^ (i.val.dist x.val / 2)) / 2 ≤
        ((6 / 5 : ℝ) + 7 / 5) / 2 := by
          exact div_le_div_of_nonneg_right
            (add_le_add (sum_add_div_two_le i) (sum_dist_div_two_le i))
            (by norm_num)
    _ = 13 / 10 := by norm_num

theorem absRowSum_nonneg {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (i : m) :
    0 ≤ absRowSum A i :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem absRowSum_smul {m n : Type*} [Fintype n]
    (a : ℝ) (A : Matrix m n ℝ) (i : m) :
    absRowSum (a • A) i = |a| * absRowSum A i := by
  classical
  simp only [absRowSum, Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem rowBound_smul {m n : Type*} [Fintype n]
    {A : Matrix m n ℝ} {c : ℝ} (hA : RowBound A c) (a : ℝ) :
    RowBound (a • A) (|a| * c) := by
  intro i
  rw [absRowSum_smul]
  exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg a)

theorem absRowSum_add_le {m n : Type*} [Fintype n]
    (A B : Matrix m n ℝ) (i : m) :
    absRowSum (A + B) i ≤ absRowSum A i + absRowSum B i := by
  classical
  simp only [absRowSum, Matrix.add_apply]
  calc
    ∑ j, |A i j + B i j| ≤ ∑ j, (|A i j| + |B i j|) :=
      Finset.sum_le_sum fun _ _ => abs_add_le _ _
    _ = _ := Finset.sum_add_distrib

theorem rowBound_add {m n : Type*} [Fintype n]
    {A B : Matrix m n ℝ} {c d : ℝ}
    (hA : RowBound A c) (hB : RowBound B d) :
    RowBound (A + B) (c + d) := by
  intro i
  exact (absRowSum_add_le A B i).trans (add_le_add (hA i) (hB i))

theorem absRowSum_mul_le {m n p : Type*} [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) (i : m) :
    absRowSum (A * B) i ≤
      ∑ k, |A i k| * absRowSum B k := by
  classical
  simp only [absRowSum, Matrix.mul_apply]
  calc
    ∑ j, |∑ k, A i k * B k j| ≤
        ∑ j, ∑ k, |A i k * B k j| := by
      gcongr with j
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, ∑ j, |A i k * B k j| := Finset.sum_comm
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
      congr 1
      funext k
      simp only [abs_mul, Finset.mul_sum]

theorem rowBound_mul {m n p : Type*} [Fintype n] [Fintype p]
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} {c d : ℝ}
    (hA : RowBound A c) (hB : RowBound B d) (hd : 0 ≤ d) :
    RowBound (A * B) (c * d) := by
  intro i
  refine (absRowSum_mul_le A B i).trans ?_
  calc
    ∑ k, |A i k| * absRowSum B k ≤ ∑ k, |A i k| * d := by
      gcongr with k
      exact hB k
    _ = absRowSum A i * d := by
      simp only [absRowSum, Finset.sum_mul]
    _ ≤ c * d := mul_le_mul_of_nonneg_right (hA i) hd

theorem rowBound_one {n : Type*} [Fintype n] [DecidableEq n] :
    RowBound (1 : Matrix n n ℝ) 1 := by
  intro i
  rw [absRowSum]
  simp only [Matrix.one_apply, abs_ite, abs_one, abs_zero]
  exact le_of_eq <| by
    simp

theorem absRowSum_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (f : n → ℝ) (i : n) :
    absRowSum (Matrix.diagonal f) i = |f i| := by
  rw [absRowSum]
  simp only [Matrix.diagonal_apply, abs_ite, abs_zero]
  simp

theorem abs_chebDInvEntry_le_one {N i : ℕ} :
    |chebDInvEntry N i| ≤ 1 := by
  rw [chebDInvEntry]
  split_ifs <;> norm_num

theorem rowBound_chebDInv (N : ℕ) :
    RowBound (chebDInv N) 1 := by
  intro i
  rw [chebDInv, absRowSum_diagonal]
  exact abs_chebDInvEntry_le_one

theorem rowBound_chebY_of_rowBound_chebK
    {N : ℕ} (hN : 0 < N)
    (hK : RowBound (chebK N) (13 / 10)) :
    RowBound (chebY N) (13 / (5 * N)) := by
  have hprod : RowBound (chebDInv N * chebK N) (1 * (13 / 10)) :=
    rowBound_mul (rowBound_chebDInv N) hK (by norm_num)
  have hsmul := rowBound_smul hprod (2 / (N : ℝ))
  rw [chebY]
  convert hsmul using 1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_of_pos (div_pos (by norm_num) hNr)]
  field_simp
  ring

/-- Elementary finite inverse bound.  It is stated from the identity
`Z = 1 - Y Z`, so it does not depend on a particular matrix-inverse API. -/
theorem rowBound_of_eq_one_sub_mul
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    (Y Z : Matrix n n ℝ) {q : ℝ}
    (hY : RowBound Y q) (hq1 : q < 1)
    (hZ : Z = 1 - Y * Z) :
    RowBound Z (1 / (1 - q)) := by
  let M := maxAbsRowSum Z
  have hM0 : 0 ≤ M := (absRowSum_nonneg Z (Classical.choice inferInstance)).trans
    (le_maxAbsRowSum Z (Classical.choice inferInstance))
  have hZM : RowBound Z M := rowBound_maxAbsRowSum Z
  have hYZ : RowBound (Y * Z) (q * M) :=
    rowBound_mul hY hZM hM0
  have hnegYZ : RowBound (-(Y * Z)) (q * M) := by
    intro i
    simpa only [absRowSum, Matrix.neg_apply, abs_neg] using hYZ i
  have hRhs : RowBound (1 - Y * Z) (1 + q * M) := by
    simpa only [sub_eq_add_neg] using rowBound_add rowBound_one hnegYZ
  have hMle : M ≤ 1 + q * M := by
    rw [maxAbsRowSum_le_iff]
    simpa only [← hZ] using hRhs
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hMdiv : M ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact fun i => (hZM i).trans hMdiv

theorem chebZ_eq_one_sub_mul
    {N : ℕ} (hunit : IsUnit (1 + chebY N).det) :
    chebZ N = 1 - chebY N * chebZ N := by
  have hmul : (1 + chebY N) * chebZ N = 1 := by
    rw [chebZ]
    exact (1 + chebY N).mul_nonsing_inv hunit
  have hadd : chebZ N + chebY N * chebZ N = 1 := by
    simpa only [Matrix.add_mul, Matrix.one_mul] using hmul
  exact eq_sub_of_add_eq hadd

theorem rowBound_chebZ_two
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    RowBound (chebZ N) 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hY := rowBound_chebY_of_rowBound_chebK hNpos hK
  have hq : (13 : ℝ) / (5 * N) < 1 := by
    have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
    have hden : (0 : ℝ) < 5 * N := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  have hZ := rowBound_of_eq_one_sub_mul
    (chebY N) (chebZ N) hY hq (chebZ_eq_one_sub_mul hunit)
  intro i
  refine (hZ i).trans ?_
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 1 - (13 : ℝ) / (5 * N) := sub_pos.mpr hq
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith

theorem rowBound_chebInverseRemainder
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    RowBound (chebInverseRemainder N) (676 / (25 * (N : ℝ) ^ 3)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hY := rowBound_chebY_of_rowBound_chebK hNpos hK
  have hZ := rowBound_chebZ_two hN hK hunit
  have hYY : RowBound (chebY N * chebY N)
      ((13 / (5 * N : ℝ)) * (13 / (5 * N : ℝ))) :=
    rowBound_mul hY hY (by positivity)
  have hYYZ : RowBound (chebY N * chebY N * chebZ N)
      (((13 / (5 * N : ℝ)) * (13 / (5 * N : ℝ))) * 2) :=
    rowBound_mul hYY hZ (by norm_num)
  have hscaledD :
      RowBound ((2 / (N : ℝ)) • chebDInv N) (2 / (N : ℝ)) := by
    have h := rowBound_smul (rowBound_chebDInv N) (2 / (N : ℝ))
    have hdiv : (0 : ℝ) < 2 / N := div_pos (by norm_num) hNr
    simpa only [abs_of_pos hdiv, mul_one] using h
  rw [chebInverseRemainder]
  convert rowBound_mul hYYZ hscaledD (le_of_lt (div_pos (by norm_num) hNr)) using 1
  field_simp
  ring

/-- A trace estimate that only uses entry bounds for the left factor and
absolute row sums for the right factor. -/
theorem abs_trace_mul_le_of_entry_le_rowBound
    {n : Type*} [Fintype n]
    (H E : Matrix n n ℝ) {h e : ℝ}
    (hH : ∀ i j, |H i j| ≤ h) (hE : RowBound E e)
    (hh : 0 ≤ h) :
    |Matrix.trace (H * E)| ≤ (Fintype.card n : ℝ) * h * e := by
  classical
  rw [Matrix.trace_mul_comm H E]
  rw [Matrix.trace]
  calc
    |∑ i, (E * H) i i| ≤ ∑ i, |(E * H) i i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, h * e := by
      gcongr with i
      rw [Matrix.mul_apply]
      calc
        |∑ j, E i j * H j i| ≤ ∑ j, |E i j * H j i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |E i j| * |H j i| := by simp only [abs_mul]
        _ ≤ ∑ j, |E i j| * h := by
          gcongr with j
          exact hH j i
        _ = absRowSum E i * h := by
          simp only [absRowSum, Finset.sum_mul]
        _ ≤ e * h := mul_le_mul_of_nonneg_right (hE i) hh
        _ = h * e := mul_comm _ _
    _ = (Fintype.card n : ℝ) * h * e := by
      simp [mul_assoc]

theorem abs_trace_chebH_inverseRemainder_le
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    |Matrix.trace (chebH N * chebInverseRemainder N)| ≤
      64 / (N : ℝ) ^ 2 := by
  have hrow := rowBound_chebInverseRemainder hN hK hunit
  have htrace := abs_trace_mul_le_of_entry_le_rowBound
    (chebH N) (chebInverseRemainder N)
    (abs_chebH_entry_le_two N) hrow (by norm_num)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [Fintype.card_fin] at htrace
  refine htrace.trans ?_
  push_cast
  field_simp
  have hNr6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end

end Erdos1131Asymptotic.ChebyshevBound
