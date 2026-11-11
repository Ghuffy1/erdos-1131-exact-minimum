/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.ChebyshevBound

/-!
# Exact resolvent algebra for the Chebyshev comparison matrix

This file separates the non-asymptotic matrix identities from both the root
calculation and the numerical estimates.  The model Gram matrix is

`R_N = (N / 2) D_N + K_N`,

where `D_N = diag (2, 1, ..., 1, 7/6)`.  Factoring out its diagonal part gives
the relative perturbation `chebY`; the inverse is then expanded through second
order with the exact remainder already estimated in `ChebyshevBound`.
-/

open scoped BigOperators

namespace Erdos1131Asymptotic.ChebyshevResolvent

open ChebyshevBound

noncomputable section

def chebDEntry (N i : ℕ) : ℝ :=
  if i = 0 then 2 else if i = N then 7 / 6 else 1

def chebD (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun i => chebDEntry N i

def modelGram (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ((N : ℝ) / 2) • chebD N + chebK N

theorem chebDEntry_mul_chebDInvEntry
    {N : ℕ} (hN : 0 < N) (i : ℕ) :
    chebDEntry N i * chebDInvEntry N i = 1 := by
  by_cases hi0 : i = 0
  · simp [chebDEntry, chebDInvEntry, hi0]
  · by_cases hiN : i = N
    · subst i
      simp [chebDEntry, chebDInvEntry, hN.ne']
    · simp [chebDEntry, chebDInvEntry, hi0, hiN]

theorem chebD_mul_chebDInv
    {N : ℕ} (hN : 0 < N) :
    chebD N * chebDInv N = 1 := by
  rw [chebD, chebDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [chebDEntry_mul_chebDInvEntry hN]
  · simp [hij]

theorem chebDInv_mul_chebD
    {N : ℕ} (hN : 0 < N) :
    chebDInv N * chebD N = 1 := by
  rw [chebD, chebDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [mul_comm]
    exact chebDEntry_mul_chebDInvEntry hN i
  · simp [hij]

theorem modelGram_factor
    {N : ℕ} (hN : 0 < N) :
    modelGram N =
      (((N : ℝ) / 2) • chebD N) * (1 + chebY N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [modelGram, chebY, Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
    chebD_mul_chebDInv hN, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem scaledChebD_mul_scaledChebDInv
    {N : ℕ} (hN : 0 < N) :
    (((N : ℝ) / 2) • chebD N) *
        ((2 / (N : ℝ)) • chebDInv N) = 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Matrix.smul_mul, Matrix.mul_smul, chebD_mul_chebDInv hN]
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> field_simp

theorem inv_scaledChebD
    {N : ℕ} (hN : 0 < N) :
    (((N : ℝ) / 2) • chebD N)⁻¹ =
      (2 / (N : ℝ)) • chebDInv N :=
  Matrix.inv_eq_right_inv (scaledChebD_mul_scaledChebDInv hN)

theorem isUnit_one_add_chebY_of_modelGram
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    IsUnit (1 + chebY N).det := by
  have hne : (modelGram N).det ≠ 0 := by
    simpa only [isUnit_iff_ne_zero] using hunit
  rw [modelGram_factor hN, Matrix.det_mul] at hne
  have hright : (1 + chebY N).det ≠ 0 := fun h =>
    hne (by simp [h])
  simpa only [isUnit_iff_ne_zero] using hright

theorem chebZ_second_order
    {N : ℕ} (hunit : IsUnit (1 + chebY N).det) :
    chebZ N = 1 - chebY N +
      chebY N * chebY N * chebZ N := by
  have hfirst := chebZ_eq_one_sub_mul hunit
  calc
    chebZ N = 1 - chebY N * chebZ N := hfirst
    _ = 1 - chebY N * (1 - chebY N * chebZ N) := by
      exact congrArg (fun Z => 1 - chebY N * Z) hfirst
    _ = 1 - chebY N + chebY N * chebY N * chebZ N := by
      noncomm_ring

theorem inv_modelGram
    {N : ℕ} (hN : 0 < N) :
    (modelGram N)⁻¹ =
      chebZ N * ((2 / (N : ℝ)) • chebDInv N) := by
  rw [modelGram_factor hN, Matrix.mul_inv_rev, inv_scaledChebD hN, chebZ]

theorem chebY_mul_scaledChebDInv
    {N : ℕ} (hN : 0 < N) :
    chebY N * ((2 / (N : ℝ)) • chebDInv N) =
      (4 / (N : ℝ) ^ 2) •
        (chebDInv N * chebK N * chebDInv N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [chebY, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem inv_modelGram_second_order
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    (modelGram N)⁻¹ =
      (2 / (N : ℝ)) • chebDInv N -
        (4 / (N : ℝ) ^ 2) •
          (chebDInv N * chebK N * chebDInv N) +
        chebInverseRemainder N := by
  have hunitY := isUnit_one_add_chebY_of_modelGram hN hunit
  rw [inv_modelGram hN, chebZ_second_order hunitY]
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    chebY_mul_scaledChebDInv hN]
  simp only [chebInverseRemainder, Matrix.mul_assoc]

end

end Erdos1131Asymptotic.ChebyshevResolvent
