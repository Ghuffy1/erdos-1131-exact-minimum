import HermiteSignature
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! The zero-root multiplicity of a symmetric characteristic polynomial is its nullity. -/

open Module
open scoped BigOperators Matrix

noncomputable section

namespace Erdos1131

theorem matrixQuadratic_radical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    M.toQuadraticForm'.radical = LinearMap.ker M.toLin' := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hs : ∀ x y : ι → ℝ, M.toBilin' x y = M.toBilin' y x := by
    intro x y
    simp only [Matrix.toBilin'_apply']
    simpa only [hM.eq] using Matrix.dotProduct_transpose_mulVec M x y
  have hAssoc : QuadraticMap.associated M.toQuadraticForm' = M.toBilin' :=
    QuadraticMap.associated_left_inverse (S := ℝ) hs
  rw [QuadraticMap.radical_eq_ker_associated, hAssoc]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    Matrix.toBilin'_apply', Matrix.toLin'_apply]
  simp only [Matrix.dotProduct_mulVec]
  rw [dotProduct_eq_zero_iff]
  have hv : x ᵥ* M = M *ᵥ x := by
    simpa only [hM.eq] using Matrix.vecMul_transpose M x
  rw [hv]

theorem matrix_inertia_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    sigPos M.toQuadraticForm' + sigNeg M.toQuadraticForm' = M.rank := by
  have hsig := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := M.toQuadraticForm')
  rw [matrixQuadratic_radical M hM] at hsig
  have hrank := LinearMap.finrank_range_add_finrank_ker M.toLin'
  have hlin : M.toLin' = M.mulVecLin := by
    ext x
    rfl
  rw [hlin] at hsig hrank
  change M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) =
    Module.finrank ℝ (ι → ℝ) at hrank
  omega

theorem trailingDegree_X_sub_C (a : ℝ) :
    (Polynomial.X - Polynomial.C a).natTrailingDegree = if a = 0 then 1 else 0 := by
  by_cases ha : a = 0
  · simp [ha, Polynomial.natTrailingDegree_X]
  · rw [ite_eq_right ha]
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    simpa using neg_ne_zero.mpr ha

theorem trailingDegree_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).natTrailingDegree =
      ∑ i ∈ s, if a i = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Polynomial.natTrailingDegree_mul
      (Polynomial.X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr (fun j _ => Polynomial.X_sub_C_ne_zero _)),
      trailingDegree_X_sub_C, ih, Finset.sum_insert hi]

theorem symmetric_charpoly_trailingDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    M.charpoly.natTrailingDegree =
      Fintype.card {i // (Matrix.isHermitian_iff_isSymm.mpr hM).eigenvalues i = 0} := by
  let hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  rw [hH.charpoly_eq, trailingDegree_prod_X_sub_C]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem symmetric_rank_add_trailingDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    M.rank + M.charpoly.natTrailingDegree = Fintype.card ι := by
  let hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  rw [hH.rank_eq_card_non_zero_eigs, symmetric_charpoly_trailingDegree M hM]
  rw [Fintype.card_subtype_compl (fun i => hH.eigenvalues i = 0)]
  have hle := Fintype.card_subtype_le (fun i => hH.eigenvalues i = 0)
  omega

theorem matrix_inertia_add_trailingDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    sigPos M.toQuadraticForm' + sigNeg M.toQuadraticForm' + M.charpoly.natTrailingDegree =
      Fintype.card ι := by
  rw [matrix_inertia_rank M hM]
  exact symmetric_rank_add_trailingDegree M hM

end Erdos1131
