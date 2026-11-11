/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Definitions and elementary facts for Erdős Problem 1131

The node configuration is represented by an embedding `Fin n ↪ ℝ`, so
pairwise distinctness is part of the type.  The extremal value is an infimum;
no attainment is assumed.
-/

open scoped BigOperators Interval
open Filter Set

namespace Erdos1131Asymptotic

def Admissible {n : ℕ} (x : Fin n ↪ ℝ) : Prop :=
  ∀ k, x k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def functional {n : ℕ} (x : Fin n ↪ ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ∑ k : Fin n,
      ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2

def values (n : ℕ) : Set ℝ :=
  {y | ∃ x : Fin n ↪ ℝ, Admissible x ∧ functional x = y}

noncomputable def M (n : ℕ) : ℝ :=
  sInf (values n)

noncomputable def scaledDefect (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 - M (n + 1))

/-- A canonical admissible configuration, used only to show nonemptiness. -/
noncomputable def canonicalNodes (n : ℕ) : Fin n ↪ ℝ where
  toFun k := (k : ℝ) / (n + 1 : ℕ)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' hn).mp hij

theorem canonicalNodes_admissible (n : ℕ) : Admissible (canonicalNodes n) := by
  intro k
  constructor
  · change (-1 : ℝ) ≤ (k : ℝ) / (n + 1 : ℕ)
    have : 0 ≤ (k : ℝ) / (n + 1 : ℕ) := by positivity
    linarith
  · change (k : ℝ) / (n + 1 : ℕ) ≤ 1
    apply div_le_one_of_le₀
    · exact_mod_cast (Nat.le_of_lt (k.isLt.trans (Nat.lt_succ_self n)))
    · positivity

theorem values_nonempty (n : ℕ) : (values n).Nonempty :=
  ⟨functional (canonicalNodes n), canonicalNodes n, canonicalNodes_admissible n, rfl⟩

theorem functional_nonneg {n : ℕ} (x : Fin n ↪ ℝ) : 0 ≤ functional x := by
  apply intervalIntegral.integral_nonneg_of_forall
  · norm_num
  · intro t
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem values_bddBelow (n : ℕ) : BddBelow (values n) :=
  ⟨0, by
    rintro y ⟨x, -, rfl⟩
    exact functional_nonneg x⟩

theorem M_nonneg (n : ℕ) : 0 ≤ M n :=
  le_csInf (values_nonempty n) fun _ hy ↦
    let ⟨x, _, hxy⟩ := hy
    hxy ▸ functional_nonneg x

theorem M_le_functional {n : ℕ} (x : Fin n ↪ ℝ) (hx : Admissible x) :
    M n ≤ functional x :=
  csInf_le (values_bddBelow n) ⟨x, hx, rfl⟩

theorem basis_intervalIntegrable {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    IntervalIntegrable
      (fun t : ℝ ↦ (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t)
      MeasureTheory.volume (-1) 1 :=
  (Polynomial.continuous _).intervalIntegrable _ _

theorem sum_sq_intervalIntegrable {n : ℕ} (x : Fin n ↪ ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦
        ∑ k : Fin n,
          ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2)
      MeasureTheory.volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem basis_eval_self {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x k) = 1 := by
  simpa using Lagrange.eval_basis_self x.injective.injOn (Finset.mem_univ k)

theorem basis_eval_of_ne {n : ℕ} (x : Fin n ↪ ℝ) {j k : Fin n} (hjk : j ≠ k) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x j) = 0 := by
  exact Lagrange.eval_basis_of_ne (Ne.symm hjk) (Finset.mem_univ j)

theorem basis_eq_product {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    Lagrange.basis Finset.univ (x : Fin n → ℝ) k =
      ∏ i ∈ (Finset.univ.erase k),
        Polynomial.C ((x k - x i)⁻¹) * (Polynomial.X - Polynomial.C (x i)) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor]

theorem basis_eval_eq_product {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) (t : ℝ) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t =
      ∏ i ∈ (Finset.univ.erase k), (t - x i) / (x k - x i) := by
  rw [basis_eq_product]
  simp only [Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_inv_mul]

theorem node_sub_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    x i - x j ≠ 0 :=
  sub_ne_zero.mpr (x.injective.ne hij)

theorem lagrange_denominator_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    ∏ i ∈ Finset.univ.erase k, (x k - x i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact node_sub_ne_zero x (Finset.ne_of_mem_erase hi).symm

theorem sq_eq_abs_sq (a : ℝ) : a ^ 2 = |a| ^ 2 := by
  rw [sq_abs]

def permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) : Fin n ↪ ℝ :=
  e.toEmbedding.trans x

@[simp]
theorem permuteNodes_apply {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) (k : Fin n) :
    permuteNodes x e k = x (e k) :=
  rfl

theorem admissible_permuteNodes {n : ℕ} {x : Fin n ↪ ℝ} (e : Fin n ≃ Fin n)
    (hx : Admissible x) : Admissible (permuteNodes x e) :=
  fun k ↦ hx (e k)

theorem basis_permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n)
    (k : Fin n) :
    Lagrange.basis Finset.univ (permuteNodes x e : Fin n → ℝ) k =
      Lagrange.basis Finset.univ (x : Fin n → ℝ) (e k) := by
  simp only [Lagrange.basis, permuteNodes_apply]
  apply Finset.prod_equiv e
  · intro i
    simp
  · intro i hi
    rfl

theorem functional_permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) :
    functional (permuteNodes x e) = functional x := by
  unfold functional
  congr 1
  funext t
  simp_rw [basis_permuteNodes]
  exact e.sum_comp (fun k : Fin n ↦
    ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2)

theorem M_one : M 1 = 2 := by
  have hvalues : values 1 = {2} := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      simp [functional]
      norm_num
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨canonicalNodes 1, canonicalNodes_admissible 1, by
        simp [functional]
        norm_num⟩
  rw [M, hvalues, csInf_singleton]

end Erdos1131Asymptotic
