/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# The explicit Chebyshev comparison nodes

For `n ≥ 2` and `b = 1/6`, the comparison nodes are the `n` real roots of

`Qₙ = Tₙ - b Tₙ₋₂`.

The alternating signs at the extrema `cos (kπ/n)` put one root in each
open interval between consecutive extrema.  This simultaneously proves
admissibility and excludes collisions.
-/

open scoped BigOperators Interval
open Set

namespace Erdos1131Asymptotic

open Polynomial Polynomial.Chebyshev Real

noncomputable def chebQ (n : ℕ) : ℝ[X] :=
  T ℝ (n : ℤ) -
    Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)

theorem chebQ_eval (n : ℕ) (x : ℝ) :
    (chebQ n).eval x =
      (T ℝ (n : ℤ)).eval x -
        (1 : ℝ) / 6 * (T ℝ ((n - 2 : ℕ) : ℤ)).eval x := by
  simp [chebQ]

theorem degree_chebQ {n : ℕ} (hn : 2 ≤ n) : (chebQ n).degree = n := by
  rw [chebQ, degree_sub_eq_left_of_degree_lt]
  · exact degree_T ℝ n
  · calc
      (Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)).degree
          = (T ℝ ((n - 2 : ℕ) : ℤ)).degree := by
              rw [degree_C_mul (by norm_num)]
      _ = (n - 2 : ℕ) := by
        simp only [degree_T, Int.natAbs_natCast]
      _ < (n : WithBot ℕ) := by
        exact_mod_cast Nat.sub_lt (by omega) (by omega)
      _ = (T ℝ n).degree := (degree_T ℝ n).symm

theorem chebQ_ne_zero {n : ℕ} (hn : 2 ≤ n) : chebQ n ≠ 0 := by
  rw [← degree_ne_bot, degree_chebQ hn]
  exact WithBot.coe_ne_bot

private theorem grid_angle_sub {n k : ℕ} (hn : 2 ≤ n) :
    ((n - 2 : ℕ) : ℝ) * ((k : ℝ) * π / n) =
      (k : ℝ) * π - 2 * ((k : ℝ) * π / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hn]
  field_simp

theorem chebQ_eval_grid {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos ((k : ℝ) * π / n)) =
      (-1 : ℝ) ^ k *
        (1 - (1 : ℝ) / 6 * cos (2 * ((k : ℝ) * π / n))) := by
  rw [chebQ_eval, T_real_cos, T_real_cos]
  norm_num only [Int.cast_natCast]
  rw [show (n : ℝ) * ((k : ℝ) * π / n) = (k : ℝ) * π by
    field_simp]
  rw [grid_angle_sub hn, cos_nat_mul_pi, cos_nat_mul_pi_sub]
  ring

theorem chebQ_grid_factor_pos {n k : ℕ} :
    0 < 1 - (1 : ℝ) / 6 * cos (2 * ((k : ℝ) * π / n)) := by
  have hcos := neg_one_le_cos (2 * ((k : ℝ) * π / n))
  have hcos' := cos_le_one (2 * ((k : ℝ) * π / n))
  nlinarith

theorem chebQ_eval_grid_ne_zero {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos ((k : ℝ) * π / n)) ≠ 0 := by
  rw [chebQ_eval_grid hn]
  exact mul_ne_zero (pow_ne_zero k (by norm_num)) (ne_of_gt chebQ_grid_factor_pos)

theorem chebQ_eval_grid_mul_next_neg {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos (((k + 1 : ℕ) : ℝ) * π / n)) *
        (chebQ n).eval (cos ((k : ℝ) * π / n)) < 0 := by
  rw [chebQ_eval_grid hn, chebQ_eval_grid hn, pow_succ]
  have hk := chebQ_grid_factor_pos (n := n) (k := k)
  have hk1 := chebQ_grid_factor_pos (n := n) (k := k + 1)
  have hs : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hsquare : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ k * -1 *
          (1 - 1 / 6 * cos (2 * (↑(k + 1) * π / ↑n))) *
          ((-1 : ℝ) ^ k *
            (1 - 1 / 6 * cos (2 * (↑k * π / ↑n))))
        = -(((-1 : ℝ) ^ k) ^ 2 *
            ((1 - 1 / 6 * cos (2 * (↑(k + 1) * π / ↑n))) *
              (1 - 1 / 6 * cos (2 * (↑k * π / ↑n))))) := by ring
    _ < 0 := by
      rw [hsquare]
      nlinarith [mul_pos hk1 hk]

private theorem grid_angle_mem {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    (k : ℝ) * π / n ∈ Set.Icc (0 : ℝ) π := by
  constructor
  · positivity
  · calc
      (k : ℝ) * π / n ≤ (n : ℝ) * π / n := by
        gcongr
      _ = π := by field_simp

theorem grid_cos_strictAnti {n i j : ℕ} (hn : 2 ≤ n) (hij : i < j) (hj : j ≤ n) :
    cos ((j : ℝ) * π / n) < cos ((i : ℝ) * π / n) := by
  apply cos_lt_cos_of_nonneg_of_le_pi
  · exact (grid_angle_mem hn (Nat.le_trans (Nat.le_of_lt hij) hj)).1
  · exact (grid_angle_mem hn hj).2
  · have hn0 : (0 : ℝ) < n := by positivity
    have hpi : (0 : ℝ) < π := pi_pos
    gcongr

theorem exists_chebQ_root_between {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    ∃ x : ℝ,
      x ∈ Set.Ioo
        (cos (((k.1 + 1 : ℕ) : ℝ) * π / n))
        (cos ((k.1 : ℝ) * π / n)) ∧
      (chebQ n).eval x = 0 := by
  let a := cos (((k.1 + 1 : ℕ) : ℝ) * π / n)
  let c := cos ((k.1 : ℝ) * π / n)
  have hac : a < c := by
    exact grid_cos_strictAnti hn (Nat.lt_succ_self k.1) (Nat.succ_le_of_lt k.2)
  have hsign :
      (chebQ n).eval a * (chebQ n).eval c < 0 := by
    simpa [a, c] using chebQ_eval_grid_mul_next_neg (n := n) (k := k.1) hn
  have hzero :
      (0 : ℝ) ∈ [[(chebQ n).eval a, (chebQ n).eval c]] := by
    rw [mem_uIcc]
    rcases (mul_neg_iff.mp hsign) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  have hiv :=
    intermediate_value_uIcc
      ((Polynomial.continuous (chebQ n)).continuousOn) hzero
  obtain ⟨x, hx, hqx⟩ := hiv
  refine ⟨x, ?_, hqx⟩
  rw [uIcc_of_le hac.le] at hx
  refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
  · intro hxa
    subst x
    exact (chebQ_eval_grid_ne_zero (n := n) (k := k.1 + 1) hn) hqx
  · intro hxc
    subst x
    exact (chebQ_eval_grid_ne_zero (n := n) (k := k.1) hn) hqx

noncomputable def chebNode {n : ℕ} (hn : 2 ≤ n) (k : Fin n) : ℝ :=
  Classical.choose (exists_chebQ_root_between hn k)

theorem chebNode_mem_interval {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    chebNode hn k ∈ Set.Ioo
      (cos (((k.1 + 1 : ℕ) : ℝ) * π / n))
      (cos ((k.1 : ℝ) * π / n)) :=
  (Classical.choose_spec (exists_chebQ_root_between hn k)).1

theorem chebNode_isRoot {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    (chebQ n).eval (chebNode hn k) = 0 :=
  (Classical.choose_spec (exists_chebQ_root_between hn k)).2

theorem chebNode_strictAnti {n : ℕ} (hn : 2 ≤ n) {i j : Fin n} (hij : i < j) :
    chebNode hn j < chebNode hn i := by
  have hi := chebNode_mem_interval hn i
  have hj := chebNode_mem_interval hn j
  have hij' : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij
  have hcos :
      cos ((j.1 : ℝ) * π / n) ≤
        cos (((i.1 + 1 : ℕ) : ℝ) * π / n) := by
    rcases hij'.eq_or_lt with h | h
    · simp [h]
    · exact (grid_cos_strictAnti hn h (Nat.le_of_lt j.2)).le
  exact (hj.2.trans_le hcos).trans hi.1

noncomputable def chebNodes (n : ℕ) (hn : 2 ≤ n) : Fin n ↪ ℝ where
  toFun := chebNode hn
  inj' := by
    intro i j h
    apply Fin.ext
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have := chebNode_strictAnti hn hij
      linarith
    · have := chebNode_strictAnti hn hji
      linarith

@[simp]
theorem chebNodes_apply {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    chebNodes n hn k = chebNode hn k :=
  rfl

theorem chebNodes_admissible {n : ℕ} (hn : 2 ≤ n) :
    Admissible (chebNodes n hn) := by
  intro k
  have hk := chebNode_mem_interval hn k
  constructor
  · exact (neg_one_le_cos _).trans hk.1.le
  · exact hk.2.le.trans (cos_le_one _)

theorem chebNodes_isRoot {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    (chebQ n).eval (chebNodes n hn k) = 0 :=
  chebNode_isRoot hn k

end Erdos1131Asymptotic
