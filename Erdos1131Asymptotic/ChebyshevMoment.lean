/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Unweighted moments of Chebyshev polynomials

The comparison-family Gram matrix uses Lebesgue measure, rather than the
classical Chebyshev weight.  This file records the corresponding elementary
moment calculation.
-/

open scoped Interval
open Polynomial

namespace Erdos1131Asymptotic

namespace ChebyshevMoment

open Polynomial.Chebyshev

lemma U_sub_two_eq_two_mul_T (m : ℤ) :
    U ℝ m - U ℝ (m - 2) = 2 * T ℝ m := by
  have hT := T_eq_U_sub_X_mul_U (R := ℝ) m
  have hU := U_sub_two ℝ m
  linear_combination -2 * hT - hU

noncomputable def primitive (m : ℤ) : ℝ[X] :=
  (2 * ((m + 1 : ℤ) : ℝ))⁻¹ • T ℝ (m + 1) -
    (2 * ((m - 1 : ℤ) : ℝ))⁻¹ • T ℝ (m - 1)

lemma derivative_primitive (m : ℤ) (hm1 : m ≠ 1) (hmneg1 : m ≠ -1) :
    (primitive m).derivative = T ℝ m := by
  have hp : ((m + 1 : ℤ) : ℝ) ≠ 0 := by
    have : m + 1 ≠ 0 := by omega
    exact_mod_cast this
  have hm : ((m - 1 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hm1
  rw [primitive, derivative_sub, derivative_smul, derivative_smul,
    T_derivative_eq_U, T_derivative_eq_U]
  have hfirst :
      (2 * ((m + 1 : ℤ) : ℝ))⁻¹ •
          ((m + 1 : ℤ) * U ℝ (m + 1 - 1)) =
        (2 : ℝ)⁻¹ • U ℝ m := by
    simp only [Int.add_sub_cancel]
    rw [← Polynomial.C_eq_intCast, ← Polynomial.smul_eq_C_mul, smul_smul]
    congr 1
    field_simp
  have hsecond :
      (2 * ((m - 1 : ℤ) : ℝ))⁻¹ •
          ((m - 1 : ℤ) * U ℝ (m - 1 - 1)) =
        (2 : ℝ)⁻¹ • U ℝ (m - 2) := by
    simp only [sub_sub]
    rw [← Polynomial.C_eq_intCast, ← Polynomial.smul_eq_C_mul, smul_smul]
    congr 1
    field_simp
  rw [hfirst, hsecond, ← smul_sub, U_sub_two_eq_two_mul_T]
  rw [← Polynomial.C_ofNat, ← Polynomial.smul_eq_C_mul, smul_smul]
  norm_num

lemma integral_eval_T_eq_primitive_sub
    (m : ℤ) (hm1 : m ≠ 1) (hmneg1 : m ≠ -1) :
    (∫ x in (-1 : ℝ)..1, (T ℝ m).eval x) =
      (primitive m).eval 1 - (primitive m).eval (-1) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x ↦ (primitive m).eval x)
    (f' := fun x ↦ (T ℝ m).eval x)
    (fun x _ ↦ by
      simpa only [derivative_primitive m hm1 hmneg1] using
        (primitive m).hasDerivAt x)
    ((by fun_prop : Continuous fun x : ℝ ↦ (T ℝ m).eval x).intervalIntegrable _ _)

lemma eval_primitive_one_sub_neg_one (m : ℤ) :
    (primitive m).eval 1 - (primitive m).eval (-1) =
      (2 * ((m + 1 : ℤ) : ℝ))⁻¹ *
          (1 - ((m + 1).negOnePow : ℝ)) -
        (2 * ((m - 1 : ℤ) : ℝ))⁻¹ *
          (1 - ((m - 1).negOnePow : ℝ)) := by
  simp only [primitive, eval_sub, eval_smul, T_eval_one, T_eval_neg_one,
    smul_eq_mul]
  ring

theorem integral_eval_T_nat_of_even (n : ℕ) (hn : Even n) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) =
      2 / (1 - (n : ℝ) ^ 2) := by
  have hn_int : Even (n : ℤ) := (Int.even_coe_nat n).mpr hn
  have hn1 : (n : ℤ) ≠ 1 := by
    rintro h
    have : n = 1 := by exact_mod_cast h
    subst n
    norm_num at hn
  have hnneg1 : (n : ℤ) ≠ -1 := by omega
  have hn1_real : (n : ℝ) ≠ 1 := by exact_mod_cast hn1
  have hminus : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hn1_real
  have hsquare : 1 - (n : ℝ) ^ 2 ≠ 0 := by
    rw [show 1 - (n : ℝ) ^ 2 = (1 - n) * (1 + n) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_comm.mpr hn1_real))
      (by positivity)
  rw [integral_eval_T_eq_primitive_sub (n : ℤ) hn1 hnneg1,
    eval_primitive_one_sub_neg_one,
    Int.negOnePow_odd _ (hn_int.add_odd odd_one),
    Int.negOnePow_odd _ (hn_int.sub_odd odd_one)]
  push_cast
  field_simp [hminus, hsquare]
  ring

theorem integral_eval_T_nat_of_odd (n : ℕ) (hn : Odd n) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) = 0 := by
  by_cases hn1 : n = 1
  · subst n
    simp [T_one]
  have hn_int : Odd (n : ℤ) := (Int.odd_coe_nat n).mpr hn
  have hn1_int : (n : ℤ) ≠ 1 := by exact_mod_cast hn1
  have hnneg1 : (n : ℤ) ≠ -1 := by omega
  rw [integral_eval_T_eq_primitive_sub (n : ℤ) hn1_int hnneg1,
    eval_primitive_one_sub_neg_one,
    Int.negOnePow_even _ (hn_int.add_odd odd_one),
    Int.negOnePow_even _ (hn_int.sub_odd odd_one)]
  norm_num

/-- The unweighted first Chebyshev moment on `[-1,1]`. -/
theorem integral_eval_T_nat (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) =
      if Even n then 2 / (1 - (n : ℝ) ^ 2) else 0 := by
  by_cases hn : Even n
  · rw [if_pos hn, integral_eval_T_nat_of_even n hn]
  · have hn' : Odd n := (Nat.not_even_iff_odd).mp hn
    rw [if_neg hn, integral_eval_T_nat_of_odd n hn']

private lemma eval_T_mul_T (j k : ℕ) (x : ℝ) :
    (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x =
      (2 : ℝ)⁻¹ *
        ((T ℝ ((j : ℤ) + (k : ℤ))).eval x +
          (T ℝ ((j : ℤ) - (k : ℤ))).eval x) := by
  have h := congrArg (Polynomial.eval x)
    (T_mul_T ℝ (j : ℤ) (k : ℤ))
  simp only [eval_mul, eval_ofNat, eval_add] at h
  linarith

/-- The product moment before simplifying the common parity condition. -/
theorem integral_eval_T_mul_T_nat_raw (j k : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x) =
      (2 : ℝ)⁻¹ *
        ((if Even (j + k) then
            2 / (1 - ((j + k : ℕ) : ℝ) ^ 2) else 0) +
          (if Even ((j : ℤ) - (k : ℤ)).natAbs then
            2 / (1 - (((j : ℤ) - (k : ℤ)).natAbs : ℝ) ^ 2) else 0)) := by
  have hsum :
      (∫ x in (-1 : ℝ)..1,
        (T ℝ ((j : ℤ) + (k : ℤ))).eval x) =
          if Even (j + k) then
            2 / (1 - ((j + k : ℕ) : ℝ) ^ 2) else 0 := by
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      integral_eval_T_nat (j + k)
  have hdiff :
      (∫ x in (-1 : ℝ)..1,
        (T ℝ ((j : ℤ) - (k : ℤ))).eval x) =
          if Even ((j : ℤ) - (k : ℤ)).natAbs then
            2 / (1 - (((j : ℤ) - (k : ℤ)).natAbs : ℝ) ^ 2) else 0 := by
    rw [← T_natAbs ℝ ((j : ℤ) - (k : ℤ))]
    exact integral_eval_T_nat ((j : ℤ) - (k : ℤ)).natAbs
  rw [intervalIntegral.integral_congr (fun x _ ↦ eval_T_mul_T j k x)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    ((by fun_prop :
      Continuous fun x : ℝ ↦
        (T ℝ ((j : ℤ) + (k : ℤ))).eval x).intervalIntegrable _ _)
    ((by fun_prop :
      Continuous fun x : ℝ ↦
        (T ℝ ((j : ℤ) - (k : ℤ))).eval x).intervalIntegrable _ _)]
  rw [hsum, hdiff]

/-- The unweighted product moment of two Chebyshev polynomials on `[-1,1]`.
It vanishes in opposite parities; in the common-parity case this is the
closed form used for the Gram matrix. -/
theorem integral_eval_T_mul_T_nat (j k : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x) =
      if Even (j + k) then
        1 / (1 - ((j : ℝ) - (k : ℝ)) ^ 2) +
          1 / (1 - ((j : ℝ) + (k : ℝ)) ^ 2)
      else 0 := by
  have hparity :
      Even ((j : ℤ) - (k : ℤ)).natAbs ↔ Even (j + k) := by
    simp only [Int.natAbs_even, Int.even_sub, Int.even_coe_nat,
      Nat.even_add]
  have habs :
      (((j : ℤ) - (k : ℤ)).natAbs : ℝ) =
        |(j : ℝ) - (k : ℝ)| := by
    calc
      (((j : ℤ) - (k : ℤ)).natAbs : ℝ) =
          ((((j : ℤ) - (k : ℤ)).natAbs : ℤ) : ℝ) := by norm_num
      _ = ((|((j : ℤ) - (k : ℤ))| : ℤ) : ℝ) := by
        rw [Int.natCast_natAbs]
      _ = |((((j : ℤ) - (k : ℤ)) : ℤ) : ℝ)| := Int.cast_abs
      _ = |(j : ℝ) - (k : ℝ)| := by push_cast; rfl
  rw [integral_eval_T_mul_T_nat_raw]
  by_cases h : Even (j + k)
  · simp only [if_pos h, if_pos (hparity.mpr h)]
    rw [habs, sq_abs]
    push_cast
    ring
  · simp only [if_neg h, if_neg (mt hparity.mp h)]
    norm_num

end ChebyshevMoment

end Erdos1131Asymptotic
