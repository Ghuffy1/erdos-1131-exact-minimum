/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.ChebyshevFamily
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Root sums for the explicit Chebyshev comparison nodes

This file identifies the roots of `chebQ` with the chosen real nodes and
computes the Chebyshev moments of those roots.
-/

open scoped BigOperators

namespace Erdos1131Asymptotic

open Polynomial Polynomial.Chebyshev

private noncomputable def chebNodeMultiset {n : ℕ} (hn : 2 ≤ n) : Multiset ℝ :=
  Finset.univ.1.map (chebNodes n hn)

private theorem chebNodeMultiset_nodup {n : ℕ} (hn : 2 ≤ n) :
    (chebNodeMultiset hn).Nodup := by
  exact Finset.univ.2.map (chebNodes n hn).injective

private theorem chebNodeMultiset_le_roots {n : ℕ} (hn : 2 ≤ n) :
    chebNodeMultiset hn ≤ (chebQ n).roots := by
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ chebNodeMultiset hn
  · have hcount_left : (chebNodeMultiset hn).count x = 1 :=
      Multiset.count_eq_one_of_mem (chebNodeMultiset_nodup hn) hx
    rw [hcount_left]
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (Multiset.one_le_count_iff_mem.mpr
      ((Polynomial.mem_roots (chebQ_ne_zero hn)).mpr (chebNodes_isRoot hn k)))
  · simp [Multiset.count_eq_zero.mpr hx]

/-- The multiset of roots of `chebQ n` is exactly the multiset of the `n`
chosen comparison nodes. -/
theorem chebQ_roots_eq_nodes {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).roots = chebNodeMultiset hn := by
  symm
  apply Multiset.eq_of_le_of_card_le (chebNodeMultiset_le_roots hn)
  calc
    (chebQ n).roots.card ≤ (chebQ n).natDegree :=
      Polynomial.card_roots' (chebQ n)
    _ = n := by
      exact (Polynomial.degree_eq_iff_natDegree_eq (chebQ_ne_zero hn)).mp
        (degree_chebQ hn)
    _ = (chebNodeMultiset hn).card := by
      simp [chebNodeMultiset]

private theorem chebQ_splits {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).Splits := by
  rw [Polynomial.splits_iff_card_roots, chebQ_roots_eq_nodes hn]
  simp [chebNodeMultiset,
    (Polynomial.degree_eq_iff_natDegree_eq (chebQ_ne_zero hn)).mp (degree_chebQ hn)]

private theorem chebQ_leadingCoeff {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).leadingCoeff = (2 : ℝ) ^ (n - 1) := by
  rw [chebQ, Polynomial.leadingCoeff_sub_of_degree_lt]
  · simp
  · calc
      (Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)).degree
          = (T ℝ ((n - 2 : ℕ) : ℤ)).degree := by
              rw [Polynomial.degree_C_mul (by norm_num)]
      _ = (n - 2 : ℕ) := by simp
      _ < (n : WithBot ℕ) := by
        exact_mod_cast Nat.sub_lt (by omega) (by omega)
      _ = (T ℝ (n : ℤ)).degree := (degree_T ℝ n).symm

/-- The reciprocal polynomial whose power sums encode the Chebyshev root
sums of `chebQ`. -/
private noncomputable def liftedChebQ (n : ℕ) : ℝ[X] :=
  Polynomial.X ^ (2 * n) -
    Polynomial.C ((1 : ℝ) / 6) * Polynomial.X ^ (2 * n - 2) -
      Polynomial.C ((1 : ℝ) / 6) * Polynomial.X ^ 2 + 1

/-- Product of the reciprocal quadratics attached to the comparison nodes. -/
private noncomputable def chebQuadraticProduct {n : ℕ} (hn : 2 ≤ n) : ℝ[X] :=
  ∏ i : Fin n,
    (Polynomial.X ^ 2 -
      Polynomial.C (2 * chebNodes n hn i) * Polynomial.X + 1)

private theorem T_eval_half_add_inv (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (T ℝ (m : ℤ)).eval ((t + t⁻¹) / 2) =
      (t ^ m + t⁻¹ ^ m) / 2 := by
  induction m using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num [T_one]
  | more m hm hm1 =>
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, T_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul]
      rw [← Polynomial.C_ofNat, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      change
        (2 * ((t + t⁻¹) / 2)) *
              (T ℝ ((m : ℤ) + 1)).eval ((t + t⁻¹) / 2) -
            (T ℝ (m : ℤ)).eval ((t + t⁻¹) / 2) =
          (t ^ (m + 2) + t⁻¹ ^ (m + 2)) / 2
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega, hm1, hm]
      simp only [inv_pow]
      field_simp [ht, pow_succ]
      ring

private theorem chebQuadraticProduct_eval_zero {n : ℕ} (hn : 2 ≤ n) :
    (chebQuadraticProduct hn).eval 0 = 1 := by
  simp [chebQuadraticProduct, Polynomial.eval_prod]

private theorem liftedChebQ_eval_zero {n : ℕ} (hn : 2 ≤ n) :
    (liftedChebQ n).eval 0 = 1 := by
  have htop : 2 * n ≠ 0 := by omega
  have hnext : 2 * n - 2 ≠ 0 := by omega
  simp [liftedChebQ, htop, hnext]

private theorem chebQ_eval_eq_prod_nodes {n : ℕ} (hn : 2 ≤ n) (y : ℝ) :
    (chebQ n).eval y =
      (2 : ℝ) ^ (n - 1) * ∏ i : Fin n, (y - chebNodes n hn i) := by
  rw [(chebQ_splits hn).eval_eq_prod_roots, chebQ_leadingCoeff hn,
    chebQ_roots_eq_nodes hn]
  simp [chebNodeMultiset, Function.comp_def,
    Finset.prod_eq_multiset_prod]

private theorem chebQuadraticProduct_eval_eq_chebQ
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ≠ 0) :
    (chebQuadraticProduct hn).eval t =
      2 * t ^ n * (chebQ n).eval ((t + t⁻¹) / 2) := by
  let y : ℝ := (t + t⁻¹) / 2
  have hfactor (i : Fin n) :
      t ^ 2 - (2 * chebNodes n hn i) * t + 1 =
        (2 * t) * (y - chebNodes n hn i) := by
    dsimp [y]
    field_simp [ht]
    ring
  rw [chebQ_eval_eq_prod_nodes hn]
  simp only [chebQuadraticProduct, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_pow]
  have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    nth_rw 1 [show n = (n - 1) + 1 by omega]
    rw [pow_add]
    ring
  rw [hpow]
  ring

private theorem pow_mul_inv_pow_eq_one {t : ℝ} (ht : t ≠ 0) (m : ℕ) :
    t ^ m * t⁻¹ ^ m = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]

private theorem pow_mul_inv_pow_sub_two {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : t ≠ 0) :
    t ^ n * t⁻¹ ^ (n - 2) = t ^ 2 := by
  nth_rw 1 [← Nat.sub_add_cancel hn]
  rw [pow_add]
  calc
    t ^ (n - 2) * t ^ 2 * t⁻¹ ^ (n - 2) =
        (t ^ (n - 2) * t⁻¹ ^ (n - 2)) * t ^ 2 := by ring
    _ = t ^ 2 := by rw [pow_mul_inv_pow_eq_one ht, one_mul]

private theorem pow_mul_pow_sub_two {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    t ^ n * t ^ (n - 2) = t ^ (2 * n - 2) := by
  rw [← pow_add]
  congr 1
  omega

private theorem chebQuadraticProduct_eval_ne_zero
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ≠ 0) :
    (chebQuadraticProduct hn).eval t = (liftedChebQ n).eval t := by
  rw [chebQuadraticProduct_eval_eq_chebQ hn ht, chebQ_eval,
    T_eval_half_add_inv n ht, T_eval_half_add_inv (n - 2) ht]
  simp only [liftedChebQ, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  have hsquare : t ^ n * t ^ n = t ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    2 * t ^ n * ((t ^ n + t⁻¹ ^ n) / 2 -
          1 / 6 * ((t ^ (n - 2) + t⁻¹ ^ (n - 2)) / 2)) =
        t ^ n * t ^ n + t ^ n * t⁻¹ ^ n -
          (1 / 6) * (t ^ n * t ^ (n - 2)) -
            (1 / 6) * (t ^ n * t⁻¹ ^ (n - 2)) := by ring
    _ = t ^ (2 * n) + 1 -
          (1 / 6) * t ^ (2 * n - 2) - (1 / 6) * t ^ 2 := by
      rw [hsquare, pow_mul_inv_pow_eq_one ht,
        pow_mul_pow_sub_two hn, pow_mul_inv_pow_sub_two hn ht]
    _ = t ^ (2 * n) - 1 / 6 * t ^ (2 * n - 2) -
          1 / 6 * t ^ 2 + 1 := by ring

/-- The reciprocal quadratic product is the sparse reciprocal polynomial
associated to `chebQ`. -/
private theorem chebQuadraticProduct_eq_liftedChebQ
    {n : ℕ} (hn : 2 ≤ n) :
    chebQuadraticProduct hn = liftedChebQ n := by
  apply Polynomial.funext
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [chebQuadraticProduct_eval_zero hn, liftedChebQ_eval_zero hn]
  · exact chebQuadraticProduct_eval_ne_zero hn ht

private noncomputable def complexQuadratic (x : ℝ) : ℂ[X] :=
  Polynomial.X ^ 2 -
    Polynomial.C (2 * (x : ℂ)) * Polynomial.X + Polynomial.C 1

private theorem complexQuadratic_eq_quadratic (x : ℝ) :
    complexQuadratic x =
      Polynomial.C (1 : ℂ) * Polynomial.X ^ 2 +
        Polynomial.C (-2 * (x : ℂ)) * Polynomial.X +
          Polynomial.C 1 := by
  simp [complexQuadratic]
  ring

private theorem complexQuadratic_natDegree (x : ℝ) :
    (complexQuadratic x).natDegree = 2 := by
  rw [complexQuadratic_eq_quadratic]
  exact Polynomial.natDegree_quadratic one_ne_zero

private theorem complexQuadratic_ne_zero (x : ℝ) :
    complexQuadratic x ≠ 0 := by
  intro h
  have := complexQuadratic_natDegree x
  simp [h] at this

private theorem complexQuadratic_leadingCoeff (x : ℝ) :
    (complexQuadratic x).leadingCoeff = 1 := by
  rw [complexQuadratic_eq_quadratic]
  exact Polynomial.leadingCoeff_quadratic one_ne_zero

private theorem complexQuadratic_roots_card (x : ℝ) :
    (complexQuadratic x).roots.card = 2 := by
  rw [← (IsAlgClosed.splits (complexQuadratic x)).natDegree_eq_card_roots,
    complexQuadratic_natDegree]

private noncomputable def quadraticRootPowerSum (x : ℝ) (m : ℕ) : ℂ :=
  ((complexQuadratic x).roots.map fun z ↦ z ^ m).sum

private theorem quadraticRootPowerSum_zero (x : ℝ) :
    quadraticRootPowerSum x 0 = 2 := by
  simp [quadraticRootPowerSum, complexQuadratic_roots_card]
  norm_num

private theorem complexQuadratic_nextCoeff (x : ℝ) :
    (complexQuadratic x).nextCoeff = -2 * (x : ℂ) := by
  rw [Polynomial.nextCoeff, complexQuadratic_natDegree,
    complexQuadratic_eq_quadratic]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

private theorem quadraticRootPowerSum_one (x : ℝ) :
    quadraticRootPowerSum x 1 = 2 * (x : ℂ) := by
  have h := (IsAlgClosed.splits (complexQuadratic x)).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [complexQuadratic_nextCoeff, complexQuadratic_leadingCoeff] at h
  simpa [quadraticRootPowerSum] using (congrArg Neg.neg h).symm

private theorem complexQuadratic_root_recurrence (x : ℝ)
    {z : ℂ} (hz : z ∈ (complexQuadratic x).roots) (m : ℕ) :
    z ^ (m + 2) = 2 * (x : ℂ) * z ^ (m + 1) - z ^ m := by
  have hroot :=
    (Polynomial.mem_roots (complexQuadratic_ne_zero x)).mp hz
  simp only [Polynomial.IsRoot, complexQuadratic, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  calc
    z ^ (m + 2) = z ^ m * z ^ 2 := by
      rw [show m + 2 = m + 2 by rfl, pow_add]
    _ = z ^ m * (2 * (x : ℂ) * z - 1) := by
      congr 1
      linear_combination hroot
    _ = 2 * (x : ℂ) * z ^ (m + 1) - z ^ m := by
      rw [pow_succ]
      ring

private theorem quadraticRootPowerSum_add_two (x : ℝ) (m : ℕ) :
    quadraticRootPowerSum x (m + 2) =
      2 * (x : ℂ) * quadraticRootPowerSum x (m + 1) -
        quadraticRootPowerSum x m := by
  change
    ((complexQuadratic x).roots.map fun z ↦ z ^ (m + 2)).sum =
      2 * (x : ℂ) *
          ((complexQuadratic x).roots.map fun z ↦ z ^ (m + 1)).sum -
        ((complexQuadratic x).roots.map fun z ↦ z ^ m).sum
  rw [← Multiset.sum_map_mul_left, ← Multiset.sum_map_sub]
  congr 1
  exact Multiset.map_congr rfl fun z hz ↦
    complexQuadratic_root_recurrence x hz m

private theorem quadraticRootPowerSum_eq_two_mul_T (x : ℝ) (m : ℕ) :
    quadraticRootPowerSum x m =
      ((2 * (T ℝ (m : ℤ)).eval x : ℝ) : ℂ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [quadraticRootPowerSum_zero, T_zero]
  | one => simp [quadraticRootPowerSum_one, T_one]
  | more m hm hm1 =>
      rw [quadraticRootPowerSum_add_two, hm, hm1,
        show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, T_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul]
      rw [← Polynomial.C_ofNat, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      push_cast
      ring

private noncomputable def complexLiftedChebQ (n : ℕ) : ℂ[X] :=
  (liftedChebQ n).map Complex.ofRealHom

private theorem complexLiftedChebQ_eq_prod_quadratic
    {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedChebQ n =
      ∏ i : Fin n, complexQuadratic (chebNodes n hn i) := by
  rw [complexLiftedChebQ, ← chebQuadraticProduct_eq_liftedChebQ hn,
    chebQuadraticProduct, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [complexQuadratic]

private theorem complexLiftedChebQ_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedChebQ n ≠ 0 := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ complexQuadratic_ne_zero _

private noncomputable def complexLiftedPowerSum (n m : ℕ) : ℂ :=
  ((complexLiftedChebQ n).roots.map fun z ↦ z ^ m).sum

private theorem complexLiftedPowerSum_eq_sum_quadratic
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    complexLiftedPowerSum n m =
      ∑ i : Fin n, quadraticRootPowerSum (chebNodes n hn i) m := by
  rw [complexLiftedPowerSum, complexLiftedChebQ_eq_prod_quadratic hn,
    Polynomial.roots_prod]
  · simp [quadraticRootPowerSum, Multiset.map_bind, List.sum_ofFn]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ complexQuadratic_ne_zero _

private theorem complexLiftedPowerSum_eq_two_mul_nodeSum
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    complexLiftedPowerSum n m =
      ((2 * ∑ i : Fin n, (T ℝ (m : ℤ)).eval (chebNodes n hn i) : ℝ) : ℂ) := by
  rw [complexLiftedPowerSum_eq_sum_quadratic hn]
  simp_rw [quadraticRootPowerSum_eq_two_mul_T]
  push_cast
  rw [Finset.mul_sum]

private noncomputable def rootPowerSum (p : ℂ[X]) (m : ℕ) : ℂ :=
  (p.roots.map fun z ↦ z ^ m).sum

private theorem rootPowerSum_newton_raw (p : ℂ[X]) {k : ℕ} (hk : 0 < k) :
    rootPowerSum p k =
      (-1 : ℂ) ^ (k + 1) * k * p.roots.esymm k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℂ) ^ a.1 * p.roots.esymm a.1 *
            rootPowerSum p a.2 := by
  let s := p.roots
  have h :=
    congrArg (MvPolynomial.aeval fun z : s ↦ (z : ℂ))
      (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ k hk)
  have he (j : ℕ) :
      MvPolynomial.eval (fun z : s ↦ (z : ℂ))
          (MvPolynomial.esymm s ℂ j) = p.roots.esymm j := by
    rw [← MvPolynomial.aeval_eq_eval]
    simpa [s] using
      (MvPolynomial.aeval_esymm_eq_multiset_esymm
        (σ := s) (R := ℂ) (S := ℂ) j (fun z : s ↦ (z : ℂ)))
  have hp (j : ℕ) :
      (∑ z : s, (z : ℂ) ^ j) = rootPowerSum p j := by
    rw [Finset.sum_eq_multiset_sum]
    change
      ((Finset.univ : Finset s).val.map fun z : s ↦ (z : ℂ) ^ j).sum =
        (p.roots.map fun z ↦ z ^ j).sum
    exact congrArg Multiset.sum (by simpa [s] using
      (Multiset.map_univ s fun z : ℂ ↦ z ^ j))
  simpa [MvPolynomial.psum, he, hp] using h

private theorem complexQuadratic_monic (x : ℝ) :
    (complexQuadratic x).Monic :=
  Polynomial.Monic.def.mpr (complexQuadratic_leadingCoeff x)

private theorem complexLiftedChebQ_monic {n : ℕ} (hn : 2 ≤ n) :
    (complexLiftedChebQ n).Monic := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  exact Polynomial.monic_prod_of_monic Finset.univ
    (fun i : Fin n ↦ complexQuadratic (chebNodes n hn i))
    (fun i _ ↦ complexQuadratic_monic _)

private theorem complexLiftedChebQ_natDegree {n : ℕ} (hn : 2 ≤ n) :
    (complexLiftedChebQ n).natDegree = 2 * n := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  calc
    (∏ i : Fin n,
        complexQuadratic (chebNodes n hn i)).natDegree =
        ∑ i ∈ Finset.univ,
          (complexQuadratic (chebNodes n hn i)).natDegree := by
      exact Polynomial.natDegree_prod_of_monic
        Finset.univ (fun i : Fin n ↦ complexQuadratic (chebNodes n hn i))
        (fun i (_ : i ∈ Finset.univ) ↦ complexQuadratic_monic
          (chebNodes n hn i))
    _ = 2 * n := by
      simp [complexQuadratic_natDegree, Nat.mul_comm]

private theorem complexLiftedChebQ_coeff (n k : ℕ) :
    (complexLiftedChebQ n).coeff k =
      (if k = 2 * n then 1 else 0) -
        (1 / 6 : ℂ) * (if k = 2 * n - 2 then 1 else 0) -
          (1 / 6 : ℂ) * (if k = 2 then 1 else 0) +
            (if k = 0 then 1 else 0) := by
  simp [complexLiftedChebQ, liftedChebQ,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one]

private theorem rootPowerSum_newton (p : ℂ[X]) (hp : p.Monic)
    {k : ℕ} (hk : 0 < k) (hkdeg : k ≤ p.natDegree) :
    rootPowerSum p k =
      -(k : ℂ) * p.coeff (p.natDegree - k) -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff (p.natDegree - a.1) * rootPowerSum p a.2 := by
  have hv (j : ℕ) (hj : j ≤ p.natDegree) :
      (-1 : ℂ) ^ j * p.roots.esymm j =
        p.coeff (p.natDegree - j) := by
    have h := p.coeff_eq_esymm_roots_of_splits
      (IsAlgClosed.splits p) (k := p.natDegree - j)
        (Nat.sub_le _ _)
    rw [hp.leadingCoeff, Nat.sub_sub_self hj, one_mul] at h
    exact h.symm
  rw [rootPowerSum_newton_raw p hk]
  calc
    (-1 : ℂ) ^ (k + 1) * k * p.roots.esymm k -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℂ) ^ a.1 * p.roots.esymm a.1 *
              rootPowerSum p a.2 =
        -(k : ℂ) * ((-1 : ℂ) ^ k * p.roots.esymm k) -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            ((-1 : ℂ) ^ a.1 * p.roots.esymm a.1) *
              rootPowerSum p a.2 := by
      rw [pow_succ]
      ring
    _ = -(k : ℂ) * p.coeff (p.natDegree - k) -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            p.coeff (p.natDegree - a.1) *
              rootPowerSum p a.2 := by
      rw [hv k hkdeg]
      apply congrArg fun z ↦
        -(k : ℂ) * p.coeff (p.natDegree - k) - z
      apply Finset.sum_congr rfl
      intro a ha
      rw [hv a.1]
      have hai : a.1 ∈ Set.Ioo 0 k := (Finset.mem_filter.mp ha).2
      exact (le_trans (le_of_lt hai.2) hkdeg)

private theorem complexLiftedChebQ_coeff_from_top {n k : ℕ}
    (hk : 0 < k) (hkmax : k ≤ 2 * n - 2) :
    (complexLiftedChebQ n).coeff (2 * n - k) =
      -(1 / 6 : ℂ) * (if k = 2 then 1 else 0) -
        (1 / 6 : ℂ) * (if k = 2 * n - 2 then 1 else 0) := by
  have htop : 2 * n - k ≠ 2 * n := by omega
  have hnext : (2 * n - k = 2 * n - 2) ↔ k = 2 := by omega
  have htwo : (2 * n - k = 2) ↔ k = 2 * n - 2 := by omega
  have hzero : 2 * n - k ≠ 0 := by omega
  rw [complexLiftedChebQ_coeff]
  simp only [htop, hnext, htwo, hzero, if_false]
  split_ifs <;> ring

private theorem complexLiftedChebQ_coeff_inner {n j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hkmax : k ≤ 2 * n - 2) :
    (complexLiftedChebQ n).coeff (2 * n - j) =
      if j = 2 then -(1 / 6 : ℂ) else 0 := by
  have htop : 2 * n - j ≠ 2 * n := by omega
  have hnext : (2 * n - j = 2 * n - 2) ↔ j = 2 := by omega
  have htwo : 2 * n - j ≠ 2 := by omega
  have hzero : 2 * n - j ≠ 0 := by omega
  rw [complexLiftedChebQ_coeff]
  simp only [htop, hnext, htwo, hzero, if_false]
  split_ifs <;> ring

private theorem complexLiftedChebQ_newton_inner_sum {n k : ℕ}
    (hk : 3 ≤ k) (hkmax : k ≤ 2 * n - 2) :
    (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (complexLiftedChebQ n).coeff (2 * n - a.1) *
          rootPowerSum (complexLiftedChebQ n) a.2) =
      -(1 / 6 : ℂ) * complexLiftedPowerSum n (k - 2) := by
  have hpair :
      (2, k - 2) ∈
        (Finset.antidiagonal k).filter (fun a ↦ a.1 ∈ Set.Ioo 0 k) := by
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo]
    omega
  rw [Finset.sum_eq_single_of_mem (2, k - 2) hpair]
  · rw [complexLiftedChebQ_coeff_inner (j := 2) (k := k)
      (by omega) (by omega) hkmax]
    simp [complexLiftedPowerSum, rootPowerSum]
  · intro a ha hne
    have ha' := Finset.mem_filter.mp ha
    have hjpos : 0 < a.1 := ha'.2.1
    have hjlt : a.1 < k := ha'.2.2
    rw [complexLiftedChebQ_coeff_inner hjpos hjlt hkmax]
    have hjne : a.1 ≠ 2 := by
      intro hj
      apply hne
      apply Prod.ext
      · exact hj
      · have hadi : a.1 + a.2 = k :=
          Finset.mem_antidiagonal.mp ha'.1
        omega
    simp [hjne]

private theorem complexLiftedPowerSum_recurrence {n k : ℕ}
    (hn : 2 ≤ n) (hk : 3 ≤ k) (hkmax : k ≤ 2 * n - 2) :
    complexLiftedPowerSum n k =
      (1 / 6 : ℂ) * complexLiftedPowerSum n (k - 2) +
        if k = 2 * n - 2 then (k : ℂ) * (1 / 6 : ℂ) else 0 := by
  have hkdeg : k ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn]
    omega
  change rootPowerSum (complexLiftedChebQ n) k = _
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum hk hkmax]
  have hk2 : k ≠ 2 := by omega
  have htop2 : 2 * n - 2 ≠ 2 := by omega
  by_cases htop : k = 2 * n - 2
  · simp [htop, htop2]
    ring
  · simp [hk2, htop]

private theorem complexLiftedChebQ_newton_inner_sum_small {n k : ℕ}
    (hk : 0 < k) (hksmall : k ≤ 2) (hkmax : k ≤ 2 * n - 2) :
    (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (complexLiftedChebQ n).coeff (2 * n - a.1) *
          rootPowerSum (complexLiftedChebQ n) a.2) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  have hjpos : 0 < a.1 := ha'.2.1
  have hjlt : a.1 < k := ha'.2.2
  rw [complexLiftedChebQ_coeff_inner hjpos hjlt hkmax]
  have hjne : a.1 ≠ 2 := by omega
  simp [hjne]

private theorem complexLiftedPowerSum_one {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedPowerSum n 1 = 0 := by
  have hkmax : 1 ≤ 2 * n - 2 := by omega
  have hkdeg : 1 ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn]
    omega
  change rootPowerSum (complexLiftedChebQ n) 1 = 0
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum_small (by omega) (by omega) hkmax]
  norm_num
  omega

private theorem complexLiftedPowerSum_two {n : ℕ} (hn : 3 ≤ n) :
    complexLiftedPowerSum n 2 = 2 * (1 / 6 : ℂ) := by
  have hn2 : 2 ≤ n := by omega
  have hkmax : 2 ≤ 2 * n - 2 := by omega
  have hkdeg : 2 ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn2]
    omega
  change rootPowerSum (complexLiftedChebQ n) 2 = _
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn2) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn2,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum_small (by omega) (by omega) hkmax]
  have htop : 2 ≠ 2 * n - 2 := by omega
  simp [htop]

private theorem complexLiftedPowerSum_two_at_two :
    complexLiftedPowerSum 2 2 = 4 * (1 / 6 : ℂ) := by
  have hkdeg : 2 ≤ (complexLiftedChebQ 2).natDegree := by
    rw [complexLiftedChebQ_natDegree (by omega)]
    omega
  change rootPowerSum (complexLiftedChebQ 2) 2 = _
  rw [rootPowerSum_newton (complexLiftedChebQ 2)
      (complexLiftedChebQ_monic (by omega)) (by omega) hkdeg,
    complexLiftedChebQ_natDegree (by omega),
    complexLiftedChebQ_coeff_from_top (n := 2) (k := 2) (by omega) (by omega),
    complexLiftedChebQ_newton_inner_sum_small
      (n := 2) (k := 2) (by omega) (by omega) (by omega)]
  norm_num

private theorem complexLiftedPowerSum_of_odd {n m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 2 * n - 2) (hodd : Odd m) :
    complexLiftedPowerSum n m = 0 := by
  rcases hodd with ⟨r, rfl⟩
  induction r generalizing n with
  | zero =>
      simpa using complexLiftedPowerSum_one hn
  | succ r ih =>
      rw [complexLiftedPowerSum_recurrence hn (k := 2 * (r + 1) + 1)
        (by omega) hm]
      have htop : 2 * (r + 1) + 1 ≠ 2 * n - 2 := by omega
      rw [if_neg htop]
      rw [show 2 * (r + 1) + 1 - 2 = 2 * r + 1 by omega,
        ih hn (by omega)]
      ring

private theorem complexLiftedPowerSum_even_lt_top {n r : ℕ}
    (hn : 2 ≤ n) (hrpos : 0 < r) (hrmax : r ≤ n - 2) :
    complexLiftedPowerSum n (2 * r) = 2 * (1 / 6 : ℂ) ^ r := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
      by_cases hrzero : r = 0
      · subst r
        have hn3 : 3 ≤ n := by omega
        simpa using complexLiftedPowerSum_two hn3
      · rw [complexLiftedPowerSum_recurrence hn (k := 2 * (r + 1))
          (by omega) (by omega)]
        have htop : 2 * (r + 1) ≠ 2 * n - 2 := by omega
        rw [if_neg htop]
        rw [show 2 * (r + 1) - 2 = 2 * r by omega,
          ih hn (by omega) (by omega)]
        rw [pow_succ]
        ring

private theorem complexLiftedPowerSum_top {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedPowerSum n (2 * n - 2) =
      2 * (1 / 6 : ℂ) ^ (n - 1) +
        (2 * n - 2 : ℕ) * (1 / 6 : ℂ) := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · rw [complexLiftedPowerSum_two_at_two]
    ring
  · rw [complexLiftedPowerSum_recurrence (by omega)
      (k := 2 * n - 2) (by omega) le_rfl, if_pos rfl]
    rw [show 2 * n - 2 - 2 = 2 * (n - 2) by omega,
      complexLiftedPowerSum_even_lt_top (by omega) (by omega) le_rfl]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring

/-- Every odd Chebyshev moment of the comparison nodes, through the last
moment below the degree of the reciprocal polynomial, vanishes. -/
theorem sum_chebNodes_T_of_odd {n m : ℕ} (hn : 2 ≤ n)
    (hm : m ≤ 2 * n - 2) (hodd : Odd m) :
    ∑ i : Fin n, (T ℝ (m : ℤ)).eval (chebNodes n hn i) = 0 := by
  have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn m
  rw [complexLiftedPowerSum_of_odd hn hm hodd] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- The even Chebyshev moments strictly below the exceptional top moment. -/
theorem sum_chebNodes_T_even {n r : ℕ} (hn : 2 ≤ n)
    (hr : r ≤ n - 2) :
    ∑ i : Fin n, (T ℝ ((2 * r : ℕ) : ℤ)).eval (chebNodes n hn i) =
      if r = 0 then (n : ℝ) else ((1 : ℝ) / 6) ^ r := by
  by_cases hrzero : r = 0
  · subst r
    simp [T_zero]
  · rw [if_neg hrzero]
    have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn (2 * r)
    rw [complexLiftedPowerSum_even_lt_top hn (Nat.pos_of_ne_zero hrzero) hr] at h
    apply Complex.ofReal_injective
    push_cast at h ⊢
    apply mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num)
    exact h.symm

/-- The exceptional last even Chebyshev moment of the comparison nodes. -/
theorem sum_chebNodes_T_top {n : ℕ} (hn : 2 ≤ n) :
    ∑ i : Fin n,
        (T ℝ ((2 * (n - 1) : ℕ) : ℤ)).eval (chebNodes n hn i) =
      ((1 : ℝ) / 6) ^ (n - 1) + ((n - 1 : ℕ) : ℝ) / 6 := by
  rw [show 2 * (n - 1) = 2 * n - 2 by omega]
  have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn (2 * n - 2)
  rw [complexLiftedPowerSum_top hn] at h
  have hnat :
      ((2 * n - 2 : ℕ) : ℂ) = 2 * ((n - 1 : ℕ) : ℂ) := by
    norm_cast
    omega
  apply Complex.ofReal_injective
  push_cast at h ⊢
  rw [hnat] at h
  apply mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num)
  calc
    2 * ∑ x,
          (T ℂ ((2 * n - 2 : ℕ) : ℤ)).eval
            (chebNodes n hn x : ℂ) =
        2 * (1 / 6 : ℂ) ^ (n - 1) +
          (2 * ((n - 1 : ℕ) : ℂ)) * (1 / 6 : ℂ) := h.symm
    _ = 2 * ((1 / 6 : ℂ) ^ (n - 1) +
          ((n - 1 : ℕ) : ℂ) / 6) := by ring

end Erdos1131Asymptotic
