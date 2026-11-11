import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! The real homogeneous lift used in the all-degree E1131 construction. -/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace Erdos1131.HomogeneousLift

def IsHomogeneous {k : ℕ} (degree : ℕ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ t x, f (t • x) = t ^ degree * f x

def penalty {k : ℕ} (r : ℕ) (x : Fin k → ℝ) : ℝ :=
  ∑ i, x i ^ (2 * (r + 1))

def lift {k : ℕ} (r : ℕ) (p : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  p x + penalty r x

theorem penalty_nonneg {k : ℕ} (r : ℕ) (x : Fin k → ℝ) : 0 ≤ penalty r x := by
  apply Finset.sum_nonneg
  intro i hi
  exact (show Even (2 * (r + 1)) from ⟨r + 1, by omega⟩).pow_nonneg _

theorem penalty_pos {k : ℕ} (r : ℕ) {x : Fin k → ℝ} (hx : x ≠ 0) :
    0 < penalty r x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    apply hx
    funext i
    exact h i
  apply Finset.sum_pos'
  · intro j hj
    exact (show Even (2 * (r + 1)) from ⟨r + 1, by omega⟩).pow_nonneg _
  · exact ⟨i, Finset.mem_univ _,
      (show Even (2 * (r + 1)) from ⟨r + 1, by omega⟩).pow_pos hi⟩

theorem penalty_zero {k : ℕ} (r : ℕ) : penalty (k := k) r 0 = 0 := by
  simp [penalty]

theorem penalty_homogeneous {k : ℕ} (r : ℕ) :
    IsHomogeneous (2 * (r + 1)) (penalty (k := k) r) := by
  intro t x
  simp [penalty, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem penalty_differentiable {k : ℕ} (r : ℕ) :
    Differentiable ℝ (penalty (k := k) r) := by
  unfold penalty
  fun_prop

theorem homogeneous_zero {k degree : ℕ} {p : (Fin k → ℝ) → ℝ}
    (hd : degree ≠ 0) (hp : IsHomogeneous degree p) : p 0 = 0 := by
  have h := hp 0 0
  simpa [hd] using h

theorem euler_identity {k degree : ℕ} {p : (Fin k → ℝ) → ℝ} {x : Fin k → ℝ}
    (hp : IsHomogeneous degree p) (hpd : DifferentiableAt ℝ p x) :
    (fderiv ℝ p x) x = (degree : ℝ) * p x := by
  simpa [nsmul_eq_mul] using
    hpd.hasFDerivAt.apply_self_eq_nsmul_of_homogeneous
      (fun t y => by simpa [smul_eq_mul] using hp t y)

theorem negative_of_nonzero_critical_point {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    {x : Fin k → ℝ} (hpd : DifferentiableAt ℝ p x)
    (hx : x ≠ 0) (hcritical : fderiv ℝ (lift r p) x = 0) : p x < 0 := by
  have hgd := (penalty_differentiable (k := k) r).differentiableAt (x := x)
  have hpe := euler_identity hp hpd
  have hge := euler_identity (penalty_homogeneous r) hgd
  change fderiv ℝ (p + penalty r) x = 0 at hcritical
  rw [fderiv_add hpd hgd] at hcritical
  have hbalance := congrArg (fun L : (Fin k → ℝ) →L[ℝ] ℝ => L x) hcritical
  simp only [add_apply, zero_apply, hpe, hge] at hbalance
  have hgpos := penalty_pos r hx
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  push_cast at hbalance
  nlinarith

theorem negative_lift_exists {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    {v : Fin k → ℝ} (hv : p v < 0) : ∃ x, lift r p x < 0 := by
  have hpzero : p 0 = 0 := homogeneous_zero (by omega) hp
  have hvzero : v ≠ 0 := by
    rintro rfl
    linarith
  have hgpos : 0 < penalty r v := penalty_pos r hvzero
  let s : ℝ := Real.sqrt (-p v / (2 * penalty r v))
  have hspos : 0 < s := Real.sqrt_pos.2 (div_pos (neg_pos.2 hv) (by positivity))
  have hsquare : s ^ 2 = -p v / (2 * penalty r v) := by
    exact Real.sq_sqrt (div_nonneg (neg_nonneg.mpr hv.le) (by positivity))
  have hproduct : s ^ 2 * penalty r v = -p v / 2 := by
    have h := (eq_div_iff (by positivity : 2 * penalty r v ≠ 0)).mp hsquare
    nlinarith
  refine ⟨s • v, ?_⟩
  have hform : lift r p (s • v) = s ^ (2 * r) * (p v + s ^ 2 * penalty r v) := by
    rw [lift, hp, penalty_homogeneous r]
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    ring
  rw [hform]
  apply mul_neg_of_pos_of_neg (pow_pos hspos _)
  linarith

theorem exists_nonzero_critical_of_negative {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    (hmin : ∃ x, ∀ y, lift r p x ≤ lift r p y)
    {v : Fin k → ℝ} (hv : p v < 0) :
    ∃ x, x ≠ 0 ∧ fderiv ℝ (lift r p) x = 0 := by
  obtain ⟨w, hw⟩ := negative_lift_exists hr hp hv
  obtain ⟨x, hx⟩ := hmin
  have hxneg : lift r p x < 0 := lt_of_le_of_lt (hx w) hw
  have hxzero : x ≠ 0 := by
    rintro rfl
    have hpzero : p 0 = 0 := homogeneous_zero (by omega) hp
    simp [lift, hpzero, penalty_zero] at hxneg
  refine ⟨x, hxzero, ?_⟩
  have hlocal : IsLocalMin (lift r p) x := Filter.Eventually.of_forall hx
  exact hlocal.fderiv_eq_zero

theorem norm_pow_le_penalty {k : ℕ} (r : ℕ) (x : Fin k → ℝ) :
    ‖x‖ ^ (2 * (r + 1)) ≤ penalty r x := by
  classical
  by_cases hx : x = 0
  · simp [hx, penalty_zero]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin k => ‖x i‖) ⟨i, Finset.mem_univ _⟩
  have hn : ‖x‖ = ‖x j‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => hmax i (Finset.mem_univ _)))
    (norm_le_pi_norm x j)
  have heven : Even (2 * (r + 1)) := ⟨r + 1, by omega⟩
  calc
    ‖x‖ ^ (2 * (r + 1)) = x j ^ (2 * (r + 1)) := by
      rw [hn, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (heven.pow_nonneg _)]
    _ ≤ penalty r x := Finset.single_le_sum (fun i _ => heven.pow_nonneg (x i)) hj

theorem homogeneous_growth_bound {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p) (hpc : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |p x| ≤ C * ‖x‖ ^ (2 * r) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin k → ℝ) 1).bddAbove_image
    hpc.abs.continuousOn
  have hb : ∀ y : Fin k → ℝ, ‖y‖ ≤ 1 → |p y| ≤ max C 0 := by
    intro y hy
    exact (hC ⟨y, by simpa [Metric.mem_closedBall, dist_zero_right] using hy, rfl⟩).trans
      (le_max_left _ _)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, homogeneous_zero (by omega : 2 * r ≠ 0) hp, norm_zero, abs_zero]
    exact mul_nonneg (le_max_right _ _) (pow_nonneg (by norm_num) _)
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : Fin k → ℝ := ‖x‖⁻¹ • x
  have hny : ‖y‖ ≤ 1 := by
    simp [y, norm_smul, norm_inv, hnx]
  have hscale : ‖x‖ • y = x := by
    simp [y, smul_smul, hnx]
  have hp_scale : p x = ‖x‖ ^ (2 * r) * p y := by
    rw [← hscale, hp]
    rw [hscale]
  rw [hp_scale, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb y hny)
    (pow_nonneg (norm_nonneg x) (2 * r))

theorem global_minimum_exists {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p) (hpc : Continuous p) :
    ∃ x, ∀ y, lift r p x ≤ lift r p y := by
  obtain ⟨C, hC, hbound⟩ := homogeneous_growth_bound hr hp hpc
  let R : ℝ := C + 2
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have houtside : ∀ y : Fin k → ℝ, R ≤ ‖y‖ → 0 ≤ lift r p y := by
    intro y hy
    have hp_bound := (abs_le.mp (hbound y)).1
    have hg_bound := norm_pow_le_penalty r y
    have hnormsq : 0 ≤ ‖y‖ ^ 2 - C := by dsimp [R] at hy; nlinarith
    have hprod := mul_nonneg (pow_nonneg (norm_nonneg y) (2 * r)) hnormsq
    have hpower : ‖y‖ ^ (2 * (r + 1)) = ‖y‖ ^ (2 * r) * ‖y‖ ^ 2 := by
      rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    rw [hpower] at hg_bound
    dsimp [lift]
    nlinarith
  have hcont : Continuous (lift r p) := hpc.add (penalty_differentiable r).continuous
  have hzero : (0 : Fin k → ℝ) ∈ Metric.closedBall 0 R := by
    simpa [Metric.mem_closedBall] using hR
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨x, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall 0 R
  · exact hmin hy
  · have hxval : lift r p x ≤ 0 := by
      have h := hmin hzero
      simpa [lift, homogeneous_zero (by omega : 2 * r ≠ 0) hp, penalty_zero] using h
    have hyR : R ≤ ‖y‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le
    exact hxval.trans (houtside y hyR)

theorem exists_nonzero_critical_iff {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    (hpd : Differentiable ℝ p) :
    (∃ x, x ≠ 0 ∧ fderiv ℝ (lift r p) x = 0) ↔ ∃ x, p x < 0 := by
  constructor
  · rintro ⟨x, hx, hc⟩
    exact ⟨x, negative_of_nonzero_critical_point hr hp (hpd x) hx hc⟩
  · rintro ⟨x, hx⟩
    exact exists_nonzero_critical_of_negative hr hp
      (global_minimum_exists hr hp hpd.continuous) hx

theorem homogeneous_fderiv_zero {k degree : ℕ} (hd : 1 < degree)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous degree p)
    (hpd : DifferentiableAt ℝ p 0) : fderiv ℝ p 0 = 0 := by
  ext v
  have hline := hpd.hasFDerivAt.hasLineDerivAt v
  change HasDerivAt (fun t : ℝ => p (0 + t • v)) ((fderiv ℝ p 0) v) 0 at hline
  simp only [zero_add] at hline
  have heq : (fun t : ℝ => p (t • v)) = (fun t : ℝ => t ^ degree * p v) :=
    funext (fun t => hp t v)
  rw [heq] at hline
  have hpower : HasDerivAt (fun t : ℝ => t ^ degree * p v) 0 0 := by
    convert (hasDerivAt_pow degree (0 : ℝ)).mul_const (p v) using 1
    simp [show degree - 1 ≠ 0 by omega]
  simpa only [zero_apply] using hline.unique hpower

theorem lift_fderiv_zero {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    (hpd : DifferentiableAt ℝ p 0) : fderiv ℝ (lift r p) 0 = 0 := by
  have hgd := (penalty_differentiable (k := k) r).differentiableAt (x := 0)
  change fderiv ℝ (p + penalty r) 0 = 0
  rw [fderiv_add hpd hgd, homogeneous_fderiv_zero (by omega) hp hpd,
    homogeneous_fderiv_zero (by omega) (penalty_homogeneous r) hgd, add_zero]

theorem critical_points_singleton_iff_nonnegative {k r : ℕ} (hr : 0 < r)
    {p : (Fin k → ℝ) → ℝ} (hp : IsHomogeneous (2 * r) p)
    (hpd : Differentiable ℝ p) :
    {x | fderiv ℝ (lift r p) x = 0} = {0} ↔ ∀ x, 0 ≤ p x := by
  constructor
  · intro hset x
    by_contra hnonneg
    have hneg : p x < 0 := lt_of_not_ge hnonneg
    obtain ⟨y, hy, hcritical⟩ := (exists_nonzero_critical_iff hr hp hpd).2 ⟨x, hneg⟩
    have hymem : y ∈ ({0} : Set (Fin k → ℝ)) := by
      rw [← hset]
      exact hcritical
    exact hy (Set.mem_singleton_iff.mp hymem)
  · intro hnonneg
    ext x
    change fderiv ℝ (lift r p) x = 0 ↔ x = 0
    constructor
    · intro hcritical
      by_contra hx
      exact (not_lt_of_ge (hnonneg x))
        (negative_of_nonzero_critical_point hr hp (hpd x) hx hcritical)
    · rintro rfl
      exact lift_fderiv_zero hr hp (hpd 0)

end Erdos1131.HomogeneousLift
