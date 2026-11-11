import PolynomialEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The squared-gap parametrization, with collision faces included. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

def gapPrefix {A : Type*} [CommRing A] {k : ℕ}
    (gaps : Fin k → A) (i : Fin (k + 1)) : A :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < i.val), gaps j

def gapTotal {A : Type*} [CommRing A] {k : ℕ} (u : Fin k → A) : A :=
  ∑ j, u j ^ 2

def gapNodes {A : Type*} [CommRing A] {k : ℕ}
    (u : Fin k → A) (i : Fin (k + 1)) : A :=
  -gapTotal u + 2 * gapPrefix (fun j => u j ^ 2) i

theorem gapPrefix_zero {A : Type*} [CommRing A] {k : ℕ} (gaps : Fin k → A) :
    gapPrefix gaps 0 = 0 := by
  simp [gapPrefix]

theorem gapPrefix_last {A : Type*} [CommRing A] {k : ℕ} (gaps : Fin k → A) :
    gapPrefix gaps (Fin.last k) = ∑ j, gaps j := by
  have hfilter : Finset.univ.filter (fun j : Fin k => j.val < k) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    exact j.isLt
  simp only [gapPrefix, Fin.val_last, hfilter]

theorem gapPrefix_succ {A : Type*} [CommRing A] {k : ℕ}
    (gaps : Fin k → A) (i : Fin k) :
    gapPrefix gaps i.succ = gapPrefix gaps i.castSucc + gaps i := by
  have hfilter : Finset.univ.filter (fun j : Fin k => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin k => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · right
        have hv : j.val ≠ i.val := fun hv => hji (Fin.ext hv)
        omega
    · rintro (rfl | hj) <;> omega
  have hnot : i ∉ Finset.univ.filter (fun j : Fin k => j.val < i.val) := by simp
  simp only [gapPrefix, Fin.val_succ, Fin.val_castSucc, hfilter,
    Finset.sum_insert hnot, add_comm]

theorem gapNodes_zero {A : Type*} [CommRing A] {k : ℕ} (u : Fin k → A) :
    gapNodes u 0 = -gapTotal u := by simp [gapNodes, gapPrefix_zero]

theorem gapNodes_last {A : Type*} [CommRing A] {k : ℕ} (u : Fin k → A) :
    gapNodes u (Fin.last k) = gapTotal u := by
  rw [gapNodes, gapPrefix_last]
  unfold gapTotal
  ring

theorem gapNodes_succ {A : Type*} [CommRing A] {k : ℕ}
    (u : Fin k → A) (i : Fin k) :
    gapNodes u i.succ = gapNodes u i.castSucc + 2 * u i ^ 2 := by
  simp only [gapNodes, gapPrefix_succ]
  ring

theorem gapTotal_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {k : ℕ} (u : Fin k → A) :
    φ (gapTotal u) = gapTotal (fun j => φ (u j)) := by
  simp [gapTotal]

theorem gapNodes_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {k : ℕ} (u : Fin k → A) (i : Fin (k + 1)) :
    φ (gapNodes u i) = gapNodes (fun j => φ (u j)) i := by
  have htwo : φ (2 : A) = (2 : B) := by
    rw [show (2 : A) = 1 + 1 by ring, map_add, map_one]
    ring
  simp [gapNodes, gapPrefix, gapTotal, htwo]

theorem gapTotal_nonneg {k : ℕ} (u : Fin k → ℝ) : 0 ≤ gapTotal u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gapTotal_pos {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : 0 < gapTotal u := by
  apply Finset.sum_pos'
  · intro i hi
    exact sq_nonneg _
  · exact ⟨⟨0, hk⟩, Finset.mem_univ _, sq_pos_of_ne_zero (hu _)⟩

theorem gapNodes_strictMono {k : ℕ} {u : Fin k → ℝ} (hu : ∀ i, u i ≠ 0) :
    StrictMono (gapNodes u) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [gapNodes_succ]
  have hsq := sq_pos_of_ne_zero (hu i)
  linarith

theorem gapNodes_injective_iff {k : ℕ} (u : Fin k → ℝ) :
    Function.Injective (gapNodes u) ↔ ∀ i, u i ≠ 0 := by
  constructor
  · intro hinj i hi
    have heq : gapNodes u i.succ = gapNodes u i.castSucc := by
      simp only [gapNodes_succ, hi, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    have hv := congrArg Fin.val (hinj heq)
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  · intro hu
    exact (gapNodes_strictMono hu).injective

def numeratorPolynomial (k : ℕ) : MvPolynomial (Fin k) ℚ :=
  encodingNumerator (gapNodes (fun i : Fin k => MvPolynomial.X i))
    (gapTotal (fun i : Fin k => MvPolynomial.X i))

def denominatorPolynomial (k : ℕ) : MvPolynomial (Fin k) ℚ :=
  encodingDenominator (gapNodes (fun i : Fin k => MvPolynomial.X i))

theorem numeratorPolynomial_eval {k : ℕ} (u : Fin k → ℝ) :
    MvPolynomial.aeval u (numeratorPolynomial k) =
      encodingNumerator (gapNodes u) (gapTotal u) := by
  rw [numeratorPolynomial, encodingNumerator_map]
  congr 1
  · funext i
    change (MvPolynomial.aeval u).toRingHom _ = _
    rw [gapNodes_map]
    simp
  · change (MvPolynomial.aeval u).toRingHom _ = _
    rw [gapTotal_map]
    simp

theorem denominatorPolynomial_eval {k : ℕ} (u : Fin k → ℝ) :
    MvPolynomial.aeval u (denominatorPolynomial k) = encodingDenominator (gapNodes u) := by
  unfold denominatorPolynomial
  change (MvPolynomial.aeval u).toRingHom _ = _
  rw [encodingDenominator_map]
  congr 1
  funext i
  change (MvPolynomial.aeval u).toRingHom _ = _
  rw [gapNodes_map]
  simp

theorem numeratorPolynomial_eval_nonneg {k : ℕ} (u : Fin k → ℝ) :
    0 ≤ MvPolynomial.aeval u (numeratorPolynomial k) := by
  rw [numeratorPolynomial_eval]
  exact encodingNumerator_nonneg _ _

theorem denominatorPolynomial_eval_pos_iff {k : ℕ} (u : Fin k → ℝ) :
    0 < MvPolynomial.aeval u (denominatorPolynomial k) ↔ ∀ i, u i ≠ 0 := by
  rw [denominatorPolynomial_eval]
  change 0 < denominator (gapNodes u) ↔ ∀ i, u i ≠ 0
  rw [denominator_pos_iff, gapNodes_injective_iff]

theorem gapPrefix_nonneg {k : ℕ} (u : Fin k → ℝ) (i : Fin (k + 1)) :
    0 ≤ gapPrefix (fun j => u j ^ 2) i :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gapPrefix_le_total {k : ℕ} (u : Fin k → ℝ) (i : Fin (k + 1)) :
    gapPrefix (fun j => u j ^ 2) i ≤ gapTotal u := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

def normalizedGapNodes {k : ℕ} (u : Fin k → ℝ) (i : Fin (k + 1)) : ℝ :=
  gapNodes u i / gapTotal u

theorem normalizedGapNodes_admissible {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : Admissible (normalizedGapNodes u) := by
  have hT := gapTotal_pos hk hu
  constructor
  · intro i j hij
    apply (gapNodes_injective_iff u).2 hu
    exact (div_left_inj' (ne_of_gt hT)).1 hij
  · intro i
    constructor
    · apply (le_div_iff₀ hT).2
      have hprefix := gapPrefix_nonneg u i
      dsimp [gapNodes]
      linarith
    · apply (div_le_iff₀ hT).2
      have hprefix := gapPrefix_le_total u i
      dsimp [gapNodes]
      linarith

theorem normalizedGapNodes_endpoints {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) :
    normalizedGapNodes u 0 = -1 ∧ normalizedGapNodes u (Fin.last k) = 1 := by
  have hT := ne_of_gt (gapTotal_pos hk hu)
  simp [normalizedGapNodes, gapNodes_zero, gapNodes_last, hT]

theorem gapNodes_eq_affine {k : ℕ} {u : Fin k → ℝ} (hT : gapTotal u ≠ 0) :
    gapNodes u = affineNodes (normalizedGapNodes u) (gapTotal u) 0 := by
  funext i
  dsimp [affineNodes, normalizedGapNodes]
  field_simp
  ring

theorem numerator_div_denominator_eq_energy {k : ℕ} (hk : 0 < k)
    {u : Fin k → ℝ} (hu : ∀ i, u i ≠ 0) :
    MvPolynomial.aeval u (numeratorPolynomial k) /
      MvPolynomial.aeval u (denominatorPolynomial k) = energy (normalizedGapNodes u) := by
  rw [numeratorPolynomial_eval, denominatorPolynomial_eval]
  have hD : encodingDenominator (gapNodes u) ≠ 0 := by
    exact ne_of_gt ((denominator_pos_iff _).2 ((gapNodes_injective_iff u).2 hu))
  apply (div_eq_iff hD).2
  have hN := encodingNumerator_affine (normalizedGapNodes_admissible hk hu).1
    (ne_of_gt (gapTotal_pos hk hu))
  rw [← gapNodes_eq_affine (ne_of_gt (gapTotal_pos hk hu))] at hN
  simpa only [mul_comm] using hN

theorem gapPrefix_differences {k : ℕ} (nodes : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    gapPrefix (fun j => nodes j.succ - nodes j.castSucc) i = nodes i - nodes 0 := by
  induction i using Fin.induction with
  | zero => simp [gapPrefix_zero]
  | succ i ih =>
    rw [gapPrefix_succ, ih]
    ring

theorem sum_gap_differences {k : ℕ} (nodes : Fin (k + 1) → ℝ) :
    ∑ i : Fin k, (nodes i.succ - nodes i.castSucc) = nodes (Fin.last k) - nodes 0 := by
  simpa only [gapPrefix_last] using gapPrefix_differences nodes (Fin.last k)

end Erdos1131
