import MinimumBoundary
import CoefficientDegrees
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-! The ordered algebraic roots and rational samples give the original minimum. -/

open scoped BigOperators Classical

noncomputable section

namespace Erdos1131

def interiorBoundaryRoots (k : ℕ) : Finset ℝ :=
  ((boundaryRoots_finite k).inter_of_left (Set.Ioo (0 : ℝ) 2)).toFinset

theorem mem_interiorBoundaryRoots (k : ℕ) (x : ℝ) :
    x ∈ interiorBoundaryRoots k ↔ x ∈ boundaryRoots k ∧ x ∈ Set.Ioo (0 : ℝ) 2 := by
  simp [interiorBoundaryRoots]

def boundaryRoot (k : ℕ) : Fin (interiorBoundaryRoots k).card → ℝ :=
  (interiorBoundaryRoots k).orderEmbOfFin rfl

theorem boundaryRoot_strictMono (k : ℕ) : StrictMono (boundaryRoot k) :=
  ((interiorBoundaryRoots k).orderEmbOfFin rfl).strictMono

theorem boundaryRoot_mem (k : ℕ) (i : Fin (interiorBoundaryRoots k).card) :
    boundaryRoot k i ∈ interiorBoundaryRoots k :=
  Finset.orderEmbOfFin_mem _ _ i

def nextBoundaryRoot (k : ℕ) (i : Fin (interiorBoundaryRoots k).card) : ℝ :=
  if h : i.val + 1 < (interiorBoundaryRoots k).card then boundaryRoot k ⟨i.val + 1, h⟩ else 2

theorem boundaryRoot_lt_next (k : ℕ) (i : Fin (interiorBoundaryRoots k).card) :
    boundaryRoot k i < nextBoundaryRoot k i := by
  unfold nextBoundaryRoot
  split_ifs with h
  · apply boundaryRoot_strictMono k
    change i.val < i.val + 1
    omega
  · exact ((mem_interiorBoundaryRoots k _).mp (boundaryRoot_mem k i)).2.2

def boundarySample (k : ℕ) (i : Fin (interiorBoundaryRoots k).card) : ℚ :=
  (exists_rat_btwn (boundaryRoot_lt_next k i)).choose

theorem boundarySample_bounds (k : ℕ) (i : Fin (interiorBoundaryRoots k).card) :
    boundaryRoot k i < (boundarySample k i : ℝ) ∧
      (boundarySample k i : ℝ) < nextBoundaryRoot k i :=
  (exists_rat_btwn (boundaryRoot_lt_next k i)).choose_spec

def minimumRootIndex (k : ℕ) (hk : 0 < k) : Fin (interiorBoundaryRoots k).card :=
  ((interiorBoundaryRoots k).orderIsoOfFin rfl).symm
    ⟨minimum (k + 1), (mem_interiorBoundaryRoots k _).mpr
      ⟨minimum_mem_boundaryRoots hk, minimum_in_open_interval hk⟩⟩

theorem boundaryRoot_minimumRootIndex (k : ℕ) (hk : 0 < k) :
    boundaryRoot k (minimumRootIndex k hk) = minimum (k + 1) := by
  exact congrArg Subtype.val
    (((interiorBoundaryRoots k).orderIsoOfFin rfl).apply_symm_apply _)

theorem boundarySample_le_minimum_iff (k : ℕ) (hk : 0 < k)
    (j : Fin (interiorBoundaryRoots k).card) :
    (boundarySample k j : ℝ) ≤ minimum (k + 1) ↔ j < minimumRootIndex k hk := by
  constructor
  · intro hsample
    by_contra hnot
    have hindex : minimumRootIndex k hk ≤ j := le_of_not_gt hnot
    have hroot := (boundaryRoot_strictMono k).monotone hindex
    rw [boundaryRoot_minimumRootIndex] at hroot
    have hleft := (boundarySample_bounds k j).1
    linarith
  · intro hindex
    have hsucc : j.val + 1 < (interiorBoundaryRoots k).card := by
      have hi := (minimumRootIndex k hk).isLt
      change j.val < (minimumRootIndex k hk).val at hindex
      omega
    have hle : (⟨j.val + 1, hsucc⟩ : Fin (interiorBoundaryRoots k).card) ≤
        minimumRootIndex k hk := by
      change j.val + 1 ≤ (minimumRootIndex k hk).val
      change j.val < (minimumRootIndex k hk).val at hindex
      omega
    have hroot := (boundaryRoot_strictMono k).monotone hle
    rw [boundaryRoot_minimumRootIndex] at hroot
    have hright := (boundarySample_bounds k j).2
    rw [nextBoundaryRoot, dif_pos hsucc] at hright
    exact hright.le.trans hroot

def signatureSampleCount (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin (interiorBoundaryRoots k).card =>
    matrixSignature (specializedHermiteMatrix k (specializeParameter (boundarySample k j))) = 1)).card

theorem signatureSampleCount_eq_index (k : ℕ) (hk : 0 < k) :
    signatureSampleCount k = (minimumRootIndex k hk).val := by
  have hsample (j : Fin (interiorBoundaryRoots k).card) :
      matrixSignature (specializedHermiteMatrix k (specializeParameter (boundarySample k j))) = 1 ↔
        j < minimumRootIndex k hk :=
    (specializedHermite_signature_threshold hk _).trans (boundarySample_le_minimum_iff k hk j)
  have hfilter : (Finset.univ.filter (fun j : Fin (interiorBoundaryRoots k).card =>
      matrixSignature (specializedHermiteMatrix k (specializeParameter (boundarySample k j))) = 1)) =
        Finset.Iio (minimumRootIndex k hk) := by
    ext j
    simp [hsample]
  rw [signatureSampleCount, hfilter, Fin.card_Iio]

theorem signatureSampleCount_lt (k : ℕ) (hk : 0 < k) :
    signatureSampleCount k < (interiorBoundaryRoots k).card := by
  rw [signatureSampleCount_eq_index k hk]
  exact (minimumRootIndex k hk).isLt

def algebraicMinimum (n : ℕ) (hn : 0 < n) : ℝ :=
  if h : n = 1 then 2 else
    boundaryRoot (n - 1)
      ⟨signatureSampleCount (n - 1), signatureSampleCount_lt (n - 1) (by omega)⟩

theorem algebraicMinimum_eq_minimum (n : ℕ) (hn : 0 < n) :
    algebraicMinimum n hn = minimum n := by
  by_cases h : n = 1
  · subst n
    simp [algebraicMinimum, minimum_one]
  · have hk : 0 < n - 1 := by omega
    have hfin : (⟨signatureSampleCount (n - 1), signatureSampleCount_lt (n - 1) hk⟩ :
        Fin (interiorBoundaryRoots (n - 1)).card) = minimumRootIndex (n - 1) hk := by
      apply Fin.ext
      exact signatureSampleCount_eq_index (n - 1) hk
    rw [algebraicMinimum, dif_neg h, hfin, boundaryRoot_minimumRootIndex]
    congr 1
    omega

end Erdos1131
