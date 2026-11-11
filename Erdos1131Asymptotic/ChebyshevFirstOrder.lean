/-
Adapted from seanm27lol/erdos-1131-lean, commit
31574acf09ae50430c08da92288800fe7d26c7fd, under Apache-2.0.
The mathematical asymptotic result and original formalization are credited to
that source. This copy uses a separate namespace and the repository's pinned
toolchain. See THIRD_PARTY.md for the complete provenance and adaptation record.
-/

import Erdos1131Asymptotic.ChebyshevBound

/-!
# A first-order lower bound for the Chebyshev trace

This file gives an independent finite estimate for the first correction term.
The diagonal supplies `N / 2 + O(1)`.  Off the diagonal, the distance part is
summed geometrically and the Hankel part is absorbed into a uniform constant.
-/

open scoped BigOperators Matrix

namespace Erdos1131Asymptotic.ChebyshevFirstOrder

open ChebyshevBound

noncomputable section

private abbrev q : ℝ := 1 / 6

def sameParityOffDiag (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  (sameParityIndices N i).erase i

lemma mem_sameParityOffDiag_iff
    {N : ℕ} {i j : Fin (N + 1)} :
    j ∈ sameParityOffDiag N i ↔
      SameParity i.val j.val ∧ j ≠ i := by
  simp [sameParityOffDiag, sameParityIndices, and_comm]

lemma dist_half_pos_of_mem_sameParityOffDiag
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    0 < i.val.dist j.val / 2 := by
  rw [mem_sameParityOffDiag_iff] at hj
  unfold SameParity at hj
  rcases le_total i.val j.val with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    have hne : i.val ≠ j.val := by
      intro h
      apply hj.2
      exact Fin.ext h.symm
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    have hne : i.val ≠ j.val := by
      intro h
      apply hj.2
      exact Fin.ext h.symm
    omega

lemma dist_half_le_add_half_of_sameParity
    {a b : ℕ} (h : SameParity a b) :
    a.dist b / 2 ≤ (a + b) / 2 := by
  unfold SameParity at h
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    omega

lemma chebMoment_nonpos {r : ℕ} (hr : 1 ≤ r) :
    chebMoment r ≤ 0 := by
  unfold chebMoment
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 1 - 4 * (r : ℝ) ^ 2 < 0 := by nlinarith
  exact div_nonpos_of_nonneg_of_nonpos (by norm_num) hden.le

lemma neg_chebMoment_le_third {r : ℕ} (hr : 1 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 3 := by
  unfold chebMoment
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)).2
  nlinarith

lemma neg_chebMoment_le_fifteenth {r : ℕ} (hr : 2 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 15 := by
  unfold chebMoment
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 15)).2
  nlinarith

lemma neg_chebMoment_le_thirtyFive {r : ℕ} (hr : 3 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 35 := by
  unfold chebMoment
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 35)).2
  nlinarith

lemma chebH_offDiag_nonpos
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    chebH N i j ≤ 0 := by
  rw [chebH, if_pos (mem_sameParityOffDiag_iff.mp hj).1]
  apply add_nonpos
  · apply chebMoment_nonpos
    have hr := dist_half_pos_of_mem_sameParityOffDiag hj
    have hs := dist_half_le_add_half_of_sameParity
      (mem_sameParityOffDiag_iff.mp hj).1
    omega
  · exact chebMoment_nonpos
      (dist_half_pos_of_mem_sameParityOffDiag hj)

lemma neg_chebH_offDiag_le_twoThirds
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    -chebH N i j ≤ (2 : ℝ) / 3 := by
  rw [chebH, if_pos (mem_sameParityOffDiag_iff.mp hj).1]
  have hr := dist_half_pos_of_mem_sameParityOffDiag hj
  have hsle := dist_half_le_add_half_of_sameParity
    (mem_sameParityOffDiag_iff.mp hj).1
  have hs : 1 ≤ (i.val + j.val) / 2 := by omega
  linarith [neg_chebMoment_le_third hs,
    neg_chebMoment_le_third (show 1 ≤ i.val.dist j.val / 2 by omega)]

/-- A geometric estimate for the negative Chebyshev moments along any
injectively indexed positive set of distances. -/
lemma sum_neg_chebMoment_mul_pow_le
    {α : Type*}
    (s : Finset α) (e : α → ℕ)
    (hinj : Set.InjOn e s)
    (hpos : ∀ x ∈ s, 1 ≤ e x) :
    (∑ x ∈ s, (-chebMoment (e x)) * q ^ (e x)) ≤
      (13 : ℝ) / 225 := by
  classical
  have hcard :
      (s.filter fun x ↦ e x = 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  have hone :
      (∑ x ∈ s.filter (fun x ↦ e x = 1),
          (-chebMoment (e x)) * q ^ (e x)) ≤
        (1 : ℝ) / 18 := by
    calc
      (∑ x ∈ s.filter (fun x ↦ e x = 1),
          (-chebMoment (e x)) * q ^ (e x)) =
          ∑ _x ∈ s.filter (fun x ↦ e x = 1), (1 : ℝ) / 18 := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mem_filter] at hx
            rw [hx.2]
            norm_num [chebMoment]
      _ = ((s.filter fun x ↦ e x = 1).card : ℝ) * (1 / 18) := by
        simp
      _ ≤ 1 / 18 := by
        have hcard_real :
            ((s.filter fun x ↦ e x = 1).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        nlinarith
  let t := s.filter fun x ↦ e x ≠ 1
  have ht_two : ∀ x ∈ t, 2 ≤ e x := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx)
    exact (show 1 ≤ e x from hpos x hx'.1).lt_of_ne hx'.2.symm
  have htinj : Set.InjOn (fun x ↦ e x - 2) t := by
    intro a ha b hb hab
    apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    have ha2 := ht_two a ha
    have hb2 := ht_two b hb
    change e a - 2 = e b - 2 at hab
    calc
      e a = e a - 2 + 2 := (Nat.sub_add_cancel ha2).symm
      _ = e b - 2 + 2 := by rw [hab]
      _ = e b := Nat.sub_add_cancel hb2
  have htailPow :
      (∑ x ∈ t, q ^ (e x)) ≤ (1 : ℝ) / 30 := by
    have hgeom :=
      sum_one_sixth_pow_le t (fun x ↦ e x - 2) htinj
    calc
      (∑ x ∈ t, q ^ (e x)) =
          q ^ 2 * ∑ x ∈ t, q ^ (e x - 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [← pow_add]
            congr 2
            exact (Nat.add_sub_of_le (ht_two x hx)).symm
      _ ≤ q ^ 2 * (6 / 5) := by
        gcongr
      _ = (1 : ℝ) / 30 := by norm_num
  have htail :
      (∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x)) ≤
        (1 : ℝ) / 450 := by
    calc
      (∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x)) ≤
          ∑ x ∈ t, ((1 : ℝ) / 15) * q ^ (e x) := by
            gcongr with x hx
            exact neg_chebMoment_le_fifteenth (ht_two x hx)
      _ = (1 / 15) * ∑ x ∈ t, q ^ (e x) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 15) * (1 / 30) := by
        gcongr
      _ = (1 : ℝ) / 450 := by norm_num
  rw [← Finset.sum_filter_add_sum_filter_not
    s (fun x ↦ e x = 1)
    (fun x ↦ (-chebMoment (e x)) * q ^ (e x))]
  change
    (∑ x ∈ s.filter (fun x ↦ e x = 1),
        (-chebMoment (e x)) * q ^ (e x)) +
      ∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x) ≤ _
  linarith

lemma sum_dist_pow_offDiag_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityOffDiag N i,
      q ^ (i.val.dist j.val / 2)) ≤ (2 : ℝ) / 5 := by
  have hi : i ∈ sameParityIndices N i := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hsplit := Finset.sum_erase_add
    (sameParityIndices N i)
    (fun j ↦ q ^ (i.val.dist j.val / 2)) hi
  have hfull := sum_dist_div_two_le i
  have hsplit' :
      (∑ j ∈ sameParityOffDiag N i,
        q ^ (i.val.dist j.val / 2)) + 1 =
        ∑ j ∈ sameParityIndices N i,
          q ^ (i.val.dist j.val / 2) := by
    simpa [sameParityOffDiag] using hsplit
  linarith

/-- The distance-dependent negative moment contributes at most `26/225`
in any row before the factor `1/2` from `chebK`. -/
lemma sum_distance_moment_offDiag_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityOffDiag N i,
      (-chebMoment (i.val.dist j.val / 2)) *
        q ^ (i.val.dist j.val / 2)) ≤
      (26 : ℝ) / 225 := by
  let left :=
    (sameParityOffDiag N i).filter fun j ↦ j.val ≤ i.val
  let right :=
    (sameParityOffDiag N i).filter fun j ↦ ¬j.val ≤ i.val
  have hleft_inj :
      Set.InjOn (fun j : Fin (N + 1) ↦ i.val.dist j.val / 2) left := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [left, Finset.mem_filter] at ha hb
    apply Fin.ext
    change i.val.dist a.val / 2 = i.val.dist b.val / 2 at hab
    rw [Nat.dist_comm i.val a.val, Nat.dist_eq_sub_of_le ha.2,
      Nat.dist_comm i.val b.val, Nat.dist_eq_sub_of_le hb.2] at hab
    have hpa := (mem_sameParityOffDiag_iff.mp ha.1).1
    have hpb := (mem_sameParityOffDiag_iff.mp hb.1).1
    unfold SameParity at hpa hpb
    omega
  have hright_inj :
      Set.InjOn (fun j : Fin (N + 1) ↦ i.val.dist j.val / 2) right := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [right, Finset.mem_filter] at ha hb
    apply Fin.ext
    have hia : i.val ≤ a.val := Nat.le_of_not_ge ha.2
    have hib : i.val ≤ b.val := Nat.le_of_not_ge hb.2
    change i.val.dist a.val / 2 = i.val.dist b.val / 2 at hab
    rw [Nat.dist_eq_sub_of_le hia, Nat.dist_eq_sub_of_le hib] at hab
    have hpa := (mem_sameParityOffDiag_iff.mp ha.1).1
    have hpb := (mem_sameParityOffDiag_iff.mp hb.1).1
    unfold SameParity at hpa hpb
    omega
  have hleft :=
    sum_neg_chebMoment_mul_pow_le left
      (fun j ↦ i.val.dist j.val / 2) hleft_inj
      (fun j hj ↦ dist_half_pos_of_mem_sameParityOffDiag
        (Finset.mem_filter.mp hj).1)
  have hright :=
    sum_neg_chebMoment_mul_pow_le right
      (fun j ↦ i.val.dist j.val / 2) hright_inj
      (fun j hj ↦ dist_half_pos_of_mem_sameParityOffDiag
        (Finset.mem_filter.mp hj).1)
  rw [← Finset.sum_filter_add_sum_filter_not
    (sameParityOffDiag N i) (fun j ↦ j.val ≤ i.val)
    (fun j ↦ (-chebMoment (i.val.dist j.val / 2)) *
      q ^ (i.val.dist j.val / 2))]
  change
    (∑ j ∈ left,
      (-chebMoment (i.val.dist j.val / 2)) *
        q ^ (i.val.dist j.val / 2)) +
      ∑ j ∈ right,
        (-chebMoment (i.val.dist j.val / 2)) *
          q ^ (i.val.dist j.val / 2) ≤ _
  linarith

lemma sum_halfIndex_pow_le (N : ℕ) :
    (∑ i : Fin (N + 1), q ^ (i.val / 2)) ≤ (12 : ℝ) / 5 := by
  let evens :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ Even i.val
  let odds :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ ¬Even i.val
  have heven_inj :
      Set.InjOn (fun i : Fin (N + 1) ↦ i.val / 2) evens := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [evens, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    simp only [Nat.even_iff] at ha hb
    change a.val / 2 = b.val / 2 at hab
    omega
  have hodd_inj :
      Set.InjOn (fun i : Fin (N + 1) ↦ i.val / 2) odds := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [odds, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    have ha' : a.val % 2 = 1 :=
      Nat.odd_iff.mp (Nat.not_even_iff_odd.mp ha)
    have hb' : b.val % 2 = 1 :=
      Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hb)
    change a.val / 2 = b.val / 2 at hab
    omega
  have heven := sum_one_sixth_pow_le evens
    (fun i : Fin (N + 1) ↦ i.val / 2) heven_inj
  have hodd := sum_one_sixth_pow_le odds
    (fun i : Fin (N + 1) ↦ i.val / 2) hodd_inj
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (N + 1))) (fun i ↦ Even i.val)
    (fun i ↦ q ^ (i.val / 2))]
  change
    (∑ i ∈ evens, q ^ (i.val / 2)) +
      ∑ i ∈ odds, q ^ (i.val / 2) ≤ _
  linarith

/-- The Hankel geometric factor has uniformly bounded total mass. -/
lemma sum_hankel_pow_offDiag_le (N : ℕ) :
    (∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
      q ^ ((i.val + j.val) / 2)) ≤ (144 : ℝ) / 25 := by
  have hhalf := sum_halfIndex_pow_le N
  have hhalf_nonneg :
      0 ≤ ∑ i : Fin (N + 1), q ^ (i.val / 2) :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  calc
    (∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤
        ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          q ^ (i.val / 2) * q ^ (j.val / 2) := by
      gcongr with i
      calc
        (∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2)) ≤
            ∑ j ∈ sameParityOffDiag N i,
              q ^ (i.val / 2) * q ^ (j.val / 2) := by
          gcongr with j hj
          rw [← pow_add]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ ≤ ∑ j : Fin (N + 1),
              q ^ (i.val / 2) * q ^ (j.val / 2) := by
          exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ by positivity)
    _ = (∑ i : Fin (N + 1), q ^ (i.val / 2)) *
          ∑ j : Fin (N + 1), q ^ (j.val / 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (144 : ℝ) / 25 := by nlinarith

lemma chebDInvEntry_nonneg (N i : ℕ) :
    0 ≤ chebDInvEntry N i := by
  unfold chebDInvEntry
  split_ifs <;> norm_num

lemma chebDInvEntry_le_one (N i : ℕ) :
    chebDInvEntry N i ≤ 1 := by
  unfold chebDInvEntry
  split_ifs <;> norm_num

lemma chebK_symmetric (N : ℕ) (i j : Fin (N + 1)) :
    chebK N i j = chebK N j i := by
  unfold chebK
  by_cases h : SameParity i.val j.val
  · rw [if_pos h, if_pos (show SameParity j.val i.val from h.symm),
      Nat.add_comm, Nat.dist_comm]
  · rw [if_neg h, if_neg (show ¬SameParity j.val i.val by
      exact fun h' ↦ h h'.symm)]

def traceTerm (N : ℕ) (i j : Fin (N + 1)) : ℝ :=
  chebH N i j * chebDInvEntry N j.val *
    chebK N j i * chebDInvEntry N i.val

lemma traceTerm_offDiag_ge_unweighted
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    chebH N i j * chebK N i j ≤ traceTerm N i j := by
  have hH := chebH_offDiag_nonpos hj
  have hK := chebK_nonneg N i j
  have hdj0 := chebDInvEntry_nonneg N j.val
  have hdi0 := chebDInvEntry_nonneg N i.val
  have hdj1 := chebDInvEntry_le_one N j.val
  have hdi1 := chebDInvEntry_le_one N i.val
  have hw0 :
      0 ≤ chebDInvEntry N j.val * chebDInvEntry N i.val :=
    mul_nonneg hdj0 hdi0
  have hw1 :
      chebDInvEntry N j.val * chebDInvEntry N i.val ≤ 1 := by
    calc
      chebDInvEntry N j.val * chebDInvEntry N i.val ≤
          1 * chebDInvEntry N i.val :=
        mul_le_mul_of_nonneg_right hdj1 hdi0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hdi1 (by norm_num)
      _ = 1 := one_mul 1
  have hHK : chebH N i j * chebK N i j ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hH hK
  rw [traceTerm, chebK_symmetric N j i]
  calc
    chebH N i j * chebK N i j =
        (chebH N i j * chebK N i j) * 1 := by ring
    _ ≤ (chebH N i j * chebK N i j) *
          (chebDInvEntry N j.val * chebDInvEntry N i.val) :=
      mul_le_mul_of_nonpos_left hw1 hHK
    _ = chebH N i j * chebDInvEntry N j.val *
          chebK N i j * chebDInvEntry N i.val := by ring

lemma neg_chebH_mul_chebK_tail_row_le
    {N : ℕ} (i : Fin (N + 1)) (hi : 6 ≤ i.val) :
    (∑ j ∈ sameParityOffDiag N i,
      -(chebH N i j * chebK N i j)) ≤
      (1 : ℝ) / 15 +
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
  have hdist := sum_distance_moment_offDiag_le i
  have hqdist := sum_dist_pow_offDiag_le i
  calc
    (∑ j ∈ sameParityOffDiag N i,
      -(chebH N i j * chebK N i j)) ≤
        ∑ j ∈ sameParityOffDiag N i,
          (1 / 2 : ℝ) *
            ((-chebMoment (i.val.dist j.val / 2)) *
                q ^ (i.val.dist j.val / 2) +
              (1 / 35) * q ^ (i.val.dist j.val / 2) +
              (2 / 3) * q ^ ((i.val + j.val) / 2)) := by
      gcongr with j hj
      have hp := (mem_sameParityOffDiag_iff.mp hj).1
      have hr := dist_half_pos_of_mem_sameParityOffDiag hj
      have hrs := dist_half_le_add_half_of_sameParity hp
      have hs : 3 ≤ (i.val + j.val) / 2 := by
        have : 3 ≤ i.val / 2 := by omega
        omega
      have has := neg_chebMoment_le_thirtyFive hs
      have har := neg_chebMoment_le_third (show 1 ≤ i.val.dist j.val / 2 by omega)
      have hqs : 0 ≤ q ^ ((i.val + j.val) / 2) := by positivity
      have hqr : 0 ≤ q ^ (i.val.dist j.val / 2) := by positivity
      rw [chebH, if_pos hp, chebK, if_pos hp]
      have h₁ :
          (-chebMoment ((i.val + j.val) / 2)) *
              q ^ (i.val.dist j.val / 2) ≤
            (1 / 35) * q ^ (i.val.dist j.val / 2) :=
        mul_le_mul_of_nonneg_right has hqr
      have h₂ :
          ((-chebMoment (i.val.dist j.val / 2)) +
              (-chebMoment ((i.val + j.val) / 2))) *
              q ^ ((i.val + j.val) / 2) ≤
            (2 / 3) * q ^ ((i.val + j.val) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hqs
        linarith
      norm_num only [q]
      nlinarith
    _ = (1 / 2 : ℝ) *
          ((∑ j ∈ sameParityOffDiag N i,
              (-chebMoment (i.val.dist j.val / 2)) *
                q ^ (i.val.dist j.val / 2)) +
            (1 / 35) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ (i.val.dist j.val / 2) +
            (2 / 3) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ ((i.val + j.val) / 2)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) *
          ((26 / 225 : ℝ) + (1 / 35) * (2 / 5) +
            (2 / 3) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ ((i.val + j.val) / 2)) := by
      gcongr
    _ ≤ (1 : ℝ) / 15 +
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
      have hq :
          0 ≤ ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) :=
        Finset.sum_nonneg fun _ _ ↦ by positivity
      nlinarith

lemma offDiagRow_ge_of_six_le
    {N : ℕ} (i : Fin (N + 1)) (hi : 6 ≤ i.val) :
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -(1 : ℝ) / 15 -
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
  have hterm :
      ∑ j ∈ sameParityOffDiag N i,
          chebH N i j * chebK N i j ≤
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
    gcongr with j hj
    exact traceTerm_offDiag_ge_unweighted hj
  have hneg := neg_chebH_mul_chebK_tail_row_le i hi
  have hneg' :
      -(∑ j ∈ sameParityOffDiag N i,
          chebH N i j * chebK N i j) ≤
        (1 : ℝ) / 15 +
          (1 / 3) *
            ∑ j ∈ sameParityOffDiag N i,
              q ^ ((i.val + j.val) / 2) := by
    simpa only [Finset.sum_neg_distrib] using hneg
  linarith

lemma offDiagRow_ge_of_lt_six
    {N : ℕ} (i : Fin (N + 1)) (_hi : i.val < 6) :
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -(13 : ℝ) / 15 := by
  have hKsum :
      (∑ j ∈ sameParityOffDiag N i, chebK N i j) ≤
        (13 : ℝ) / 10 := by
    calc
      (∑ j ∈ sameParityOffDiag N i, chebK N i j) ≤
          ∑ j : Fin (N + 1), chebK N i j :=
        Finset.sum_le_univ_sum_of_nonneg (chebK_nonneg N i)
      _ = absRowSum (chebK N) i := by
        rw [absRowSum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (chebK_nonneg N i j)]
      _ ≤ (13 : ℝ) / 10 := rowBound_chebK N i
  calc
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        ∑ j ∈ sameParityOffDiag N i,
          (-(2 : ℝ) / 3) * chebK N i j := by
      gcongr with j hj
      calc
        (-(2 : ℝ) / 3) * chebK N i j ≤
            chebH N i j * chebK N i j := by
          apply mul_le_mul_of_nonneg_right _ (chebK_nonneg N i j)
          linarith [neg_chebH_offDiag_le_twoThirds hj]
        _ ≤ traceTerm N i j := traceTerm_offDiag_ge_unweighted hj
    _ = (-(2 : ℝ) / 3) *
          ∑ j ∈ sameParityOffDiag N i, chebK N i j := by
      rw [Finset.mul_sum]
    _ ≥ -(13 : ℝ) / 15 := by nlinarith

lemma total_offDiag_ge (N : ℕ) :
    (∑ i : Fin (N + 1),
      ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -((N + 1 : ℕ) : ℝ) / 15 - 26 / 5 - 48 / 25 := by
  let early :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ i.val < 6
  let late :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ ¬i.val < 6
  have hearly_card : early.card ≤ 6 := by
    have hcard := Finset.card_le_card_of_injOn
      (s := early) (t := Finset.range 6) (fun i : Fin (N + 1) ↦ i.val)
      (by
        intro i hi
        simp only [early, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.mpr hi)
      (by
        intro a _ b _ hab
        exact Fin.ext hab)
    simpa using hcard
  have hearly :
      (∑ i ∈ early,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        -(26 : ℝ) / 5 := by
    calc
      (∑ i ∈ early,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
          ∑ _i ∈ early, (-(13 : ℝ) / 15) := by
        gcongr with i hi
        exact offDiagRow_ge_of_lt_six i
          (Finset.mem_filter.mp hi).2
      _ = (early.card : ℝ) * (-(13 : ℝ) / 15) := by simp
      _ ≥ -(26 : ℝ) / 5 := by
        have hc : (early.card : ℝ) ≤ 6 := by exact_mod_cast hearly_card
        nlinarith
  have hlate_card : late.card ≤ N + 1 :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
  have hlate_q :
      (∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤ (144 : ℝ) / 25 := by
    calc
      (∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤
          ∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)
      _ ≤ (144 : ℝ) / 25 := sum_hankel_pow_offDiag_le N
  have hlate :
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        -((N + 1 : ℕ) : ℝ) / 15 - 48 / 25 := by
    calc
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
          ∑ i ∈ late,
            (-(1 : ℝ) / 15 -
              (1 / 3) *
                ∑ j ∈ sameParityOffDiag N i,
                  q ^ ((i.val + j.val) / 2)) := by
        gcongr with i hi
        apply offDiagRow_ge_of_six_le
        have := (Finset.mem_filter.mp hi).2
        omega
      _ = (late.card : ℝ) * (-(1 : ℝ) / 15) -
          (1 / 3) *
            ∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
              q ^ ((i.val + j.val) / 2) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, ← Finset.mul_sum]
      _ ≥ -((N + 1 : ℕ) : ℝ) / 15 - 48 / 25 := by
        have hc : (late.card : ℝ) ≤ (N + 1 : ℕ) := by
          exact_mod_cast hlate_card
        nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (N + 1))) (fun i ↦ i.val < 6)
    (fun i ↦ ∑ j ∈ sameParityOffDiag N i, traceTerm N i j)]
  change
    (∑ i ∈ early,
      ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) +
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥ _
  linarith

def interiorIndices (N : ℕ) : Finset (Fin (N + 1)) :=
  ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase (Fin.last N)

lemma interiorIndices_card
    {N : ℕ} (hN : 0 < N) :
    (interiorIndices N).card = N - 1 := by
  have hlast :
      Fin.last N ∈
        (Finset.univ : Finset (Fin (N + 1))).erase 0 := by
    simp [Fin.last, hN.ne']
  rw [interiorIndices, Finset.card_erase_of_mem hlast,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (N + 1)))]
  simp

lemma mem_interiorIndices
    {N : ℕ} {i : Fin (N + 1)}
    (hi : i ∈ interiorIndices N) :
    0 < i.val ∧ i.val < N := by
  simp only [interiorIndices, Finset.mem_erase, Finset.mem_univ,
    and_true] at hi
  have hi0 : i.val ≠ 0 := by
    intro h
    apply hi.2
    exact Fin.ext h
  have hiN : i.val ≠ N := by
    intro h
    apply hi.1
    exact Fin.ext h
  omega

lemma sum_chebMoment_interior_ge
    {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ interiorIndices N, chebMoment i.val) ≥
      -(1 : ℝ) / 2 := by
  have hlast :
      Fin.last N ∈
        (Finset.univ : Finset (Fin (N + 1))).erase 0 := by
    simp [Fin.last, hN.ne']
  have hzero := Finset.sum_erase_add
    (Finset.univ : Finset (Fin (N + 1)))
    (fun i ↦ chebMoment i.val)
    (Finset.mem_univ (0 : Fin (N + 1)))
  have hlastSum := Finset.sum_erase_add
    ((Finset.univ : Finset (Fin (N + 1))).erase 0)
    (fun i ↦ chebMoment i.val) hlast
  have hfull := sum_chebMoment_fin N
  have hsum :
      (∑ i ∈ interiorIndices N, chebMoment i.val) =
        -(N : ℝ) / (2 * N + 1) - chebMoment N := by
    change
      (∑ i ∈
        ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase
          (Fin.last N), chebMoment i.val) =
        -(N : ℝ) / (2 * N + 1) - chebMoment N
    simp only [Fin.val_zero, Fin.val_last] at hzero hlastSum
    rw [chebMoment_zero] at hzero
    have hzero' :
        (∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).erase 0,
          chebMoment x.val) =
          (∑ x : Fin (N + 1), chebMoment x.val) - 1 :=
      eq_sub_of_add_eq hzero
    have hlast' :
        (∑ x ∈
          ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase
            (Fin.last N), chebMoment x.val) =
          (∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).erase 0,
            chebMoment x.val) - chebMoment N :=
      eq_sub_of_add_eq hlastSum
    rw [hlast', hzero', hfull]
    ring
  rw [hsum]
  have hmN : chebMoment N ≤ 0 := chebMoment_nonpos hN
  have hden : (0 : ℝ) < 2 * N + 1 := by positivity
  have hfrac : (N : ℝ) / (2 * N + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hnegfrac :
      -(1 : ℝ) / 2 ≤ -(N : ℝ) / (2 * N + 1) := by
    simpa only [neg_div] using neg_le_neg hfrac
  linarith

lemma chebK_diag (N : ℕ) (i : Fin (N + 1)) :
    chebK N i i = (q ^ i.val + 1) / 2 := by
  rw [chebK, if_pos (show SameParity i.val i.val from rfl),
    Nat.dist_self, Nat.zero_div]
  have hii : (i.val + i.val) / 2 = i.val := by omega
  rw [hii, pow_zero]

lemma traceTerm_diag_nonneg (N : ℕ) (i : Fin (N + 1)) :
    0 ≤ traceTerm N i i := by
  have hH : 0 ≤ chebH N i i := by
    rw [chebH_diag]
    by_cases hi : i.val = 0
    · rw [hi, chebMoment_zero]
      norm_num
    · have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
      linarith [neg_chebMoment_le_third hi1]
  have hK := chebK_nonneg N i i
  have hd := chebDInvEntry_nonneg N i.val
  rw [traceTerm]
  positivity

lemma traceTerm_diag_ge
    {N : ℕ} {i : Fin (N + 1)}
    (hi : i ∈ interiorIndices N) :
    traceTerm N i i ≥ (1 + chebMoment i.val) / 2 := by
  have hi' := mem_interiorIndices hi
  have hi0 : i.val ≠ 0 := Nat.ne_of_gt hi'.1
  have hiN : i.val ≠ N := ne_of_lt hi'.2
  have hd : chebDInvEntry N i.val = 1 := by
    simp [chebDInvEntry, hi0, hiN]
  have hH : 0 ≤ 1 + chebMoment i.val := by
    linarith [neg_chebMoment_le_third hi'.1]
  have hK : (1 : ℝ) / 2 ≤ chebK N i i := by
    rw [chebK_diag]
    have : 0 ≤ q ^ i.val := by positivity
    linarith
  rw [traceTerm, hd, chebH_diag]
  simp only [mul_one]
  have hmul := mul_le_mul_of_nonneg_left hK hH
  nlinarith

lemma total_diag_ge
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin (N + 1), traceTerm N i i) ≥
      (N : ℝ) / 2 - 3 / 4 := by
  have hcard := interiorIndices_card hN
  have hmom := sum_chebMoment_interior_ge hN
  calc
    (∑ i : Fin (N + 1), traceTerm N i i) ≥
        ∑ i ∈ interiorIndices N, traceTerm N i i :=
      Finset.sum_le_univ_sum_of_nonneg (traceTerm_diag_nonneg N)
    _ ≥ ∑ i ∈ interiorIndices N,
        (1 + chebMoment i.val) / 2 := by
      gcongr with i hi
      exact traceTerm_diag_ge hi
    _ = ((interiorIndices N).card : ℝ) / 2 +
          (∑ i ∈ interiorIndices N, chebMoment i.val) / 2 := by
      simp only [add_div, Finset.sum_add_distrib, Finset.sum_div,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≥ (N : ℝ) / 2 - 3 / 4 := by
      have hc : ((interiorIndices N).card : ℝ) = (N - 1 : ℕ) := by
        exact_mod_cast hcard
      rw [hc]
      have hNcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]
        norm_num
      rw [hNcast]
      linarith

lemma chebDInv_mul_chebK_apply
    (N : ℕ) (j i : Fin (N + 1)) :
    (chebDInv N * chebK N) j i =
      chebDInvEntry N j.val * chebK N j i := by
  classical
  rw [chebDInv, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · simp

lemma chebDInv_mul_chebK_mul_chebDInv_apply
    (N : ℕ) (j i : Fin (N + 1)) :
    (chebDInv N * chebK N * chebDInv N) j i =
      chebDInvEntry N j.val * chebK N j i *
        chebDInvEntry N i.val := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [chebDInv_mul_chebK_apply]
    simp [chebDInv]
  · intro b _ hb
    simp [chebDInv, hb]
  · simp

lemma trace_eq_sum_traceTerm (N : ℕ) :
    Matrix.trace
      (chebH N * (chebDInv N * chebK N * chebDInv N)) =
        ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), traceTerm N i j := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change
    (chebH N * (chebDInv N * chebK N * chebDInv N)) i i =
      ∑ j : Fin (N + 1), traceTerm N i j
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [traceTerm, chebDInv_mul_chebK_mul_chebDInv_apply]
  ring

lemma traceTerm_zero_of_not_sameParity
    {N : ℕ} {i j : Fin (N + 1)}
    (h : ¬SameParity i.val j.val) :
    traceTerm N i j = 0 := by
  rw [traceTerm, chebH, if_neg h]
  ring

lemma sum_traceTerm_row_eq_diag_add_offDiag
    (N : ℕ) (i : Fin (N + 1)) :
    (∑ j : Fin (N + 1), traceTerm N i j) =
      traceTerm N i i +
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
  have hi : i ∈ sameParityIndices N i := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hrestrict :
      (∑ j ∈ sameParityIndices N i, traceTerm N i j) =
        ∑ j : Fin (N + 1), traceTerm N i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply traceTerm_zero_of_not_sameParity
    simpa [sameParityIndices] using hj
  have herase := Finset.sum_erase_add
    (sameParityIndices N i) (fun j ↦ traceTerm N i j) hi
  change
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) +
      traceTerm N i i =
        ∑ j ∈ sameParityIndices N i, traceTerm N i j at herase
  rw [← hrestrict] at *
  linarith

lemma trace_eq_diag_add_offDiag (N : ℕ) :
    Matrix.trace
      (chebH N * (chebDInv N * chebK N * chebDInv N)) =
        (∑ i : Fin (N + 1), traceTerm N i i) +
          ∑ i : Fin (N + 1),
            ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
  rw [trace_eq_sum_traceTerm]
  simp_rw [sum_traceTerm_row_eq_diag_add_offDiag]
  exact Finset.sum_add_distrib

/-- The finite first-order trace bound needed in the Chebyshev comparison. -/
theorem trace_firstOrder_lower_bound
    {N : ℕ} (hN : 6 ≤ N) :
    (13 : ℝ) * (N : ℝ) / 30 - 13 ≤
      Matrix.trace
        (chebH N * (chebDInv N * chebK N * chebDInv N)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hdiag := total_diag_ge hNpos
  have hoff := total_offDiag_ge N
  rw [trace_eq_diag_add_offDiag]
  push_cast at hoff
  linarith

end

end Erdos1131Asymptotic.ChebyshevFirstOrder
