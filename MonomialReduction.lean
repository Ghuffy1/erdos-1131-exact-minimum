import BoundedMonomials
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Order

/-! Terminating reduction by monic pure-power equations with lower-degree tails. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

def LowerDegree {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) : Prop :=
  ∀ i a, a ∈ (tails i).support → a.degree < m

theorem replacement_degree_lt {k m : ℕ} {a b : Fin k →₀ ℕ} {i : Fin k}
    (hi : m ≤ a i) (hb : b.degree < m) :
    (a - Finsupp.single i m + b).degree < a.degree := by
  have hsingle : Finsupp.single i m ≤ a := Finsupp.single_le_iff.mpr hi
  have hsum : (a - Finsupp.single i m).degree + m = a.degree := by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hsingle)
    simpa only [map_add, Finsupp.degree_single] using h
  rw [map_add]
  omega

noncomputable def normalMonomial {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) : MvPolynomial (Fin k) R := by
  classical
  exact if h : ∃ i, m ≤ a i then
    ∑ b : (tails h.choose).support,
      MvPolynomial.C ((tails h.choose).coeff b.val) *
        normalMonomial tails htails (a - Finsupp.single h.choose m + b.val)
  else MvPolynomial.monomial a 1
termination_by a.degree
decreasing_by
  exact replacement_degree_lt h.choose_spec (htails h.choose b.val b.property)

theorem normalMonomial_of_bounded {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (ha : ∀ i, a i < m) :
    normalMonomial tails htails a = MvPolynomial.monomial a 1 := by
  have hnot : ¬ ∃ i, m ≤ a i := by
    rintro ⟨i, hi⟩
    exact (not_le_of_gt (ha i)) hi
  rw [normalMonomial, dite_eq_right hnot]

def normalForm {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    MvPolynomial (Fin k) R →ₗ[R] MvPolynomial (Fin k) R :=
  (MvPolynomial.basisMonomials (Fin k) R).constr R (normalMonomial tails htails)

theorem normalForm_monomial_one {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) :
    normalForm tails htails (MvPolynomial.monomial a 1) = normalMonomial tails htails a := by
  exact (MvPolynomial.basisMonomials (Fin k) R).constr_basis R (normalMonomial tails htails) a

theorem normalForm_boundedMonomial {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Erdos1131.BoundedIndex k (m - 1)) :
    normalForm tails htails (Erdos1131.boundedMonomial a) = Erdos1131.boundedMonomial a := by
  rw [Erdos1131.boundedMonomial, normalForm_monomial_one]
  apply normalMonomial_of_bounded
  intro i
  have hi := Erdos1131.boundedExponent_le a i
  omega

theorem normalForm_monomial {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (coefficient : R) :
    normalForm tails htails (MvPolynomial.monomial a coefficient) =
      MvPolynomial.C coefficient * normalMonomial tails htails a := by
  have hmonomial : MvPolynomial.monomial a coefficient =
      coefficient • (MvPolynomial.monomial a 1 : MvPolynomial (Fin k) R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmonomial, map_smul, normalForm_monomial_one, MvPolynomial.C_mul']

def normalSpace (R : Type*) [CommRing R] (k m : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  Submodule.span R (Set.range (Erdos1131.boundedMonomial (R := R) (k := k) (d := m - 1)))

theorem normalMonomial_mem {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) : normalMonomial tails htails a ∈ normalSpace R k m := by
  classical
  rw [normalMonomial]
  split_ifs with h
  · apply Submodule.sum_mem
    intro b hb
    rw [MvPolynomial.C_mul']
    apply Submodule.smul_mem
    exact normalMonomial_mem hm tails htails (a - Finsupp.single h.choose m + b.val)
  · have hbounded : ∀ i, a i ≤ m - 1 := by
      intro i
      have hi : ¬ m ≤ a i := fun hi => h ⟨i, hi⟩
      omega
    obtain ⟨b, hb⟩ := Erdos1131.exists_boundedIndex a hbounded
    apply Submodule.subset_span
    exact ⟨b, by simp only [Erdos1131.boundedMonomial, hb]⟩
termination_by a.degree
decreasing_by
  exact replacement_degree_lt h.choose_spec (htails h.choose b.val b.property)

theorem normalForm_mem {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) : normalForm tails htails p ∈ normalSpace R k m := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  | monomial a coefficient =>
    rw [normalForm_monomial, MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (normalMonomial_mem hm tails htails a)

theorem normalForm_eq_self_of_mem {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    {p : MvPolynomial (Fin k) R} (hp : p ∈ normalSpace R k m) :
    normalForm tails htails p = p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact normalForm_boundedMonomial hm tails htails a
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq]
  | smul coefficient p hp ih => simp only [map_smul, ih]

theorem normalForm_idempotent {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) :
    normalForm tails htails (normalForm tails htails p) = normalForm tails htails p :=
  normalForm_eq_self_of_mem hm tails htails (normalForm_mem hm tails htails p)

theorem normalForm_monomial_mul {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (p : MvPolynomial (Fin k) R) :
    normalForm tails htails (MvPolynomial.monomial a 1 * p) =
      ∑ b ∈ p.support, MvPolynomial.C (p.coeff b) * normalMonomial tails htails (a + b) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.monomial_mul_monomial, one_mul, normalForm_monomial]

theorem normalMonomial_step {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (h : ∃ i, m ≤ a i) :
    normalMonomial tails htails a =
      normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single h.choose m) 1 * tails h.choose) := by
  rw [normalMonomial, dite_eq_left h, normalForm_monomial_mul]
  exact Finset.sum_coe_sort (tails h.choose).support
    (fun b : Fin k →₀ ℕ => MvPolynomial.C ((tails h.choose).coeff b) *
      normalMonomial tails htails (a - Finsupp.single h.choose m + b))

theorem removed_coordinate_ge {k m : ℕ} {a b : Fin k →₀ ℕ} {i j : Fin k}
    (hj : m ≤ a j) (hij : i ≠ j) : m ≤ (a - Finsupp.single i m + b) j := by
  simp [Finsupp.sub_apply, Finsupp.add_apply, hij, hij.symm]
  omega

theorem subtract_after_add {k m : ℕ} {a b : Fin k →₀ ℕ} {i j : Fin k}
    (hj : m ≤ a j) (hij : i ≠ j) :
    (a - Finsupp.single i m + b) - Finsupp.single j m =
      (a - Finsupp.single i m - Finsupp.single j m) + b := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [Finsupp.sub_apply, Finsupp.add_apply, hij, hij.symm]
  · by_cases hxj : x = j
    · subst x
      simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      simp [hij, hij.symm]
      omega
    · simp [Finsupp.sub_apply, Finsupp.add_apply, hxi, hxj, Ne.symm hxi, Ne.symm hxj]

theorem subtract_comm {k m : ℕ} (a : Fin k →₀ ℕ) (i j : Fin k) :
    a - Finsupp.single i m - Finsupp.single j m =
      a - Finsupp.single j m - Finsupp.single i m := by
  ext x
  change a x - (Finsupp.single i m) x - (Finsupp.single j m) x =
    a x - (Finsupp.single j m) x - (Finsupp.single i m) x
  omega

end Erdos1131.MonomialReduction
