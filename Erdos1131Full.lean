/- Private complete formalization of the proposed Erdős 1131 exact-minimum construction.
Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
This file combines the individually checked exact-minimum project modules.
The main theorem is Erdos1131.erdos1131_solution.
Novelty, publication priority, external acceptance, and prize eligibility remain unverified.
-/

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false


/- Source module QuadraticSurjection. -/
section PrivateSource_QuadraticSurjection

/-! Pullback along a surjective linear map preserves both inertia indices. -/

open Module

noncomputable section

namespace Erdos1131

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [Module.Finite ℝ M]
  [AddCommGroup N] [Module ℝ N] [Module.Finite ℝ N]

theorem sigPos_comp_le (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N) :
    sigPos (Q.comp f) ≤ sigPos Q := by
  obtain ⟨V, hdim, hpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q.comp f)
  have hinj : Function.Injective (f.domRestrict V) := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hp := hpos (x - y) hne
    have hz : f (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    simpa [QuadraticMap.restrict_apply, QuadraticMap.comp_apply, hz] using hp
  have htarget : (Q.restrict (LinearMap.range (f.domRestrict V))).PosDef := by
    rintro ⟨y, x, rfl⟩ hy
    have hx : x ≠ 0 := by
      intro hx
      subst x
      simp at hy
    simpa only [QuadraticMap.restrict_apply, QuadraticMap.comp_apply,
      LinearMap.domRestrict_apply] using hpos x hx
  calc
    sigPos (Q.comp f) = Module.finrank ℝ V := hdim.symm
    _ = Module.finrank ℝ (LinearMap.range (f.domRestrict V)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q htarget

theorem sigPos_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigPos (Q.comp f) = sigPos Q := by
  apply le_antisymm (sigPos_comp_le Q f)
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hcomp : (Q.comp f).comp g = Q := by
    ext x
    simp only [QuadraticMap.comp_apply]
    exact congrArg Q (LinearMap.congr_fun hg x)
  have h := sigPos_comp_le (Q.comp f) g
  rwa [hcomp] at h

theorem sigNeg_comp_surjective (Q : QuadraticForm ℝ N) (f : M →ₗ[ℝ] N)
    (hf : Function.Surjective f) : sigNeg (Q.comp f) = sigNeg Q := by
  have hneg : (-Q).comp f = -(Q.comp f) := by
    ext x
    rfl
  simpa only [sigNeg, hneg] using sigPos_comp_surjective (-Q) f hf

end Erdos1131


end
end PrivateSource_QuadraticSurjection


/- Source module QuadraticContinuity. -/
section PrivateSource_QuadraticContinuity

/-! Positive-definite restrictions persist under a continuous perturbation. -/

open Filter
open scoped Topology

noncomputable section

namespace Erdos1131

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem posDef_eventually (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) {x₀ : X}
    (hpos : (Q x₀).PosDef) : ∀ᶠ x in 𝓝 x₀, (Q x).PosDef := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : E) 1, 0 < Q x v := by
    apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hvne : v ≠ 0 := by
      intro hz
      simp [hz] at hv
    exact (isOpen_lt continuous_const hQ).mem_nhds (hpos v hvne)
  filter_upwards [hunit] with x hx
  intro v hv
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hu : u ∈ Metric.sphere (0 : E) 1 := by
    simp [u, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, hnorm]
  have hscale : ‖v‖ • u = v := by
    simp [u, smul_smul, hnorm]
  rw [← hscale, QuadraticMap.map_smul]
  exact smul_pos (mul_pos hnormpos hnormpos) (hx u hu)

theorem sigPos_eventually_ge (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, sigPos (Q x₀) ≤ sigPos (Q x) := by
  obtain ⟨V, hdim, hpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q x₀)
  have hrestrict : Continuous (fun z : X × V => (Q z.fst).restrict V z.snd) := by
    exact hQ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := posDef_eventually (fun x => (Q x).restrict V) hrestrict hpos
  filter_upwards [hp] with x hx
  rw [← hdim]
  exact le_sigPos_of_posDef (Q x) hx

theorem sigNeg_eventually_ge (Q : X → QuadraticForm ℝ E)
    (hQ : Continuous (fun z : X × E => Q z.fst z.snd)) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, sigNeg (Q x₀) ≤ sigNeg (Q x) := by
  have hneg : Continuous (fun z : X × E => (-Q z.fst) z.snd) := hQ.neg
  exact sigPos_eventually_ge (fun x => -Q x) hneg x₀

end Erdos1131


end
end PrivateSource_QuadraticContinuity


/- Source module BoundedMonomials. -/
section PrivateSource_BoundedMonomials

/-! The finite monomial index set used for the normalized-gradient quotient. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

abbrev BoundedIndex (k d : ℕ) := Fin k → Fin (d + 1)

def boundedExponent {k d : ℕ} (a : BoundedIndex k d) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

theorem boundedExponent_apply {k d : ℕ} (a : BoundedIndex k d) (i : Fin k) :
    boundedExponent a i = (a i).val := by
  simp [boundedExponent]

theorem boundedExponent_injective (k d : ℕ) :
    Function.Injective (boundedExponent (k := k) (d := d)) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun f : Fin k →₀ ℕ => f i) hab
  simpa only [boundedExponent_apply] using h

theorem boundedExponent_le {k d : ℕ} (a : BoundedIndex k d) (i : Fin k) :
    boundedExponent a i ≤ d := by
  rw [boundedExponent_apply]
  exact Nat.le_of_lt_succ (a i).isLt

theorem exists_boundedIndex {k d : ℕ} (a : Fin k →₀ ℕ) (ha : ∀ i, a i ≤ d) :
    ∃ b : BoundedIndex k d, boundedExponent b = a := by
  refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, ?_⟩
  ext i
  simp only [boundedExponent_apply]

theorem card_boundedIndex (k d : ℕ) : Fintype.card (BoundedIndex k d) = (d + 1) ^ k := by
  simp only [BoundedIndex, Fintype.card_fun, Fintype.card_fin]

def boundedMonomial {R : Type*} [CommRing R] {k d : ℕ} (a : BoundedIndex k d) :
    MvPolynomial (Fin k) R := MvPolynomial.monomial (boundedExponent a) 1

theorem boundedMonomials_linearIndependent (R : Type*) [CommRing R] (k d : ℕ) :
    LinearIndependent R (boundedMonomial (R := R) (k := k) (d := d)) := by
  change LinearIndependent R
    (fun a : BoundedIndex k d => (MvPolynomial.basisMonomials (Fin k) R) (boundedExponent a))
  exact (MvPolynomial.basisMonomials (Fin k) R).linearIndependent.comp
    boundedExponent (boundedExponent_injective k d)

theorem boundedMonomial_coeff {R : Type*} [CommRing R] {k d : ℕ}
    (a b : BoundedIndex k d) :
    (boundedMonomial (R := R) b).coeff (boundedExponent a) =
      if a = b then 1 else 0 := by
  classical
  simp only [boundedMonomial, MvPolynomial.coeff_monomial,
    (boundedExponent_injective k d).eq_iff, eq_comm]

end Erdos1131


end
end PrivateSource_BoundedMonomials


/- Source module MonomialReduction. -/
section PrivateSource_MonomialReduction

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


end
end PrivateSource_MonomialReduction


/- Source module MonomialConfluence. -/
section PrivateSource_MonomialConfluence

/-! Independence of the first chosen pure-power reduction. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem expand_two_reductions {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ)
    (ih : ∀ b, b.degree < a.degree → ∀ i, m ≤ b i →
      normalMonomial tails htails b =
        normalForm tails htails (MvPolynomial.monomial (b - Finsupp.single i m) 1 * tails i))
    (i j : Fin k) (hi : m ≤ a i) (hj : m ≤ a j) (hij : i ≠ j) :
    normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) =
      ∑ b ∈ (tails i).support, ∑ c ∈ (tails j).support,
        MvPolynomial.C ((tails i).coeff b) * MvPolynomial.C ((tails j).coeff c) *
          normalMonomial tails htails (a - Finsupp.single i m - Finsupp.single j m + b + c) := by
  rw [normalForm_monomial_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have hsmall := replacement_degree_lt hi (htails i b hb)
  have hlarge := removed_coordinate_ge (b := b) hj hij
  rw [ih (a - Finsupp.single i m + b) hsmall j hlarge,
    subtract_after_add hj hij, normalForm_monomial_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem normalMonomial_rule {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (i : Fin k) (hi : m ≤ a i) :
    normalMonomial tails htails a =
      normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) := by
  classical
  have h : ∃ j, m ≤ a j := ⟨i, hi⟩
  let j := h.choose
  have hj : m ≤ a j := h.choose_spec
  have hstep := normalMonomial_step tails htails a h
  change normalMonomial tails htails a =
    normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single j m) 1 * tails j) at hstep
  by_cases hij : i = j
  · rw [hij]
    exact hstep
  · have ih (b : Fin k →₀ ℕ) (hb : b.degree < a.degree) (index : Fin k) (hindex : m ≤ b index) :
        normalMonomial tails htails b =
          normalForm tails htails (MvPolynomial.monomial (b - Finsupp.single index m) 1 * tails index) :=
      normalMonomial_rule tails htails b index hindex
    calc
      normalMonomial tails htails a =
          normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single j m) 1 * tails j) := hstep
      _ = ∑ b ∈ (tails j).support, ∑ c ∈ (tails i).support,
          MvPolynomial.C ((tails j).coeff b) * MvPolynomial.C ((tails i).coeff c) *
            normalMonomial tails htails (a - Finsupp.single j m - Finsupp.single i m + b + c) :=
        expand_two_reductions tails htails a ih j i hj hi (Ne.symm hij)
      _ = ∑ c ∈ (tails i).support, ∑ b ∈ (tails j).support,
          MvPolynomial.C ((tails i).coeff c) * MvPolynomial.C ((tails j).coeff b) *
            normalMonomial tails htails (a - Finsupp.single i m - Finsupp.single j m + c + b) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro b hb
        rw [subtract_comm a j i]
        have hexponent : a - Finsupp.single i m - Finsupp.single j m + b + c =
            a - Finsupp.single i m - Finsupp.single j m + c + b :=
          add_right_comm _ b c
        rw [hexponent]
        ring
      _ = normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) :=
        (expand_two_reductions tails htails a ih i j hi hj hij).symm
termination_by a.degree
decreasing_by exact hb

end Erdos1131.MonomialReduction


end
end PrivateSource_MonomialConfluence


/- Source module MonomialQuotient. -/
section PrivateSource_MonomialQuotient

/-! The normal-form map and the quotient by the pure-power relations. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

def relation {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) (i : Fin k) : MvPolynomial (Fin k) R :=
  MvPolynomial.X i ^ m - tails i

def relationIdeal {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range (relation m tails))

abbrev RelationQuotient {R : Type*} [CommRing R] {k : ℕ} (m : ℕ)
    (tails : Fin k → MvPolynomial (Fin k) R) :=
  (MvPolynomial (Fin k) R) ⧸ relationIdeal m tails

theorem normalForm_monomial_mul_relation {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (i : Fin k) :
    normalForm tails htails (MvPolynomial.monomial a 1 * relation m tails i) = 0 := by
  unfold relation
  rw [mul_sub, map_sub, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, one_mul, normalForm_monomial_one]
  apply sub_eq_zero.mpr
  have hi : m ≤ (a + Finsupp.single i m) i := by simp
  have h := normalMonomial_rule tails htails (a + Finsupp.single i m) i hi
  simpa only [add_tsub_cancel_right] using h

theorem normalForm_mul_relation {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) (i : Fin k) :
    normalForm tails htails (p * relation m tails i) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, add_zero]
  | monomial a coefficient =>
    have hmonomial : MvPolynomial.monomial a coefficient =
        coefficient • (MvPolynomial.monomial a 1 : MvPolynomial (Fin k) R) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hmonomial, smul_mul_assoc, map_smul, normalForm_monomial_mul_relation, smul_zero]

theorem normalForm_zero_of_mem_ideal {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    {p : MvPolynomial (Fin k) R} (hp : p ∈ relationIdeal m tails) :
    normalForm tails htails p = 0 := by
  change p ∈ Ideal.span (Set.range (relation m tails)) at hp
  obtain ⟨coefficients, hcoefficients⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  rw [← hcoefficients, map_sum]
  exact Finset.sum_eq_zero (fun i hi => normalForm_mul_relation tails htails (coefficients i) i)

def quotientNormalForm {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    RelationQuotient m tails →ₗ[R] MvPolynomial (Fin k) R :=
  ((relationIdeal m tails).restrictScalars R).liftQ (normalForm tails htails)
    (fun p hp => normalForm_zero_of_mem_ideal tails htails hp) |>.comp
      (Submodule.Quotient.restrictScalarsEquiv R (relationIdeal m tails)).symm.toLinearMap

theorem quotientNormalForm_mk {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) :
    quotientNormalForm tails htails (Ideal.Quotient.mk (relationIdeal m tails) p) =
      normalForm tails htails p := by
  rfl

theorem monomial_mul_expand {R : Type*} [CommRing R] {k : ℕ}
    (a : Fin k →₀ ℕ) (p : MvPolynomial (Fin k) R) :
    MvPolynomial.monomial a 1 * p =
      ∑ b ∈ p.support, MvPolynomial.C (p.coeff b) * MvPolynomial.monomial (a + b) 1 := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.C_mul_monomial, mul_one]

end Erdos1131.MonomialReduction


end
end PrivateSource_MonomialQuotient


/- Source module QuotientBasis. -/
section PrivateSource_QuotientBasis

/-! The bounded monomials form a basis over every coefficient ring. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem normalMonomial_quotient {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) :
    Ideal.Quotient.mk (relationIdeal m tails) (normalMonomial tails htails a) =
      Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1) := by
  classical
  let projection := Ideal.Quotient.mk (relationIdeal m tails)
  change projection (normalMonomial tails htails a) = projection (MvPolynomial.monomial a 1)
  rw [normalMonomial]
  split_ifs with h
  · have hsum := Finset.sum_coe_sort (tails h.choose).support
      (fun b : Fin k →₀ ℕ => MvPolynomial.C ((tails h.choose).coeff b) *
        normalMonomial tails htails (a - Finsupp.single h.choose m + b))
    rw [hsum, map_sum]
    have hrelation : projection (MvPolynomial.X h.choose ^ m) = projection (tails h.choose) := by
      have hmem : relation m tails h.choose ∈ relationIdeal m tails :=
        Ideal.subset_span ⟨h.choose, rfl⟩
      have hz : projection (relation m tails h.choose) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa only [relation, map_sub, sub_eq_zero] using hz
    calc
      (∑ b ∈ (tails h.choose).support, projection
          (MvPolynomial.C ((tails h.choose).coeff b) *
            normalMonomial tails htails (a - Finsupp.single h.choose m + b))) =
          ∑ b ∈ (tails h.choose).support, projection
            (MvPolynomial.C ((tails h.choose).coeff b) *
              MvPolynomial.monomial (a - Finsupp.single h.choose m + b) 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [map_mul, map_mul, normalMonomial_quotient tails htails]
      _ = projection (MvPolynomial.monomial (a - Finsupp.single h.choose m) 1 * tails h.choose) := by
        rw [monomial_mul_expand, map_sum]
      _ = projection (MvPolynomial.monomial a 1) := by
        rw [map_mul, ← hrelation, ← map_mul, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul_monomial, one_mul,
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h.choose_spec)]
  · rfl
termination_by a.degree
decreasing_by exact replacement_degree_lt h.choose_spec (htails h.choose b hb)

theorem normalForm_quotient {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) :
    Ideal.Quotient.mk (relationIdeal m tails) (normalForm tails htails p) =
      Ideal.Quotient.mk (relationIdeal m tails) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial a coefficient =>
    rw [normalForm_monomial, map_mul, normalMonomial_quotient, ← map_mul,
      MvPolynomial.C_mul_monomial, mul_one]

def quotientMonomial {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (a : Erdos1131.BoundedIndex k (m - 1)) :
    RelationQuotient m tails :=
  Ideal.Quotient.mk (relationIdeal m tails) (Erdos1131.boundedMonomial a)

theorem quotientMonomials_linearIndependent {R : Type*} [CommRing R] {k m : ℕ}
    (hm : 0 < m) (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    LinearIndependent R (quotientMonomial (m := m) tails) := by
  have hcomp : LinearIndependent R
      (fun a => quotientNormalForm tails htails (quotientMonomial (m := m) tails a)) := by
    simpa only [quotientMonomial, quotientNormalForm_mk, normalForm_boundedMonomial hm]
      using Erdos1131.boundedMonomials_linearIndependent R k (m - 1)
  exact LinearIndependent.of_comp (quotientNormalForm tails htails) hcomp

theorem quotientMonomials_span {R : Type*} [CommRing R] {k m : ℕ}
    (hm : 0 < m) (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Submodule.span R (Set.range (quotientMonomial (m := m) tails)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← normalForm_quotient tails htails p]
  let projection := (Ideal.Quotient.mkₐ R (relationIdeal m tails)).toLinearMap
  have hmem : projection (normalForm tails htails p) ∈
      Submodule.map projection (normalSpace R k m) :=
    ⟨normalForm tails htails p, normalForm_mem hm tails htails p, rfl⟩
  rw [normalSpace, Submodule.map_span] at hmem
  rw [← Set.range_comp] at hmem
  exact hmem

def quotientBasis {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Basis (Erdos1131.BoundedIndex k (m - 1)) R (RelationQuotient m tails) :=
  Basis.mk (quotientMonomials_linearIndependent hm tails htails)
    (by rw [quotientMonomials_span hm tails htails])

theorem quotientBasis_apply {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Erdos1131.BoundedIndex k (m - 1)) :
    quotientBasis hm tails htails a = quotientMonomial tails a := by
  simp [quotientBasis]

end Erdos1131.MonomialReduction


end
end PrivateSource_QuotientBasis


/- Source module Erdos1131. -/
section PrivateSource_Erdos1131

/-!
# Erdős problem 1131

The definitions in this file use arbitrary distinct real nodes in `[-1, 1]`,
unit cardinal weights, and ordinary Lebesgue measure.

The all-degree algebraic value rule is proved in `CompleteSolution.lean`.
The accompanying paper gives the mathematical construction and proof.
-/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def Admissible {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1) 1

def cardinalPolynomial {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes i

def cardinal {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  (cardinalPolynomial nodes i).eval x

def squareSumPolynomial {n : ℕ} (nodes : Fin n → ℝ) : ℝ[X] :=
  ∑ i, cardinalPolynomial nodes i ^ 2

def squareSum {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, cardinal nodes i x ^ 2

def energy {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, squareSum nodes x

def minimum (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v}

theorem cardinal_eq_product {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    cardinal nodes i x =
      ∏ j ∈ Finset.univ.erase i, (x - nodes j) / (nodes i - nodes j) := by
  simp only [cardinal, cardinalPolynomial, Lagrange.basis, Polynomial.eval_prod,
    Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem cardinal_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i j : Fin n) :
    cardinal nodes i (nodes j) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [cardinal, cardinalPolynomial]
    exact Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ i)
  · simp [cardinal, cardinalPolynomial, hij]

theorem sum_cardinal {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (x : ℝ) : ∑ i, cardinal nodes i x = 1 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hpoly := Lagrange.sum_basis hinj.injOn hne
  have heval := congrArg (Polynomial.eval x) hpoly
  simpa [cardinal, cardinalPolynomial, Polynomial.eval_finsetSum] using heval

theorem squareSum_eq_eval {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) :
    squareSum nodes x = (squareSumPolynomial nodes).eval x := by
  simp only [squareSum, squareSumPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, cardinal]

theorem continuous_squareSum {n : ℕ} (nodes : Fin n → ℝ) :
    Continuous (squareSum nodes) := by
  simpa only [← squareSum_eq_eval] using (squareSumPolynomial nodes).continuous

theorem intervalIntegrable_squareSum {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) :
    IntervalIntegrable (squareSum nodes) volume a b :=
  (continuous_squareSum nodes).intervalIntegrable a b

theorem squareSum_nonneg {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) :
    0 ≤ squareSum nodes x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (cardinal nodes i x)

theorem energy_nonneg {n : ℕ} (nodes : Fin n → ℝ) : 0 ≤ energy nodes := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact squareSum_nonneg nodes x

theorem squareSum_lower_bound {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (x : ℝ) :
    1 / (n : ℝ) ≤ squareSum nodes x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) (fun i => cardinal nodes i x)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sum_cardinal hn hinj, one_pow] at h
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  simpa [squareSum, mul_comm] using h

theorem energy_lower_bound {n : ℕ} (hn : 0 < n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) : 2 / (n : ℝ) ≤ energy nodes := by
  have h := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1)
    (f := fun _ => 1 / (n : ℝ)) (g := squareSum nodes) (by norm_num)
    (continuous_const.intervalIntegrable _ _) (intervalIntegrable_squareSum nodes _ _)
    (fun x _ => squareSum_lower_bound hn hinj x)
  norm_num [energy, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] at h ⊢
  exact h

theorem energy_one (nodes : Fin 1 → ℝ) : energy nodes = 2 := by
  have hb : ∀ i : Fin 1, cardinalPolynomial nodes i = 1 := by
    intro i
    fin_cases i
    simp [cardinalPolynomial, Lagrange.basis]
  norm_num [energy, squareSum, cardinal, hb, intervalIntegral.integral_const]

def referenceNodes (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ) / n

theorem referenceNodes_admissible {n : ℕ} (hn : 0 < n) :
    Admissible (referenceNodes n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · intro i j hij
    apply Fin.ext
    have hc : (i.val : ℝ) = j.val := by
      apply (div_left_inj' (ne_of_gt hnR)).mp
      exact hij
    exact_mod_cast hc
  · intro i
    constructor
    · have : (0 : ℝ) ≤ referenceNodes n i := div_nonneg (Nat.cast_nonneg _) hnR.le
      linarith
    · apply le_of_lt
      exact (div_lt_one hnR).2 (by exact_mod_cast i.isLt)

theorem attainableValues_nonempty {n : ℕ} (hn : 0 < n) :
    Set.Nonempty {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v} :=
  ⟨energy (referenceNodes n), referenceNodes n, referenceNodes_admissible hn, rfl⟩

theorem attainableValues_bddBelow (n : ℕ) :
    BddBelow {v : ℝ | ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = v} := by
  refine ⟨0, ?_⟩
  rintro v ⟨nodes, _, rfl⟩
  exact energy_nonneg nodes

theorem minimum_le_energy {n : ℕ} {nodes : Fin n → ℝ}
    (h : Admissible nodes) : minimum n ≤ energy nodes := by
  exact csInf_le (attainableValues_bddBelow n) ⟨nodes, h, rfl⟩

theorem minimum_lower_bound {n : ℕ} (hn : 0 < n) : 2 / (n : ℝ) ≤ minimum n := by
  apply le_csInf (attainableValues_nonempty hn)
  rintro v ⟨nodes, h, rfl⟩
  exact energy_lower_bound hn h.1

theorem minimum_one : minimum 1 = 2 := by
  apply le_antisymm
  · simpa [energy_one] using minimum_le_energy (referenceNodes_admissible (by decide : 0 < 1))
  · simpa using minimum_lower_bound (by decide : 0 < 1)

/-! ## Rational polynomial moments -/

def moment (k : ℕ) : ℚ :=
  (1 - (-1 : ℚ) ^ (k + 1)) / (k + 1)

def polynomialMoment (p : ℚ[X]) : ℚ :=
  p.sum fun k a => a * moment k

theorem polynomialMoment_add (p q : ℚ[X]) :
    polynomialMoment (p + q) = polynomialMoment p + polynomialMoment q := by
  exact Polynomial.sum_add_index p q (fun k a => a * moment k)
    (fun _ => by simp) (fun _ _ _ => add_mul _ _ _)

theorem polynomialMoment_monomial (k : ℕ) (a : ℚ) :
    polynomialMoment (Polynomial.monomial k a) = a * moment k := by
  exact Polynomial.sum_monomial_index a (fun j b => b * moment j) (by simp)

theorem integral_mapped_rational_polynomial (p : ℚ[X]) :
    (polynomialMoment p : ℝ) =
      ∫ x in (-1 : ℝ)..1, (p.map (algebraMap ℚ ℝ)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [polynomialMoment_add, Rat.cast_add, hp, hq, Polynomial.map_add]
    simp only [Polynomial.eval_add]
    exact (intervalIntegral.integral_add
      ((p.map (algebraMap ℚ ℝ)).continuous.intervalIntegrable _ _)
      ((q.map (algebraMap ℚ ℝ)).continuous.intervalIntegrable _ _)).symm
  | monomial k a =>
    rw [polynomialMoment_monomial]
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial, Rat.cast_mul]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [moment]

def rationalCardinalSquareSum {n : ℕ} (nodes : Fin n → ℚ) : ℚ[X] :=
  ∑ i, Lagrange.basis Finset.univ nodes i ^ 2

def rationalEnergy {n : ℕ} (nodes : Fin n → ℚ) : ℚ :=
  polynomialMoment (rationalCardinalSquareSum nodes)

theorem map_rational_cardinal {n : ℕ} (nodes : Fin n → ℚ) (i : Fin n) :
    (Lagrange.basis Finset.univ nodes i).map (algebraMap ℚ ℝ) =
      cardinalPolynomial (fun j => (nodes j : ℝ)) i := by
  simp [cardinalPolynomial, Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod]

theorem map_rational_squareSum {n : ℕ} (nodes : Fin n → ℚ) :
    (rationalCardinalSquareSum nodes).map (algebraMap ℚ ℝ) =
      squareSumPolynomial (fun j => (nodes j : ℝ)) := by
  simp only [rationalCardinalSquareSum, Polynomial.map_sum, Polynomial.map_pow,
    map_rational_cardinal, squareSumPolynomial]

theorem rationalEnergy_eq_energy {n : ℕ} (nodes : Fin n → ℚ) :
    (rationalEnergy nodes : ℝ) = energy (fun j => (nodes j : ℝ)) := by
  rw [rationalEnergy, integral_mapped_rational_polynomial, map_rational_squareSum]
  simp_rw [energy, squareSum_eq_eval]

/-! ## Affine covariance of the cardinal functions -/

def affineNodes {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) : Fin n → ℝ :=
  fun i => a * nodes i + b

theorem cardinal_affine {n : ℕ} (nodes : Fin n → ℝ) {a : ℝ} (ha : a ≠ 0)
    (b x : ℝ) (i : Fin n) :
    cardinal (affineNodes nodes a b) i (a * x + b) = cardinal nodes i x := by
  rw [cardinal_eq_product, cardinal_eq_product]
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [affineNodes]
  rw [show a * x + b - (a * nodes j + b) = a * (x - nodes j) by ring]
  rw [show a * nodes i + b - (a * nodes j + b) = a * (nodes i - nodes j) by ring]
  exact mul_div_mul_left _ _ ha

theorem squareSum_affine {n : ℕ} (nodes : Fin n → ℝ) {a : ℝ} (ha : a ≠ 0)
    (b x : ℝ) :
    squareSum (affineNodes nodes a b) (a * x + b) = squareSum nodes x := by
  simp only [squareSum, cardinal_affine nodes ha]

theorem integral_squareSum_affine {n : ℕ} (nodes : Fin n → ℝ)
    {a : ℝ} (ha : a ≠ 0) (b left right : ℝ) :
    (∫ x in (a * left + b)..(a * right + b), squareSum (affineNodes nodes a b) x) =
      a * ∫ x in left..right, squareSum nodes x := by
  rw [← intervalIntegral.mul_integral_comp_mul_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact squareSum_affine nodes ha b x

end Erdos1131


end
end PrivateSource_Erdos1131


/- Source module NodeReindexing. -/
section PrivateSource_NodeReindexing

/-! Permuting nodes preserves the original objective. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem cardinalPolynomial_degree_lt {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) :
    (cardinalPolynomial nodes i).degree < n := by
  rw [cardinalPolynomial, Lagrange.degree_basis hinj.injOn (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot, WithBot.coe_lt_coe]
  have hi := i.isLt
  omega

theorem cardinalPolynomial_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    cardinalPolynomial (nodes ∘ e) i = cardinalPolynomial nodes (e i) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (hinj.comp e.injective).injOn
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      cardinalPolynomial_degree_lt (hinj.comp e.injective) i
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      cardinalPolynomial_degree_lt hinj (e i)
  · intro j hj
    change cardinal (nodes ∘ e) i ((nodes ∘ e) j) = cardinal nodes (e i) (nodes (e j))
    rw [cardinal_at_node (hinj.comp e.injective), cardinal_at_node hinj]
    simp only [e.injective.eq_iff]

theorem squareSum_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) (x : ℝ) :
    squareSum (nodes ∘ e) x = squareSum nodes x := by
  simp only [squareSum, cardinal, cardinalPolynomial_reindex hinj e]
  exact Equiv.sum_comp e (fun i => (cardinalPolynomial nodes i).eval x ^ 2)

theorem energy_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) :
    energy (nodes ∘ e) = energy nodes := by
  unfold energy
  simp_rw [squareSum_reindex hinj e]

theorem admissible_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (h : Admissible nodes) (e : Equiv.Perm (Fin n)) : Admissible (nodes ∘ e) :=
  ⟨h.1.comp e.injective, fun i => h.2 (e i)⟩

theorem exists_strictMono_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (nodes ∘ e) := by
  classical
  let s := Finset.univ.image nodes
  have hcard : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let f : Fin n → s := fun i => ⟨nodes i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hinj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hix⟩
  let original : Fin n ≃ s := Equiv.ofBijective f hf
  let sorted : Fin n ≃o s := s.orderIsoOfFin hcard
  let e : Equiv.Perm (Fin n) := sorted.toEquiv.trans original.symm
  have hvalues (i : Fin n) : nodes (e i) = (sorted i).val := by
    change nodes (original.symm (sorted i)) = (sorted i).val
    exact congrArg Subtype.val (original.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  change nodes (e i) < nodes (e j)
  rw [hvalues i, hvalues j]
  exact sorted.strictMono hij

end Erdos1131


end
end PrivateSource_NodeReindexing


/- Source module VandermondeMoment. -/
section PrivateSource_VandermondeMoment

/-! Vandermonde identities linking the numerator construction to the original integral. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem lagrange_reproduces_monomial {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (j : Fin n) (x : ℝ) :
    x ^ j.val = ∑ i, cardinal nodes i x * nodes i ^ j.val := by
  have hdegree : ((X : ℝ[X]) ^ j.val).degree <
      (Finset.univ : Finset (Fin n)).card := by
    simp only [degree_X_pow, Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
      WithBot.coe_lt_coe]
    exact j.isLt
  have h := Lagrange.eq_interpolate hinj.injOn hdegree
  have heval := congrArg (Polynomial.eval x) h
  simpa [Lagrange.interpolate_apply, cardinal, cardinalPolynomial,
    Polynomial.eval_finsetSum, mul_comm] using heval

def delta {n : ℕ} (nodes : Fin n → ℝ) : ℝ := (Matrix.vandermonde nodes).det

theorem delta_eq_product {n : ℕ} (nodes : Fin n → ℝ) :
    delta nodes = ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (nodes j - nodes i) := by
  have hsets : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    intro i
    ext j
    simp
  simpa only [delta, hsets] using Matrix.det_vandermonde nodes

theorem delta_ne_zero_iff {n : ℕ} (nodes : Fin n → ℝ) :
    delta nodes ≠ 0 ↔ Function.Injective nodes := Matrix.det_vandermonde_ne_zero_iff

theorem delta_update {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (x : ℝ) :
    delta (Function.update nodes i x) = cardinal nodes i x * delta nodes := by
  have hrow : (fun j : Fin n => x ^ j.val) =
      ∑ k, cardinal nodes k x • Matrix.vandermonde nodes k := by
    ext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vandermonde_apply]
      using lagrange_reproduces_monomial hinj j x
  have hmatrix : Matrix.vandermonde (Function.update nodes i x) =
      (Matrix.vandermonde nodes).updateRow i (fun j => x ^ j.val) := by
    ext a b
    by_cases hai : a = i
    · subst a
      rw [Matrix.updateRow_self]
      simp only [Matrix.vandermonde_apply, Function.update_self]
    · rw [Matrix.updateRow_ne hai]
      simp only [Matrix.vandermonde_apply, Function.update_of_ne hai]
  unfold delta
  rw [hmatrix, hrow, Matrix.det_updateRow_sum, smul_eq_mul]

def denominator {n : ℕ} (nodes : Fin n → ℝ) : ℝ := delta nodes ^ 2

def integralNumerator {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ x in (-1 : ℝ)..1, delta (Function.update nodes i x) ^ 2

theorem denominator_nonneg {n : ℕ} (nodes : Fin n → ℝ) :
    0 ≤ denominator nodes := sq_nonneg _

theorem denominator_pos_iff {n : ℕ} (nodes : Fin n → ℝ) :
    0 < denominator nodes ↔ Function.Injective nodes := by
  rw [denominator, sq_pos_iff, delta_ne_zero_iff]

theorem integralNumerator_nonneg {n : ℕ} (nodes : Fin n → ℝ) :
    0 ≤ integralNumerator nodes := by
  apply Finset.sum_nonneg
  intro i hi
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _)

theorem integralNumerator_eq_energy {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    integralNumerator nodes = denominator nodes * energy nodes := by
  unfold integralNumerator
  simp_rw [delta_update hinj, mul_pow]
  have hint : ∀ i : Fin n, IntervalIntegrable
      (fun x => cardinal nodes i x ^ 2) volume (-1 : ℝ) 1 := by
    intro i
    exact ((cardinalPolynomial nodes i).continuous.pow 2).intervalIntegrable _ _
  simp_rw [intervalIntegral.integral_mul_const]
  rw [← Finset.sum_mul]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  exact mul_comm _ _

end Erdos1131


end
end PrivateSource_VandermondeMoment


/- Source module Fekete. -/
section PrivateSource_Fekete

/-! The compact Vandermonde maximization used to obtain a strict upper bound. -/

open Polynomial
open scoped BigOperators Topology

noncomputable section

namespace Erdos1131

def nodeBox (n : ℕ) : Set (Fin n → ℝ) :=
  {nodes | ∀ i, nodes i ∈ Set.Icc (-1) 1}

theorem nodeBox_eq_Icc (n : ℕ) : nodeBox n = Set.Icc (-1) 1 := by
  ext nodes
  simp only [nodeBox, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def,
    Pi.neg_apply, Pi.one_apply]
  exact forall_and

theorem isCompact_nodeBox (n : ℕ) : IsCompact (nodeBox n) := by
  rw [nodeBox_eq_Icc]
  exact isCompact_Icc

theorem continuous_delta (n : ℕ) : Continuous (delta (n := n)) := by
  change Continuous (fun nodes : Fin n → ℝ => delta nodes)
  simp_rw [delta_eq_product]
  fun_prop

theorem continuous_denominator (n : ℕ) : Continuous (denominator (n := n)) :=
  (continuous_delta n).pow 2

def IsFekete {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Admissible nodes ∧ ∀ other ∈ nodeBox n, denominator other ≤ denominator nodes

theorem exists_fekete {n : ℕ} (hn : 0 < n) : ∃ nodes : Fin n → ℝ, IsFekete nodes := by
  have href : referenceNodes n ∈ nodeBox n := (referenceNodes_admissible hn).2
  obtain ⟨nodes, hnodes, hmax⟩ := (isCompact_nodeBox n).exists_isMaxOn
    ⟨referenceNodes n, href⟩ (continuous_denominator n).continuousOn
  have hpositive : 0 < denominator nodes :=
    lt_of_lt_of_le ((denominator_pos_iff _).2 (referenceNodes_admissible hn).1) (hmax href)
  exact ⟨nodes, ⟨(denominator_pos_iff _).1 hpositive, hnodes⟩, hmax⟩

theorem fekete_cardinal_sq_le_one {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    cardinal nodes i x ^ 2 ≤ 1 := by
  have hreplace : Function.update nodes i x ∈ nodeBox n := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hx
    · simpa only [Function.update_of_ne hji] using h.1.2 j
  have hmax := h.2 (Function.update nodes i x) hreplace
  have hpos := (denominator_pos_iff nodes).2 h.1.1
  simp only [denominator, delta_update h.1.1, mul_pow] at hmax hpos
  nlinarith

theorem one_lt_prod_real {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i ∈ s, f i := by
  simpa using Finset.prod_lt_prod_of_nonempty₀ (s := s) (f := fun _ => (1 : ℝ))
    (g := f) (fun _ _ => by norm_num) hf hs

theorem cardinal_left_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    {x : ℝ} (hx : x < nodes i) : 1 < cardinal nodes i x := by
  rw [cardinal_eq_product]
  apply one_lt_prod_real
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hlt : nodes i < nodes j := lt_of_le_of_ne (hmin j) (by
      intro heq
      exact hji (hinj heq).symm)
    apply (one_lt_div_of_neg (sub_neg.mpr hlt)).2
    linarith
  · apply Finset.card_pos.mp
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] using (show 0 < n - 1 by omega)

theorem cardinal_right_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    {x : ℝ} (hx : nodes i < x) : 1 < cardinal nodes i x := by
  rw [cardinal_eq_product]
  apply one_lt_prod_real
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hlt : nodes j < nodes i := lt_of_le_of_ne (hmax j) (by
      intro heq
      exact hji (hinj heq))
    apply (one_lt_div (sub_pos.mpr hlt)).2
    linarith
  · apply Finset.card_pos.mp
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] using (show 0 < n - 1 by omega)

theorem fekete_contains_endpoints {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) : (∃ i, nodes i = -1) ∧ (∃ i, nodes i = 1) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  constructor
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ nodes hnonempty
    refine ⟨i, le_antisymm ?_ (h.1.2 i).1⟩
    by_contra hle
    have houtside := cardinal_left_of_hull hn h.1.1 i
      (fun j => hmin j (Finset.mem_univ j)) (lt_of_not_ge hle)
    have hbound := fekete_cardinal_sq_le_one h i (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1)
    nlinarith
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ nodes hnonempty
    refine ⟨i, le_antisymm (h.1.2 i).2 ?_⟩
    by_contra hle
    have houtside := cardinal_right_of_hull hn h.1.1 i
      (fun j => hmax j (Finset.mem_univ j)) (lt_of_not_ge hle)
    have hbound := fekete_cardinal_sq_le_one h i (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1)
    nlinarith

theorem fekete_cardinal_derivative_zero {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) (hi : nodes i ∈ Set.Ioo (-1) 1) :
    (cardinalPolynomial nodes i).derivative.eval (nodes i) = 0 := by
  have hself : cardinal nodes i (nodes i) = 1 := by
    simpa using cardinal_at_node h.1.1 i i
  have hlocal : IsLocalMax (fun x => cardinal nodes i x ^ 2) (nodes i) := by
    filter_upwards [Icc_mem_nhds hi.1 hi.2] with x hx
    simpa only [hself, one_pow] using fekete_cardinal_sq_le_one h i hx
  have hlocal' : IsLocalMax
      (fun x => (cardinalPolynomial nodes i ^ 2).eval x) (nodes i) := by
    simpa only [Polynomial.eval_pow, cardinal] using hlocal
  have hzero := hlocal'.hasDerivAt_eq_zero
    ((cardinalPolynomial nodes i ^ 2).hasDerivAt (nodes i))
  have hself' : (cardinalPolynomial nodes i).eval (nodes i) = 1 := hself
  simpa [Polynomial.derivative_pow, hself'] using hzero

theorem squareSumPolynomial_derivative_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) :
    (squareSumPolynomial nodes).derivative.eval (nodes i) =
      2 * (cardinalPolynomial nodes i).derivative.eval (nodes i) := by
  classical
  simp only [squareSumPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  trans ∑ j, 2 * cardinal nodes j (nodes i) *
      (cardinalPolynomial nodes j).derivative.eval (nodes i)
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Polynomial.derivative_pow, cardinal]
  · simp [cardinal_at_node hinj]

theorem fekete_squareSum_derivative_zero {n : ℕ} {nodes : Fin n → ℝ}
    (h : IsFekete nodes) (i : Fin n) (hi : nodes i ∈ Set.Ioo (-1) 1) :
    (squareSumPolynomial nodes).derivative.eval (nodes i) = 0 := by
  rw [squareSumPolynomial_derivative_at_node h.1.1,
    fekete_cardinal_derivative_zero h i hi, mul_zero]

end Erdos1131


end
end PrivateSource_Fekete


/- Source module FeketeUpper. -/
section PrivateSource_FeketeUpper

/-! Polynomial factorization behind the Fekete upper bound. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem nodal_dvd_of_eval_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s : Finset (Fin n)) {p : ℝ[X]}
    (hroot : ∀ i ∈ s, p.eval (nodes i) = 0) : Lagrange.nodal s nodes ∣ p := by
  unfold Lagrange.nodal
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C hinj hij
  · intro i hi
    exact Polynomial.dvd_iff_isRoot.mpr (hroot i hi)

theorem nodal_derivative_eval_ne_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    (Lagrange.nodal s nodes).derivative.eval (nodes i) ≠ 0 := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq hi]
  simp only [Lagrange.nodal, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hinj hij).symm

theorem double_nodal_dvd_of_eval_zero {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (s t : Finset (Fin n)) (hts : t ⊆ s) {p : ℝ[X]}
    (hroot : ∀ i ∈ s, p.eval (nodes i) = 0)
    (hderiv : ∀ i ∈ t, p.derivative.eval (nodes i) = 0) :
    Lagrange.nodal s nodes * Lagrange.nodal t nodes ∣ p := by
  obtain ⟨q, hp⟩ := nodal_dvd_of_eval_zero hinj s hroot
  have hqroot : ∀ i ∈ t, q.eval (nodes i) = 0 := by
    intro i hi
    have hd := hderiv i hi
    simp only [hp, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Lagrange.eval_nodal_at_node (hts hi), zero_mul, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left (nodal_derivative_eval_ne_zero hinj s (hts hi))
  obtain ⟨r, hq⟩ := nodal_dvd_of_eval_zero hinj t hqroot
  refine ⟨r, ?_⟩
  rw [hp, hq, mul_assoc]

theorem squareSum_at_node {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) : squareSum nodes (nodes i) = 1 := by
  simp [squareSum, cardinal_at_node hinj]

theorem squareSumPolynomial_natDegree_le {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    (squareSumPolynomial nodes).natDegree ≤ 2 * (n - 1) := by
  unfold squareSumPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [Polynomial.natDegree_pow, cardinalPolynomial,
    Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem fekete_nodal_factorization {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {left right : Fin n} (hleft : nodes left = -1)
    (hright : nodes right = 1) :
    squareSumPolynomial nodes - 1 =
      Polynomial.C (squareSumPolynomial nodes - 1).leadingCoeff *
        (Lagrange.nodal Finset.univ nodes *
          Lagrange.nodal ((Finset.univ.erase left).erase right) nodes) := by
  have hlr : left ≠ right := by
    intro heq
    have : (-1 : ℝ) = 1 := hleft.symm.trans (heq ▸ hright)
    norm_num at this
  let inside := (Finset.univ.erase left).erase right
  have hright_mem : right ∈ (Finset.univ : Finset (Fin n)).erase left := by
    simp [hlr.symm]
  have hdvd : Lagrange.nodal Finset.univ nodes * Lagrange.nodal inside nodes ∣
      squareSumPolynomial nodes - 1 := by
    apply double_nodal_dvd_of_eval_zero h.1.1 _ _ (by intro i hi; simp)
    · intro i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_one, ← squareSum_eq_eval,
        squareSum_at_node h.1.1, sub_self]
    · intro i hi
      have hir : i ≠ right := (Finset.mem_erase.mp hi).1
      have hil : i ≠ left := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hvleft : nodes i ≠ -1 := by
        intro hv
        exact hil (h.1.1 (hv.trans hleft.symm))
      have hvright : nodes i ≠ 1 := by
        intro hv
        exact hir (h.1.1 (hv.trans hright.symm))
      have hinside : nodes i ∈ Set.Ioo (-1) 1 :=
        ⟨lt_of_le_of_ne (h.1.2 i).1 hvleft.symm, lt_of_le_of_ne (h.1.2 i).2 hvright⟩
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero]
      exact fekete_squareSum_derivative_zero h i hinside
  have hmonic := (Lagrange.nodal_monic (s := Finset.univ) (v := nodes)).mul
    (Lagrange.nodal_monic (s := inside) (v := nodes))
  apply Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmonic hdvd
  have hdeg : (Lagrange.nodal Finset.univ nodes * Lagrange.nodal inside nodes).natDegree =
      n + (n - 2) := by
    rw [Polynomial.natDegree_mul (Lagrange.nodal_monic.ne_zero) (Lagrange.nodal_monic.ne_zero),
      Lagrange.natDegree_nodal, Lagrange.natDegree_nodal]
    simp only [inside, Finset.card_erase_of_mem hright_mem,
      Finset.card_erase_of_mem (Finset.mem_univ left), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hdeg]
  have hs := squareSumPolynomial_natDegree_le h.1.1
  have hp := Polynomial.natDegree_sub_le (squareSumPolynomial nodes) (1 : ℝ[X])
  simp only [Polynomial.natDegree_one] at hp
  omega

theorem nodal_two_erase_factorization {n : ℕ} (nodes : Fin n → ℝ)
    (left right : Fin n) (hlr : left ≠ right) :
    Lagrange.nodal Finset.univ nodes =
      (Polynomial.X - Polynomial.C (nodes left)) *
      (Polynomial.X - Polynomial.C (nodes right)) *
      Lagrange.nodal ((Finset.univ.erase left).erase right) nodes := by
  have hleft := Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun i => Polynomial.X - Polynomial.C (nodes i)) (Finset.mem_univ left)
  have hright_mem : right ∈ (Finset.univ : Finset (Fin n)).erase left := by
    simp [hlr.symm]
  have hright := Finset.mul_prod_erase (Finset.univ.erase left)
    (fun i => Polynomial.X - Polynomial.C (nodes i)) hright_mem
  unfold Lagrange.nodal
  rw [← hleft, ← hright]
  ring

theorem fekete_squareSum_factorization {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {left right : Fin n} (hleft : nodes left = -1)
    (hright : nodes right = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ,
      squareSum nodes x - 1 = c * (x + 1) * (x - 1) *
        ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x) ^ 2 := by
  have hlr : left ≠ right := by
    intro heq
    have : (-1 : ℝ) = 1 := hleft.symm.trans (heq ▸ hright)
    norm_num at this
  let c := (squareSumPolynomial nodes - 1).leadingCoeff
  have hpoly := fekete_nodal_factorization hn h hleft hright
  rw [nodal_two_erase_factorization nodes left right hlr] at hpoly
  have hvalue (x : ℝ) : squareSum nodes x - 1 = c * (x + 1) * (x - 1) *
      ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x) ^ 2 := by
    have heval := congrArg (Polynomial.eval x) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, hleft, hright, ← squareSum_eq_eval] at heval
    dsimp [c]
    nlinarith [heval]
  refine ⟨c, ?_, hvalue⟩
  have hcard : 1 < cardinal nodes left (-2) := by
    apply cardinal_left_of_hull hn h.1.1 left
    · intro j
      rw [hleft]
      exact (h.1.2 j).1
    · rw [hleft]
      norm_num
  have hsum : cardinal nodes left (-2) ^ 2 ≤ squareSum nodes (-2) :=
    Finset.single_le_sum (fun i hi => sq_nonneg (cardinal nodes i (-2))) (Finset.mem_univ left)
  have hpositive : 0 < squareSum nodes (-2) - 1 := by nlinarith
  have hv := hvalue (-2)
  by_contra hc
  have hc0 : c ≤ 0 := le_of_not_gt hc
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hc0
    (sq_nonneg ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval (-2)))
  nlinarith

theorem fekete_squareSum_le_one {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : squareSum nodes x ≤ 1 := by
  obtain ⟨left, hleft⟩ := (fekete_contains_endpoints hn h).1
  obtain ⟨right, hright⟩ := (fekete_contains_endpoints hn h).2
  obtain ⟨c, hc, hvalue⟩ := fekete_squareSum_factorization hn h hleft hright
  have hleft_nonneg : 0 ≤ x + 1 := by linarith [hx.1]
  have hright_nonpos : x - 1 ≤ 0 := by linarith [hx.2]
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hleft_nonneg) hright_nonpos)
    (sq_nonneg ((Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x))
  have hv := hvalue x
  linarith

theorem fekete_squareSum_lt_one_off_nodes {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1)
    (hnotnode : ∀ i, x ≠ nodes i) : squareSum nodes x < 1 := by
  obtain ⟨left, hleft⟩ := (fekete_contains_endpoints hn h).1
  obtain ⟨right, hright⟩ := (fekete_contains_endpoints hn h).2
  obtain ⟨c, hc, hvalue⟩ := fekete_squareSum_factorization hn h hleft hright
  have hnodal : (Lagrange.nodal ((Finset.univ.erase left).erase right) nodes).eval x ≠ 0 := by
    exact Lagrange.eval_nodal_not_at_node (fun i hi => hnotnode i)
  have hleft_pos : 0 < x + 1 := by linarith [hx.1]
  have hright_neg : x - 1 < 0 := by linarith [hx.2]
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos hc hleft_pos) hright_neg)
    (sq_pos_of_ne_zero hnodal)
  have hv := hvalue x
  linarith

theorem fekete_energy_lt_two {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (h : IsFekete nodes) : energy nodes < 2 := by
  obtain ⟨x, hx, hnot⟩ := (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).exists_notMem_finset
    (Finset.univ.image nodes)
  have hnotnode : ∀ i, x ≠ nodes i := by
    intro i heq
    exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩)
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (-1 : ℝ) < 1) (continuous_squareSum nodes).continuousOn
    (continuous_const (y := (1 : ℝ))).continuousOn
    (fun y hy => fekete_squareSum_le_one hn h ⟨hy.1.le, hy.2⟩)
    ⟨x, ⟨hx.1.le, hx.2.le⟩, fekete_squareSum_lt_one_off_nodes hn h hx hnotnode⟩
  simpa only [energy, intervalIntegral.integral_const, sub_neg_eq_add, one_add_one_eq_two,
    smul_eq_mul, mul_one] using hstrict

theorem minimum_lt_two {n : ℕ} (hn : 2 ≤ n) : minimum n < 2 := by
  obtain ⟨nodes, hnodes⟩ := exists_fekete (by omega : 0 < n)
  exact lt_of_le_of_lt (minimum_le_energy hnodes.1) (fekete_energy_lt_two hn hnodes)

end Erdos1131


end
end PrivateSource_FeketeUpper


/- Source module EndpointReduction. -/
section PrivateSource_EndpointReduction

/-! Affine expansion of a node hull and the corresponding integral estimates. -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem squareSum_left_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    {x : ℝ} (hx : x ≤ nodes i) : 1 ≤ squareSum nodes x := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · have hcard := cardinal_left_of_hull hn hinj i hmin hlt
    have hsum : cardinal nodes i x ^ 2 ≤ squareSum nodes x :=
      Finset.single_le_sum (fun j hj => sq_nonneg (cardinal nodes j x)) (Finset.mem_univ i)
    nlinarith
  · rw [squareSum]
    simp [cardinal_at_node hinj]

theorem squareSum_right_of_hull {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    {x : ℝ} (hx : nodes i ≤ x) : 1 ≤ squareSum nodes x := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · have hcard := cardinal_right_of_hull hn hinj i hmax hlt
    have hsum : cardinal nodes i x ^ 2 ≤ squareSum nodes x :=
      Finset.single_le_sum (fun j hj => sq_nonneg (cardinal nodes j x)) (Finset.mem_univ i)
    nlinarith
  · rw [← heq, squareSum]
    simp [cardinal_at_node hinj]

theorem outside_left_integral_lower {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmin : ∀ j, nodes i ≤ nodes j)
    (ha : -1 ≤ nodes i) :
    nodes i + 1 ≤ ∫ x in (-1 : ℝ)..nodes i, squareSum nodes x := by
  have hbound := intervalIntegral.integral_mono_on ha
    (continuous_const.intervalIntegrable (-1) (nodes i))
    (intervalIntegrable_squareSum nodes (-1) (nodes i))
    (fun x hx => squareSum_left_of_hull hn hinj i hmin hx.2)
  simpa only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul, mul_one]
    using hbound

theorem outside_right_integral_lower {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) (hmax : ∀ j, nodes j ≤ nodes i)
    (hb : nodes i ≤ 1) :
    1 - nodes i ≤ ∫ x in nodes i..(1 : ℝ), squareSum nodes x := by
  have hbound := intervalIntegral.integral_mono_on hb
    (continuous_const.intervalIntegrable (nodes i) 1)
    (intervalIntegrable_squareSum nodes (nodes i) 1)
    (fun x hx => squareSum_right_of_hull hn hinj i hmax hx.1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hbound

theorem hull_energy_decomposition {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) :
    (∫ x in (-1 : ℝ)..a, squareSum nodes x) +
      (∫ x in a..b, squareSum nodes x) +
      (∫ x in b..(1 : ℝ), squareSum nodes x) = energy nodes := by
  rw [intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_squareSum nodes (-1) a) (intervalIntegrable_squareSum nodes a b)]
  rw [intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_squareSum nodes (-1) b) (intervalIntegrable_squareSum nodes b 1)]
  rfl

def expandedNodes {n : ℕ} (nodes : Fin n → ℝ) (a b : ℝ) : Fin n → ℝ :=
  affineNodes nodes (2 / (b - a)) (-1 - (2 / (b - a)) * a)

theorem expandedNodes_energy {n : ℕ} (nodes : Fin n → ℝ) {a b : ℝ} (hab : a < b) :
    energy (expandedNodes nodes a b) =
      (2 / (b - a)) * ∫ x in a..b, squareSum nodes x := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hscale : 2 / (b - a) ≠ 0 := div_ne_zero (by norm_num) hne
  have hleft : (2 / (b - a)) * a + (-1 - (2 / (b - a)) * a) = -1 := by ring
  have hright : (2 / (b - a)) * b + (-1 - (2 / (b - a)) * a) = 1 := by
    field_simp
    ring
  have h := integral_squareSum_affine nodes hscale (-1 - (2 / (b - a)) * a) a b
  rw [hleft, hright] at h
  exact h

theorem expandedNodes_admissible {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) {a b : ℝ} (hab : a < b)
    (hbox : ∀ i, a ≤ nodes i ∧ nodes i ≤ b) : Admissible (expandedNodes nodes a b) := by
  have hscale : 0 < 2 / (b - a) := div_pos (by norm_num) (sub_pos.mpr hab)
  constructor
  · intro i j hij
    apply hinj
    dsimp [expandedNodes, affineNodes] at hij
    exact mul_left_cancel₀ hscale.ne' (add_right_cancel hij)
  · intro i
    have hlower := mul_le_mul_of_nonneg_left (hbox i).1 hscale.le
    have hupper := mul_le_mul_of_nonneg_left (hbox i).2 hscale.le
    have hlength : (2 / (b - a)) * (b - a) = 2 :=
      div_mul_cancel₀ 2 (ne_of_gt (sub_pos.mpr hab))
    dsimp [expandedNodes, affineNodes]
    constructor <;> nlinarith

theorem expandedNodes_improves_energy {n : ℕ} (hn : 2 ≤ n) {nodes : Fin n → ℝ}
    (hadm : Admissible nodes) (left right : Fin n)
    (hmin : ∀ i, nodes left ≤ nodes i) (hmax : ∀ i, nodes i ≤ nodes right)
    (hspan : nodes left < nodes right) (hshort : nodes right - nodes left < 2)
    (henergy : energy nodes < 2) :
    energy (expandedNodes nodes (nodes left) (nodes right)) < energy nodes := by
  have hL : 0 < nodes right - nodes left := sub_pos.mpr hspan
  have hleft := outside_left_integral_lower hn hadm.1 left hmin (hadm.2 left).1
  have hright := outside_right_integral_lower hn hadm.1 right hmax (hadm.2 right).2
  have hsplit := hull_energy_decomposition nodes (nodes left) (nodes right)
  have hinside : (∫ x in nodes left..nodes right, squareSum nodes x) < nodes right - nodes left := by
    linarith
  have hproduct := mul_pos (sub_pos.mpr hshort) (sub_pos.mpr hinside)
  have houtside := mul_nonneg hL.le (show 0 ≤
    (∫ x in (-1 : ℝ)..nodes left, squareSum nodes x) +
    (∫ x in nodes right..(1 : ℝ), squareSum nodes x) -
    (2 - (nodes right - nodes left)) by linarith)
  rw [expandedNodes_energy nodes hspan, div_mul_eq_mul_div]
  apply (div_lt_iff₀ hL).2
  nlinarith

end Erdos1131


end
end PrivateSource_EndpointReduction


/- Source module PolynomialEncoding. -/
section PrivateSource_PolynomialEncoding

/-! Rational coefficient rules for the cleared interpolation integral. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def coefficientMoment {A : Type*} [CommRing A] [Algebra ℚ A] (p : A[X]) : A :=
  p.sum fun k a => a * algebraMap ℚ A (moment k)

theorem coefficientMoment_add {A : Type*} [CommRing A] [Algebra ℚ A] (p q : A[X]) :
    coefficientMoment (p + q) = coefficientMoment p + coefficientMoment q :=
  Polynomial.sum_add_index p q (fun k a => a * algebraMap ℚ A (moment k))
    (fun _ => by simp) (fun _ _ _ => add_mul _ _ _)

theorem coefficientMoment_monomial {A : Type*} [CommRing A] [Algebra ℚ A]
    (k : ℕ) (a : A) :
    coefficientMoment (Polynomial.monomial k a) = a * algebraMap ℚ A (moment k) :=
  Polynomial.sum_monomial_index a (fun k a => a * algebraMap ℚ A (moment k)) (by simp)

theorem coefficientMoment_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (p : A[X]) :
    coefficientMoment (p.map φ.toRingHom) = φ (coefficientMoment p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, coefficientMoment_add, coefficientMoment_add,
      map_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.map_monomial, coefficientMoment_monomial, map_mul, φ.commutes]
    rfl

theorem coefficientMoment_real (p : ℝ[X]) :
    coefficientMoment p = ∫ x in (-1 : ℝ)..1, p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [coefficientMoment_add, hp, hq]
    simp only [Polynomial.eval_add]
    exact (intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
      (q.continuous.intervalIntegrable _ _)).symm
  | monomial k a =>
    rw [coefficientMoment_monomial]
    simp only [Polynomial.eval_monomial]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [moment]

def algebraicDelta {A : Type*} [CommRing A] {n : ℕ} (nodes : Fin n → A) : A :=
  (Matrix.vandermonde nodes).det

theorem algebraicDelta_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A) :
    φ (algebraicDelta nodes) = algebraicDelta (fun i => φ (nodes i)) := by
  unfold algebraicDelta
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

def encodingDenominator {A : Type*} [CommRing A] {n : ℕ} (nodes : Fin n → A) : A :=
  algebraicDelta nodes ^ 2

def encodingNumerator {A : Type*} [CommRing A] [Algebra ℚ A]
    {n : ℕ} (nodes : Fin n → A) (scale : A) : A :=
  ∑ i, coefficientMoment (algebraicDelta
    (Function.update (fun j => Polynomial.C (nodes j)) i (Polynomial.C scale * Polynomial.X)) ^ 2)

theorem encodingDenominator_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A) :
    φ (encodingDenominator nodes) = encodingDenominator (fun i => φ (nodes i)) := by
  simp only [encodingDenominator, map_pow, algebraicDelta_map]

theorem polynomial_algebraicDelta_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (nodes : Fin n → A[X]) :
    (algebraicDelta nodes).map φ = algebraicDelta (fun i => (nodes i).map φ) :=
  algebraicDelta_map (Polynomial.mapRingHom φ) nodes

theorem encodingNumerator_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (φ : A →ₐ[ℚ] B)
    {n : ℕ} (nodes : Fin n → A) (scale : A) :
    φ (encodingNumerator nodes scale) =
      encodingNumerator (fun i => φ (nodes i)) (φ scale) := by
  unfold encodingNumerator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← coefficientMoment_map φ, Polynomial.map_pow, polynomial_algebraicDelta_map]
  apply congrArg coefficientMoment
  apply congrArg (fun p : B[X] => p ^ 2)
  apply congrArg algebraicDelta
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

theorem polynomial_delta_eval {n : ℕ} (nodes : Fin n → ℝ)
    (i : Fin n) (scale x : ℝ) :
    (algebraicDelta (Function.update (fun j => Polynomial.C (nodes j)) i
      (Polynomial.C scale * Polynomial.X))).eval x =
      delta (Function.update nodes i (scale * x)) := by
  have h := algebraicDelta_map (Polynomial.evalRingHom x)
    (Function.update (fun j => Polynomial.C (nodes j)) i (Polynomial.C scale * Polynomial.X))
  change _ = algebraicDelta _
  refine h.trans ?_
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

theorem encodingNumerator_real {n : ℕ} (nodes : Fin n → ℝ) (scale : ℝ) :
    encodingNumerator nodes scale =
      ∑ i, ∫ x in (-1 : ℝ)..1, delta (Function.update nodes i (scale * x)) ^ 2 := by
  unfold encodingNumerator
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficientMoment_real]
  simp only [Polynomial.eval_pow, polynomial_delta_eval]

theorem encodingNumerator_nonneg {n : ℕ} (nodes : Fin n → ℝ) (scale : ℝ) :
    0 ≤ encodingNumerator nodes scale := by
  rw [encodingNumerator_real]
  exact Finset.sum_nonneg (fun i hi =>
    intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _))

theorem encodingNumerator_affine {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) {scale : ℝ} (hscale : scale ≠ 0) :
    encodingNumerator (affineNodes nodes scale 0) scale =
      encodingDenominator (affineNodes nodes scale 0) * energy nodes := by
  have haffine : Function.Injective (affineNodes nodes scale 0) := by
    intro i j hij
    apply hinj
    exact mul_left_cancel₀ hscale (by simpa only [affineNodes, add_zero] using hij)
  have hcard (i : Fin n) (x : ℝ) :
      cardinal (affineNodes nodes scale 0) i (scale * x) = cardinal nodes i x := by
    simpa only [add_zero] using cardinal_affine nodes hscale 0 x i
  rw [encodingNumerator_real]
  simp_rw [delta_update haffine, hcard, mul_pow, intervalIntegral.integral_mul_const]
  rw [← Finset.sum_mul]
  have hint : ∀ i : Fin n, IntervalIntegrable
      (fun x => cardinal nodes i x ^ 2) volume (-1 : ℝ) 1 := by
    intro i
    exact ((cardinalPolynomial nodes i).continuous.pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  exact mul_comm _ _

end Erdos1131


end
end PrivateSource_PolynomialEncoding


/- Source module GapEncoding. -/
section PrivateSource_GapEncoding

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


end
end PrivateSource_GapEncoding


/- Source module GapParametrization. -/
section PrivateSource_GapParametrization

/-! Surjectivity of the squared-gap parametrization and its exact sign condition. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def sqrtGaps {k : ℕ} (nodes : Fin (k + 1) → ℝ) (i : Fin k) : ℝ :=
  Real.sqrt ((nodes i.succ - nodes i.castSucc) / 2)

theorem sqrtGaps_pos {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin k) : 0 < sqrtGaps nodes i := by
  apply Real.sqrt_pos.mpr
  apply div_pos _ (by norm_num)
  exact sub_pos.mpr (hmono (by exact_mod_cast Nat.lt_succ_self i.val))

theorem sqrtGaps_sq {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin k) :
    sqrtGaps nodes i ^ 2 = (nodes i.succ - nodes i.castSucc) / 2 := by
  apply Real.sq_sqrt
  apply div_nonneg _ (by norm_num)
  exact sub_nonneg.mpr (hmono.monotone (by exact_mod_cast Nat.le_succ i.val))

theorem gapTotal_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    gapTotal (sqrtGaps nodes) = 1 := by
  unfold gapTotal
  simp_rw [sqrtGaps_sq hmono]
  rw [← Finset.sum_div, sum_gap_differences, hleft, hright]
  norm_num

theorem gapPrefix_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (i : Fin (k + 1)) :
    gapPrefix (fun j => sqrtGaps nodes j ^ 2) i = (nodes i - nodes 0) / 2 := by
  unfold gapPrefix
  simp_rw [sqrtGaps_sq hmono]
  rw [← Finset.sum_div]
  change gapPrefix (fun j => nodes j.succ - nodes j.castSucc) i / 2 = _
  rw [gapPrefix_differences]

theorem gapNodes_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    gapNodes (sqrtGaps nodes) = nodes := by
  funext i
  unfold gapNodes
  rw [gapTotal_sqrtGaps hmono hleft hright, gapPrefix_sqrtGaps hmono, hleft]
  ring

theorem normalizedGapNodes_sqrtGaps {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (hmono : StrictMono nodes) (hleft : nodes 0 = -1) (hright : nodes (Fin.last k) = 1) :
    normalizedGapNodes (sqrtGaps nodes) = nodes := by
  funext i
  unfold normalizedGapNodes
  rw [gapTotal_sqrtGaps hmono hleft hright, gapNodes_sqrtGaps hmono hleft hright, div_one]

theorem normalizedGapNodes_strictMono {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : StrictMono (normalizedGapNodes u) := by
  intro i j hij
  exact div_lt_div_of_pos_right (gapNodes_strictMono hu hij) (gapTotal_pos hk hu)

def OrderedEndpoints {k : ℕ} (nodes : Fin (k + 1) → ℝ) : Prop :=
  StrictMono nodes ∧ nodes 0 = -1 ∧ nodes (Fin.last k) = 1

theorem normalizedGapNodes_orderedEndpoints {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ≠ 0) : OrderedEndpoints (normalizedGapNodes u) :=
  ⟨normalizedGapNodes_strictMono hk hu, normalizedGapNodes_endpoints hk hu⟩

theorem squared_gap_parametrization_surjective {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) :
    ∃ u : Fin k → ℝ, (∀ i, u i ≠ 0) ∧ normalizedGapNodes u = nodes := by
  exact ⟨sqrtGaps nodes, fun i => ne_of_gt (sqrtGaps_pos h.1 i),
    normalizedGapNodes_sqrtGaps h.1 h.2.1 h.2.2⟩

def thresholdExpression (k : ℕ) (t : ℝ) (u : Fin k → ℝ) : ℝ :=
  MvPolynomial.aeval u (numeratorPolynomial k) -
    t * MvPolynomial.aeval u (denominatorPolynomial k)

theorem denominatorPolynomial_eval_nonneg {k : ℕ} (u : Fin k → ℝ) :
    0 ≤ MvPolynomial.aeval u (denominatorPolynomial k) := by
  rw [denominatorPolynomial_eval]
  exact sq_nonneg _

theorem thresholdExpression_nonneg_iff {k : ℕ} (hk : 0 < k) (t : ℝ)
    {u : Fin k → ℝ} (hu : ∀ i, u i ≠ 0) :
    0 ≤ thresholdExpression k t u ↔ t ≤ energy (normalizedGapNodes u) := by
  have hD := (denominatorPolynomial_eval_pos_iff u).2 hu
  have hratio := numerator_div_denominator_eq_energy hk hu
  apply Iff.trans (sub_nonneg : _)
  constructor
  · intro h
    rw [← hratio]
    exact (le_div_iff₀ hD).2 h
  · intro h
    rw [← hratio] at h
    exact (le_div_iff₀ hD).1 h

theorem thresholdExpression_collision_nonneg {k : ℕ} (t : ℝ) (u : Fin k → ℝ)
    (hcollision : ¬ ∀ i, u i ≠ 0) : 0 ≤ thresholdExpression k t u := by
  have hnotpos : ¬ 0 < MvPolynomial.aeval u (denominatorPolynomial k) := by
    simpa only [denominatorPolynomial_eval_pos_iff] using hcollision
  have hzero : MvPolynomial.aeval u (denominatorPolynomial k) = 0 :=
    le_antisymm (le_of_not_gt hnotpos) (denominatorPolynomial_eval_nonneg u)
  simpa only [thresholdExpression, hzero, mul_zero, sub_zero]
    using numeratorPolynomial_eval_nonneg u

theorem thresholdExpression_globally_nonnegative_iff {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ u : Fin k → ℝ, 0 ≤ thresholdExpression k t u) ↔
      ∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes := by
  constructor
  · intro h nodes hnodes
    obtain ⟨u, hu, hparam⟩ := squared_gap_parametrization_surjective hnodes
    have hbound := (thresholdExpression_nonneg_iff hk t hu).1 (h u)
    simpa only [hparam] using hbound
  · intro h u
    by_cases hu : ∀ i, u i ≠ 0
    · exact (thresholdExpression_nonneg_iff hk t hu).2
        (h _ (normalizedGapNodes_orderedEndpoints hk hu))
    · exact thresholdExpression_collision_nonneg t u hu

end Erdos1131


end
end PrivateSource_GapParametrization


/- Source module HomogeneousLift. -/
section PrivateSource_HomogeneousLift

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


end
end PrivateSource_HomogeneousLift


/- Source module EncodingHomogeneity. -/
section PrivateSource_EncodingHomogeneity

/-! Homogeneity and the critical-point reduction for the explicit rational polynomials. -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem twice_sum_fin_val (n : ℕ) :
    2 * (∑ i : Fin n, i.val) = n * (n - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
  have h := Finset.sum_range_id_mul_two n
  simpa only [mul_comm] using h

theorem algebraicDelta_mul {A : Type*} [CommRing A] {n : ℕ}
    (s : A) (nodes : Fin n → A) :
    algebraicDelta (fun i => s * nodes i) =
      s ^ (∑ i : Fin n, i.val) * algebraicDelta nodes := by
  have hmatrix : Matrix.vandermonde (fun i => s * nodes i) =
      Matrix.of (fun i j => s ^ j.val * Matrix.vandermonde nodes i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, mul_pow, Matrix.of_apply]
  unfold algebraicDelta
  rw [hmatrix, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]

theorem gapTotal_mul {A : Type*} [CommRing A] {k : ℕ} (s : A) (u : Fin k → A) :
    gapTotal (fun i => s * u i) = s ^ 2 * gapTotal u := by
  simp only [gapTotal, mul_pow, Finset.mul_sum]

theorem gapNodes_mul {A : Type*} [CommRing A] {k : ℕ}
    (s : A) (u : Fin k → A) (i : Fin (k + 1)) :
    gapNodes (fun j => s * u j) i = s ^ 2 * gapNodes u i := by
  have hprefix : gapPrefix (fun j => (s * u j) ^ 2) i =
      s ^ 2 * gapPrefix (fun j => u j ^ 2) i := by
    simp only [gapPrefix, mul_pow, Finset.mul_sum]
  change -gapTotal (fun j => s * u j) + 2 * gapPrefix (fun j => (s * u j) ^ 2) i =
    s ^ 2 * (-gapTotal u + 2 * gapPrefix (fun j => u j ^ 2) i)
  rw [gapTotal_mul, hprefix]
  ring

theorem scaled_updated_gapNodes {A : Type*} [CommRing A] {k : ℕ}
    (s : A) (u : Fin k → A) (i : Fin (k + 1)) (x : A) :
    Function.update (gapNodes (fun j => s * u j)) i (gapTotal (fun j => s * u j) * x) =
      fun j => s ^ 2 * Function.update (gapNodes u) i (gapTotal u * x) j := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, gapTotal_mul]
    ring
  · simp only [Function.update_of_ne hji, gapNodes_mul]

theorem gap_degree_identity (k : ℕ) :
    2 * ((∑ i : Fin (k + 1), i.val) * 2) = 2 * ((k + 1) * k) := by
  rw [← mul_assoc, twice_sum_fin_val]
  simp only [Nat.add_sub_cancel]
  omega

theorem updated_delta_homogeneous {k : ℕ} (s : ℝ) (u : Fin k → ℝ)
    (i : Fin (k + 1)) (x : ℝ) :
    delta (Function.update (gapNodes (s • u)) i (gapTotal (s • u) * x)) ^ 2 =
      s ^ (2 * ((k + 1) * k)) *
        delta (Function.update (gapNodes u) i (gapTotal u * x)) ^ 2 := by
  change delta (Function.update (gapNodes (fun j => s * u j)) i
    (gapTotal (fun j => s * u j) * x)) ^ 2 = _
  rw [scaled_updated_gapNodes]
  change algebraicDelta (fun j => s ^ 2 *
    Function.update (gapNodes u) i (gapTotal u * x) j) ^ 2 = _
  rw [algebraicDelta_mul, mul_pow, ← pow_mul, ← pow_mul, gap_degree_identity]
  rfl

theorem numerator_homogeneous (k : ℕ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k))
      (fun u : Fin k → ℝ => MvPolynomial.aeval u (numeratorPolynomial k)) := by
  intro s u
  dsimp only
  rw [numeratorPolynomial_eval, numeratorPolynomial_eval,
    encodingNumerator_real, encodingNumerator_real]
  simp_rw [updated_delta_homogeneous, intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]

theorem denominator_homogeneous (k : ℕ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k))
      (fun u : Fin k → ℝ => MvPolynomial.aeval u (denominatorPolynomial k)) := by
  intro s u
  dsimp only
  rw [denominatorPolynomial_eval, denominatorPolynomial_eval]
  change algebraicDelta (gapNodes (fun j => s * u j)) ^ 2 =
    s ^ (2 * ((k + 1) * k)) * algebraicDelta (gapNodes u) ^ 2
  have hnodes : gapNodes (fun j => s * u j) = fun j => s ^ 2 * gapNodes u j :=
    funext (gapNodes_mul s u)
  rw [hnodes, algebraicDelta_mul, mul_pow, ← pow_mul, ← pow_mul, gap_degree_identity]

theorem threshold_homogeneous (k : ℕ) (t : ℝ) :
    HomogeneousLift.IsHomogeneous (2 * ((k + 1) * k)) (thresholdExpression k t) := by
  intro s u
  dsimp [thresholdExpression]
  have hn := numerator_homogeneous k s u
  have hd := denominator_homogeneous k s u
  dsimp only at hn hd
  rw [hn, hd]
  ring

theorem differentiable_aeval (k : ℕ) (p : MvPolynomial (Fin k) ℚ) :
    Differentiable ℝ (fun u : Fin k → ℝ => MvPolynomial.aeval u p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    fun_prop
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (by fun_prop)

theorem threshold_differentiable (k : ℕ) (t : ℝ) :
    Differentiable ℝ (thresholdExpression k t) := by
  exact (differentiable_aeval k (numeratorPolynomial k)).sub
    ((differentiable_aeval k (denominatorPolynomial k)).const_mul t)

theorem critical_points_singleton_iff_endpoint_bound {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0} = {0} ↔
      ∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes := by
  rw [HomogeneousLift.critical_points_singleton_iff_nonnegative
    (Nat.mul_pos (Nat.succ_pos k) hk) (threshold_homogeneous k t)
    (threshold_differentiable k t)]
  exact thresholdExpression_globally_nonnegative_iff hk t

end Erdos1131


end
end PrivateSource_EncodingHomogeneity


/- Source module OriginalThreshold. -/
section PrivateSource_OriginalThreshold

/-! Identification of the polynomial nonnegativity threshold with the original infimum. -/

noncomputable section

namespace Erdos1131

theorem orderedEndpoints_admissible {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) : Admissible nodes := by
  refine ⟨h.1.injective, fun i => ?_⟩
  constructor
  · have hi := h.1.monotone (Fin.zero_le i)
    simpa only [h.2.1] using hi
  · have hi := h.1.monotone (Fin.le_last i)
    simpa only [h.2.2] using hi

theorem expandedNodes_orderedEndpoints {k : ℕ} (hk : 0 < k)
    {nodes : Fin (k + 1) → ℝ} (hmono : StrictMono nodes) :
    OrderedEndpoints (expandedNodes nodes (nodes 0) (nodes (Fin.last k))) := by
  have hspan : nodes 0 < nodes (Fin.last k) := hmono (by exact_mod_cast hk)
  have hden : nodes (Fin.last k) - nodes 0 ≠ 0 := ne_of_gt (sub_pos.mpr hspan)
  have hscale : 0 < 2 / (nodes (Fin.last k) - nodes 0) :=
    div_pos (by norm_num) (sub_pos.mpr hspan)
  constructor
  · intro i j hij
    dsimp [expandedNodes, affineNodes]
    have hmul := mul_lt_mul_of_pos_left (hmono hij) hscale
    linarith
  constructor
  · dsimp [expandedNodes, affineNodes]
    ring
  · dsimp [expandedNodes, affineNodes]
    field_simp
    ring

theorem exists_orderedEndpoints_le_energy {k : ℕ} (hk : 0 < k)
    {nodes : Fin (k + 1) → ℝ} (hadm : Admissible nodes) (henergy : energy nodes < 2) :
    ∃ other : Fin (k + 1) → ℝ, OrderedEndpoints other ∧ energy other ≤ energy nodes := by
  obtain ⟨e, hmono⟩ := exists_strictMono_reindex hadm.1
  let ordered := nodes ∘ e
  have hordered : Admissible ordered := admissible_reindex hadm e
  have heq : energy ordered = energy nodes := energy_reindex hadm.1 e
  have hspan : ordered 0 < ordered (Fin.last k) := hmono (by exact_mod_cast hk)
  by_cases hshort : ordered (Fin.last k) - ordered 0 < 2
  · refine ⟨expandedNodes ordered (ordered 0) (ordered (Fin.last k)),
      expandedNodes_orderedEndpoints hk hmono, ?_⟩
    have hbetter := expandedNodes_improves_energy (by omega : 2 ≤ k + 1) hordered
      0 (Fin.last k) (fun i => hmono.monotone (Fin.zero_le i))
      (fun i => hmono.monotone (Fin.le_last i)) hspan hshort (heq ▸ henergy)
    exact hbetter.le.trans heq.le
  · have hleft : ordered 0 = -1 := by
      obtain ⟨h0lo, h0hi⟩ := hordered.2 0
      obtain ⟨h1lo, h1hi⟩ := hordered.2 (Fin.last k)
      linarith
    have hright : ordered (Fin.last k) = 1 := by
      obtain ⟨h0lo, h0hi⟩ := hordered.2 0
      obtain ⟨h1lo, h1hi⟩ := hordered.2 (Fin.last k)
      linarith
    exact ⟨ordered, ⟨hmono, hleft, hright⟩, heq.le⟩

def endpointValues (k : ℕ) : Set ℝ :=
  {v | ∃ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes ∧ energy nodes = v}

def endpointMinimum (k : ℕ) : ℝ := sInf (endpointValues k)

theorem exists_orderedEndpoints_energy_lt_two {k : ℕ} (hk : 0 < k) :
    ∃ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes ∧ energy nodes < 2 := by
  obtain ⟨nodes, hnodes⟩ := exists_fekete (Nat.succ_pos k)
  have henergy := fekete_energy_lt_two (by omega : 2 ≤ k + 1) hnodes
  obtain ⟨other, hother, hle⟩ := exists_orderedEndpoints_le_energy hk hnodes.1 henergy
  exact ⟨other, hother, lt_of_le_of_lt hle henergy⟩

theorem endpointValues_nonempty {k : ℕ} (hk : 0 < k) : (endpointValues k).Nonempty := by
  obtain ⟨nodes, hnodes, henergy⟩ := exists_orderedEndpoints_energy_lt_two hk
  exact ⟨energy nodes, nodes, hnodes, rfl⟩

theorem endpointValues_bddBelow (k : ℕ) : BddBelow (endpointValues k) := by
  refine ⟨0, ?_⟩
  rintro v ⟨nodes, hnodes, rfl⟩
  exact energy_nonneg nodes

theorem endpointMinimum_le_energy {k : ℕ} {nodes : Fin (k + 1) → ℝ}
    (h : OrderedEndpoints nodes) : endpointMinimum k ≤ energy nodes :=
  csInf_le (endpointValues_bddBelow k) ⟨nodes, h, rfl⟩

theorem endpointMinimum_lt_two {k : ℕ} (hk : 0 < k) : endpointMinimum k < 2 := by
  obtain ⟨nodes, hnodes, henergy⟩ := exists_orderedEndpoints_energy_lt_two hk
  exact lt_of_le_of_lt (endpointMinimum_le_energy hnodes) henergy

theorem endpointMinimum_eq_minimum {k : ℕ} (hk : 0 < k) :
    endpointMinimum k = minimum (k + 1) := by
  apply le_antisymm
  · apply le_csInf (attainableValues_nonempty (Nat.succ_pos k))
    rintro value ⟨nodes, hnodes, rfl⟩
    by_cases hsmall : energy nodes < 2
    · obtain ⟨other, hother, hle⟩ := exists_orderedEndpoints_le_energy hk hnodes hsmall
      exact (endpointMinimum_le_energy hother).trans hle
    · exact (endpointMinimum_lt_two hk).le.trans (le_of_not_gt hsmall)
  · apply le_csInf (endpointValues_nonempty hk)
    rintro value ⟨nodes, hnodes, rfl⟩
    exact minimum_le_energy (orderedEndpoints_admissible hnodes)

theorem bound_all_orderedEndpoints_iff {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ nodes : Fin (k + 1) → ℝ, OrderedEndpoints nodes → t ≤ energy nodes) ↔
      t ≤ endpointMinimum k := by
  constructor
  · intro h
    apply le_csInf (endpointValues_nonempty hk)
    rintro value ⟨nodes, hnodes, rfl⟩
    exact h nodes hnodes
  · intro h nodes hnodes
    exact h.trans (endpointMinimum_le_energy hnodes)

theorem original_polynomial_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∀ u : Fin k → ℝ, 0 ≤ thresholdExpression k t u) ↔ t ≤ minimum (k + 1) := by
  rw [thresholdExpression_globally_nonnegative_iff hk t,
    bound_all_orderedEndpoints_iff hk t, endpointMinimum_eq_minimum hk]

theorem original_critical_point_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0} = {0} ↔
      t ≤ minimum (k + 1) := by
  rw [critical_points_singleton_iff_endpoint_bound hk t, bound_all_orderedEndpoints_iff hk t,
    endpointMinimum_eq_minimum hk]

end Erdos1131


end
end PrivateSource_OriginalThreshold


/- Source module ParametricSystem. -/
section PrivateSource_ParametricSystem

/-! Rational parameter coefficients and the normalized-gradient quotient. -/

open Polynomial

noncomputable section

namespace Erdos1131

abbrev ParameterRing := Polynomial ℚ

def clearedDegree (k : ℕ) : ℕ := 2 * ((k + 1) * k)

def liftRationalCoefficients {k : ℕ} :
    MvPolynomial (Fin k) ℚ →+* MvPolynomial (Fin k) ParameterRing :=
  MvPolynomial.map Polynomial.C

def parametricThreshold (k : ℕ) : MvPolynomial (Fin k) ParameterRing :=
  liftRationalCoefficients (numeratorPolynomial k) -
    MvPolynomial.C Polynomial.X * liftRationalCoefficients (denominatorPolynomial k)

def specializeParameter (t : ℝ) : ParameterRing →+* ℝ :=
  Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t

def evaluateParametricSystem {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    MvPolynomial (Fin k) ParameterRing →+* ℝ :=
  MvPolynomial.eval₂Hom (specializeParameter t) u

theorem evaluate_liftRationalCoefficients {k : ℕ} (t : ℝ) (u : Fin k → ℝ)
    (p : MvPolynomial (Fin k) ℚ) :
    evaluateParametricSystem t u (liftRationalCoefficients p) = MvPolynomial.aeval u p := by
  have hhom : (evaluateParametricSystem t u).comp liftRationalCoefficients =
      (MvPolynomial.aeval u).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evaluateParametricSystem, specializeParameter, liftRationalCoefficients]
    · intro i
      simp [evaluateParametricSystem, specializeParameter, liftRationalCoefficients]
  exact RingHom.congr_fun hhom p

theorem evaluate_parametricThreshold {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    evaluateParametricSystem t u (parametricThreshold k) = thresholdExpression k t u := by
  unfold parametricThreshold
  rw [map_sub, map_mul, evaluate_liftRationalCoefficients, evaluate_liftRationalCoefficients]
  simp [evaluateParametricSystem, specializeParameter, thresholdExpression]

def normalizedGradient (k : ℕ) (i : Fin k) : MvPolynomial (Fin k) ParameterRing :=
  MvPolynomial.X i ^ (clearedDegree k + 1) +
    MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)

def gradientIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) ParameterRing) :=
  Ideal.span (Set.range (normalizedGradient k))

abbrev GradientQuotient (k : ℕ) :=
  (MvPolynomial (Fin k) ParameterRing) ⧸ gradientIdeal k

end Erdos1131


end
end PrivateSource_ParametricSystem


/- Source module GradedPolynomialEncoding. -/
section PrivateSource_GradedPolynomialEncoding

/-! Algebraic homogeneity of every coefficient in the Vandermonde construction. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

def HasHomogeneousCoefficients {σ R : Type*} [CommRing R]
    (p : Polynomial (MvPolynomial σ R)) (degree : ℕ) : Prop :=
  ∀ j, (p.coeff j).IsHomogeneous degree

namespace HasHomogeneousCoefficients

variable {σ R : Type*} [CommRing R]

theorem zero (degree : ℕ) :
    HasHomogeneousCoefficients (0 : Polynomial (MvPolynomial σ R)) degree := by
  intro j
  simpa using (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) degree)

theorem constant {p : MvPolynomial σ R} {degree : ℕ} (hp : p.IsHomogeneous degree) :
    HasHomogeneousCoefficients (Polynomial.C p) degree := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using hp
  · simpa [Polynomial.coeff_C, hj, Ne.symm hj] using
      (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) degree)

theorem one : HasHomogeneousCoefficients (1 : Polynomial (MvPolynomial σ R)) 0 := by
  simpa using constant (MvPolynomial.isHomogeneous_one (σ := σ) (R := R))

theorem indeterminate : HasHomogeneousCoefficients (Polynomial.X : Polynomial (MvPolynomial σ R)) 0 := by
  intro j
  by_cases hj : j = 1
  · subst j
    simpa using (MvPolynomial.isHomogeneous_one (σ := σ) (R := R))
  · simpa [Polynomial.coeff_X, hj, Ne.symm hj] using
      (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R) 0)

theorem add {p q : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) (hq : HasHomogeneousCoefficients q degree) :
    HasHomogeneousCoefficients (p + q) degree := by
  intro j
  rw [Polynomial.coeff_add]
  exact (hp j).add (hq j)

theorem neg {p : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) : HasHomogeneousCoefficients (-p) degree := by
  intro j
  rw [Polynomial.coeff_neg]
  exact (hp j).neg

theorem sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R)) (degree : ℕ)
    (hp : ∀ i ∈ s, HasHomogeneousCoefficients (p i) degree) :
    HasHomogeneousCoefficients (∑ i ∈ s, p i) degree := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i hi => hp i hi j)

theorem mul {p q : Polynomial (MvPolynomial σ R)} {degreeP degreeQ : ℕ}
    (hp : HasHomogeneousCoefficients p degreeP) (hq : HasHomogeneousCoefficients q degreeQ) :
    HasHomogeneousCoefficients (p * q) (degreeP + degreeQ) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun pair _ => (hp pair.1).mul (hq pair.2))

theorem pow {p : Polynomial (MvPolynomial σ R)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) (n : ℕ) :
    HasHomogeneousCoefficients (p ^ n) (degree * n) := by
  induction n with
  | zero => simpa using (one (σ := σ) (R := R))
  | succ n ih =>
    simpa only [pow_succ, Nat.mul_succ] using ih.mul hp

theorem prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial σ R))
    (degree : ι → ℕ) (hp : ∀ i ∈ s, HasHomogeneousCoefficients (p i) (degree i)) :
    HasHomogeneousCoefficients (∏ i ∈ s, p i) (∑ i ∈ s, degree i) := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simpa using (one (σ := σ) (R := R))
  | @insert i s his ih =>
    intro hp
    simp only [Finset.prod_insert his, Finset.sum_insert his]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial (MvPolynomial σ R))) (degree : ι → ℕ)
    (hM : ∀ i j, HasHomogeneousCoefficients (M i j) (degree j)) :
    HasHomogeneousCoefficients M.det (∑ j, degree j) := by
  classical
  rw [Matrix.det_apply]
  apply sum
  intro permutation hpermutation
  have hprod := prod Finset.univ (fun j => M (permutation j) j) degree
    (fun j _ => hM (permutation j) j)
  rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with hsign | hsign
  · simpa [hsign] using hprod
  · simpa [hsign] using hprod.neg

end HasHomogeneousCoefficients

theorem coefficientMoment_homogeneous {σ : Type*}
    {p : Polynomial (MvPolynomial σ ℚ)} {degree : ℕ}
    (hp : HasHomogeneousCoefficients p degree) : (coefficientMoment p).IsHomogeneous degree := by
  change (∑ j ∈ p.support, p.coeff j * algebraMap ℚ (MvPolynomial σ ℚ) (moment j)).IsHomogeneous degree
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  change (p.coeff j * MvPolynomial.C (moment j)).IsHomogeneous degree
  simpa only [mul_comm] using (hp j).C_mul (moment j)

end Erdos1131


end
end PrivateSource_GradedPolynomialEncoding


/- Source module EncodingDegrees. -/
section PrivateSource_EncodingDegrees

/-! Exact degrees of the rational forms and the lower-degree gradient tails. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem gapTotal_polynomial_homogeneous (k : ℕ) :
    (gapTotal (fun i : Fin k => (MvPolynomial.X i : MvPolynomial (Fin k) ℚ))).IsHomogeneous 2 := by
  unfold gapTotal
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_X_pow i 2)

theorem gapNodes_polynomial_homogeneous (k : ℕ) (i : Fin (k + 1)) :
    (gapNodes (fun j : Fin k => (MvPolynomial.X j : MvPolynomial (Fin k) ℚ)) i).IsHomogeneous 2 := by
  have hprefix : (gapPrefix (fun j : Fin k =>
      (MvPolynomial.X j : MvPolynomial (Fin k) ℚ) ^ 2) i).IsHomogeneous 2 := by
    unfold gapPrefix
    exact MvPolynomial.IsHomogeneous.sum _ _ _
      (fun j _ => MvPolynomial.isHomogeneous_X_pow j 2)
  unfold gapNodes
  convert! (gapTotal_polynomial_homogeneous k).neg.add (hprefix.C_mul 2) using 1

theorem vandermonde_homogeneousCoefficients {σ : Type*} {n : ℕ}
    (nodes : Fin n → Polynomial (MvPolynomial σ ℚ))
    (hnodes : ∀ i, HasHomogeneousCoefficients (nodes i) 2) :
    HasHomogeneousCoefficients (algebraicDelta nodes) (n * (n - 1)) := by
  have hdet := HasHomogeneousCoefficients.det (Matrix.vandermonde nodes)
    (fun j : Fin n => 2 * j.val) (fun i j => (hnodes i).pow j.val)
  change HasHomogeneousCoefficients (Matrix.vandermonde nodes).det (n * (n - 1))
  have hdegree : (∑ j : Fin n, 2 * j.val) = n * (n - 1) := by
    rw [← Finset.mul_sum, twice_sum_fin_val]
  rwa [hdegree] at hdet

theorem denominatorPolynomial_homogeneous (k : ℕ) :
    (denominatorPolynomial k).IsHomogeneous (clearedDegree k) := by
  let nodes := gapNodes (fun i : Fin k => (MvPolynomial.X i : MvPolynomial (Fin k) ℚ))
  have hdet : HasHomogeneousCoefficients
      (algebraicDelta (fun i => Polynomial.C (nodes i))) ((k + 1) * k) := by
    simpa only [Nat.add_sub_cancel] using vandermonde_homogeneousCoefficients
      (fun i => Polynomial.C (nodes i))
      (fun i => HasHomogeneousCoefficients.constant (gapNodes_polynomial_homogeneous k i))
  have hpow := hdet.pow 2 0
  have hmap := algebraicDelta_map Polynomial.C nodes
  rw [← hmap, ← Polynomial.C_pow, Polynomial.coeff_C_zero] at hpow
  change (algebraicDelta nodes ^ 2).IsHomogeneous (clearedDegree k)
  simpa only [clearedDegree, Nat.mul_comm] using hpow

theorem numeratorPolynomial_homogeneous (k : ℕ) :
    (numeratorPolynomial k).IsHomogeneous (clearedDegree k) := by
  unfold numeratorPolynomial encodingNumerator
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply coefficientMoment_homogeneous
  have hnodes : ∀ j : Fin (k + 1), HasHomogeneousCoefficients
      (Function.update
        (fun j => Polynomial.C (gapNodes (fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) ℚ)) j))
        i (Polynomial.C (gapTotal (fun a : Fin k => MvPolynomial.X a)) * Polynomial.X) j) 2 := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      simpa only [Nat.add_zero] using
        (HasHomogeneousCoefficients.constant (gapTotal_polynomial_homogeneous k)).mul
          HasHomogeneousCoefficients.indeterminate
    · rw [Function.update_of_ne hji]
      exact HasHomogeneousCoefficients.constant (gapNodes_polynomial_homogeneous k j)
  have hdet := vandermonde_homogeneousCoefficients _ hnodes
  simpa only [clearedDegree, Nat.add_sub_cancel, Nat.mul_comm] using hdet.pow 2

theorem parametricThreshold_homogeneous (k : ℕ) :
    (parametricThreshold k).IsHomogeneous (clearedDegree k) := by
  unfold parametricThreshold liftRationalCoefficients
  exact ((numeratorPolynomial_homogeneous k).map Polynomial.C).sub
    (((denominatorPolynomial_homogeneous k).map Polynomial.C).C_mul Polynomial.X)

theorem normalizedGradient_tail_homogeneous (k : ℕ) (i : Fin k) :
    (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)).IsHomogeneous (clearedDegree k - 1) :=
  (parametricThreshold_homogeneous k).pderiv.C_mul _

theorem normalizedGradient_tail_totalDegree_le (k : ℕ) (i : Fin k) :
    (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
      MvPolynomial.pderiv i (parametricThreshold k)).totalDegree ≤ clearedDegree k - 1 :=
  (normalizedGradient_tail_homogeneous k i).totalDegree_le

end Erdos1131


end
end PrivateSource_EncodingDegrees


/- Source module NormalizedBasis. -/
section PrivateSource_NormalizedBasis

/-! The fixed monomial basis over the parameter ring and after specialization. -/

open Module

noncomputable section

namespace Erdos1131

def reductionTails (k : ℕ) (i : Fin k) : MvPolynomial (Fin k) ParameterRing :=
  -(MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹)) *
    MvPolynomial.pderiv i (parametricThreshold k))

theorem reductionTails_lower (k : ℕ) :
    MonomialReduction.LowerDegree (clearedDegree k + 1) (reductionTails k) := by
  intro i a ha
  have hdegree := MvPolynomial.le_totalDegree ha
  change a.degree ≤ (-(_ : MvPolynomial (Fin k) ParameterRing)).totalDegree at hdegree
  rw [MvPolynomial.totalDegree_neg] at hdegree
  have htail := normalizedGradient_tail_totalDegree_le k i
  omega

theorem reduction_relation_eq_gradient (k : ℕ) :
    MonomialReduction.relation (clearedDegree k + 1) (reductionTails k) = normalizedGradient k := by
  funext i
  simp only [MonomialReduction.relation, reductionTails, normalizedGradient, sub_neg_eq_add]

theorem reductionIdeal_eq_gradientIdeal (k : ℕ) :
    MonomialReduction.relationIdeal (clearedDegree k + 1) (reductionTails k) = gradientIdeal k := by
  rw [MonomialReduction.relationIdeal, reduction_relation_eq_gradient, gradientIdeal]

def normalizedGradientBasis (k : ℕ) :
    Basis (BoundedIndex k (clearedDegree k)) ParameterRing (GradientQuotient k) :=
  (MonomialReduction.quotientBasis (Nat.zero_lt_succ (clearedDegree k))
    (reductionTails k) (reductionTails_lower k)).map
      (Ideal.quotientEquivAlgOfEq ParameterRing (reductionIdeal_eq_gradientIdeal k)).toLinearEquiv

theorem normalizedGradientBasis_apply (k : ℕ) (a : BoundedIndex k (clearedDegree k)) :
    normalizedGradientBasis k a = Ideal.Quotient.mk (gradientIdeal k) (boundedMonomial a) := by
  simp [normalizedGradientBasis, MonomialReduction.quotientBasis_apply,
    MonomialReduction.quotientMonomial]

instance normalizedGradient_free (k : ℕ) : Module.Free ParameterRing (GradientQuotient k) :=
  Module.Free.of_basis (normalizedGradientBasis k)

instance normalizedGradient_finite (k : ℕ) : Module.Finite ParameterRing (GradientQuotient k) :=
  Module.Finite.of_basis (normalizedGradientBasis k)

theorem lowerDegree_map {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) {tails : Fin k → MvPolynomial (Fin k) R}
    (htails : MonomialReduction.LowerDegree m tails) :
    MonomialReduction.LowerDegree m (fun i => (tails i).map φ) := by
  intro i a ha
  have hcoefficient : ((tails i).map φ).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
  have horiginal : (tails i).coeff a ≠ 0 := by
    intro hz
    apply hcoefficient
    simp [MvPolynomial.coeff_map, hz]
  exact htails i a (MvPolynomial.mem_support_iff.mpr horiginal)

def specializedTails {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S)
    (i : Fin k) : MvPolynomial (Fin k) S :=
  (reductionTails k i).map φ

theorem specializedTails_lower {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    MonomialReduction.LowerDegree (clearedDegree k + 1) (specializedTails k φ) :=
  lowerDegree_map φ (reductionTails_lower k)

abbrev SpecializedQuotient {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :=
  MonomialReduction.RelationQuotient (clearedDegree k + 1) (specializedTails k φ)

def specializedGradientBasis {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Basis (BoundedIndex k (clearedDegree k)) S (SpecializedQuotient k φ) :=
  MonomialReduction.quotientBasis (Nat.zero_lt_succ (clearedDegree k))
    (specializedTails k φ) (specializedTails_lower k φ)

instance specializedGradient_free {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.Free S (SpecializedQuotient k φ) :=
  Module.Free.of_basis (specializedGradientBasis k φ)

instance specializedGradient_finite {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.Finite S (SpecializedQuotient k φ) :=
  Module.Finite.of_basis (specializedGradientBasis k φ)

theorem specializedGradient_finrank {S : Type*} [Field S] (k : ℕ) (φ : ParameterRing →+* S) :
    Module.finrank S (SpecializedQuotient k φ) = (clearedDegree k + 1) ^ k := by
  rw [Module.finrank_eq_card_basis (specializedGradientBasis k φ), card_boundedIndex]

end Erdos1131


end
end PrivateSource_NormalizedBasis


/- Source module QuotientBaseChange. -/
section PrivateSource_QuotientBaseChange

/-! Coefficient specialization preserves the bounded monomial coordinates. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem relation_map {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) (i : Fin k) :
    (relation m tails i).map φ = relation m (fun j => (tails j).map φ) i := by
  simp [relation]

theorem relationIdeal_le_comap {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) :
    relationIdeal m tails ≤
      (relationIdeal m (fun i => (tails i).map φ)).comap (MvPolynomial.map φ) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change (relation m tails i).map φ ∈ relationIdeal m (fun j => (tails j).map φ)
  rw [relation_map]
  exact Ideal.subset_span ⟨i, rfl⟩

def quotientBaseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) :
    RelationQuotient m tails →+* RelationQuotient m (fun i => (tails i).map φ) :=
  Ideal.quotientMap _ (MvPolynomial.map φ) (relationIdeal_le_comap φ tails)

theorem quotientBaseChange_mk {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (p : MvPolynomial (Fin k) R) :
    quotientBaseChange (m := m) φ tails (Ideal.Quotient.mk (relationIdeal m tails) p) =
      Ideal.Quotient.mk (relationIdeal m (fun i => (tails i).map φ)) (p.map φ) := by
  rfl

theorem quotientBaseChange_algebraMap {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R) (r : R) :
    quotientBaseChange (m := m) φ tails (algebraMap R (RelationQuotient m tails) r) =
      algebraMap S (RelationQuotient m (fun i => (tails i).map φ)) (φ r) := by
  change Ideal.Quotient.mk _ ((MvPolynomial.C r).map φ) =
    Ideal.Quotient.mk _ (MvPolynomial.C (φ r))
  rw [MvPolynomial.map_C]

theorem quotientBaseChange_smul {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (r : R) (q : RelationQuotient m tails) :
    quotientBaseChange φ tails (r • q) = φ r • quotientBaseChange φ tails q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hsource := (Ideal.Quotient.mkₐ R (relationIdeal m tails)).toLinearMap.map_smul r p
  have htarget := (Ideal.Quotient.mkₐ S
    (relationIdeal m (fun i => (tails i).map φ))).toLinearMap.map_smul (φ r) (p.map φ)
  erw [← hsource, quotientBaseChange_mk, ← htarget]
  have hp : (r • p).map φ = φ r • p.map φ := by
    rw [← MvPolynomial.C_mul', map_mul, MvPolynomial.map_C, MvPolynomial.C_mul']
  exact congrArg (Ideal.Quotient.mk _) hp

theorem quotientBaseChange_basis {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (a : BoundedIndex k (m - 1)) :
    quotientBaseChange φ tails (quotientBasis hm tails htails a) =
      quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) a := by
  simp only [quotientBasis_apply, quotientMonomial, quotientBaseChange_mk,
    boundedMonomial, MvPolynomial.map_monomial, map_one]

theorem quotientBaseChange_repr {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails)
    (a : BoundedIndex k (m - 1)) :
    (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails)).repr
        (quotientBaseChange φ tails q) a =
      φ ((quotientBasis hm tails htails).repr q a) := by
  classical
  have hrep : quotientBaseChange φ tails q =
      ∑ b, φ ((quotientBasis hm tails htails).repr q b) •
        quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) b := by
    conv_lhs => rw [← (quotientBasis hm tails htails).sum_repr q]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [quotientBaseChange_smul, quotientBaseChange_basis]
  rw [hrep]
  exact congrFun ((quotientBasis hm (fun i => (tails i).map φ)
    (lowerDegree_map φ htails)).repr_sum_self
      (fun b => φ ((quotientBasis hm tails htails).repr q b))) a

end Erdos1131.MonomialReduction


end
end PrivateSource_QuotientBaseChange


/- Source module TraceConstruction. -/
section PrivateSource_TraceConstruction

/-! Multiplication and Hermite trace matrices in the fixed quotient basis. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem leftMulMatrix_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails) :
    Algebra.leftMulMatrix
        (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails))
        (quotientBaseChange φ tails q) =
      (Algebra.leftMulMatrix (quotientBasis hm tails htails) q).map φ := by
  classical
  ext a b
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply]
  rw [← quotientBaseChange_basis hm φ tails htails b, ← map_mul,
    quotientBaseChange_repr]

theorem trace_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) (q : RelationQuotient m tails) :
    Algebra.trace S (RelationQuotient m (fun i => (tails i).map φ))
        (quotientBaseChange φ tails q) =
      φ (Algebra.trace R (RelationQuotient m tails) q) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (quotientBasis hm tails htails),
    Algebra.trace_eq_matrix_trace
      (quotientBasis hm (fun i => (tails i).map φ) (lowerDegree_map φ htails)),
    leftMulMatrix_baseChange, AddMonoidHom.map_trace]

def hermiteMatrix {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    Matrix (BoundedIndex k (m - 1)) (BoundedIndex k (m - 1)) R :=
  (Algebra.traceForm R (RelationQuotient m tails)).toMatrix (quotientBasis hm tails htails)

theorem hermiteMatrix_apply {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a b : BoundedIndex k (m - 1)) :
    hermiteMatrix hm tails htails a b = Algebra.trace R (RelationQuotient m tails)
      (Ideal.Quotient.mk (relationIdeal m tails)
        (MvPolynomial.monomial (boundedExponent a + boundedExponent b) 1)) := by
  classical
  rw [hermiteMatrix, Algebra.traceForm_toMatrix]
  simp only [quotientBasis_apply, quotientMonomial, boundedMonomial, ← map_mul,
    MvPolynomial.monomial_mul_monomial, one_mul]

theorem hermiteMatrix_isSymm {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails) :
    (hermiteMatrix hm tails htails).IsSymm := by
  classical
  ext a b
  simp only [Matrix.transpose_apply, hermiteMatrix_apply, add_comm]

theorem hermiteMatrix_baseChange {R S : Type*} [CommRing R] [CommRing S] {k m : ℕ}
    (hm : 0 < m) (φ : R →+* S) (tails : Fin k → MvPolynomial (Fin k) R)
    (htails : LowerDegree m tails) :
    hermiteMatrix hm (fun i => (tails i).map φ) (lowerDegree_map φ htails) =
      (hermiteMatrix hm tails htails).map φ := by
  classical
  ext a b
  simp only [hermiteMatrix_apply, Matrix.map_apply]
  rw [← trace_baseChange hm φ tails htails, quotientBaseChange_mk,
    MvPolynomial.map_monomial]
  simp only [map_one]

end Erdos1131.MonomialReduction

namespace Erdos1131

def parametricHermiteMatrix (k : ℕ) :
    Matrix (BoundedIndex k (clearedDegree k)) (BoundedIndex k (clearedDegree k)) ParameterRing :=
  MonomialReduction.hermiteMatrix (Nat.zero_lt_succ (clearedDegree k))
    (reductionTails k) (reductionTails_lower k)

def specializedHermiteMatrix {S : Type*} [CommRing S] (k : ℕ) (φ : ParameterRing →+* S) :
    Matrix (BoundedIndex k (clearedDegree k)) (BoundedIndex k (clearedDegree k)) S :=
  MonomialReduction.hermiteMatrix (Nat.zero_lt_succ (clearedDegree k))
    (specializedTails k φ) (specializedTails_lower k φ)

theorem specializedHermiteMatrix_eq_map {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    specializedHermiteMatrix k φ = (parametricHermiteMatrix k).map φ :=
  MonomialReduction.hermiteMatrix_baseChange _ φ _ _

theorem parametricHermiteMatrix_isSymm (k : ℕ) : (parametricHermiteMatrix k).IsSymm :=
  MonomialReduction.hermiteMatrix_isSymm _ _ _

theorem specializedHermiteMatrix_isSymm {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) : (specializedHermiteMatrix k φ).IsSymm :=
  MonomialReduction.hermiteMatrix_isSymm _ _ _

def hermiteCharacteristicPolynomial (k : ℕ) : Polynomial ParameterRing :=
  (parametricHermiteMatrix k).charpoly

theorem specializedHermiteMatrix_charpoly {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    (specializedHermiteMatrix k φ).charpoly = (hermiteCharacteristicPolynomial k).map φ := by
  rw [specializedHermiteMatrix_eq_map, Matrix.charpoly_map]
  rfl

theorem hermiteCharacteristicPolynomial_monic (k : ℕ) :
    (hermiteCharacteristicPolynomial k).Monic := Matrix.charpoly_monic _

theorem hermiteCharacteristicPolynomial_natDegree (k : ℕ) :
    (hermiteCharacteristicPolynomial k).natDegree = (clearedDegree k + 1) ^ k := by
  rw [hermiteCharacteristicPolynomial, Matrix.charpoly_natDegree_eq_dim, card_boundedIndex]

end Erdos1131


end
end PrivateSource_TraceConstruction


/- Source module TraceNilpotents. -/
section PrivateSource_TraceNilpotents

/-! The algebra trace and its bilinear form annihilate nilpotents. -/

open Module

noncomputable section

namespace Erdos1131

theorem algebraTrace_nilpotent {R A : Type*} [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] {x : A} (hx : IsNilpotent x) :
    Algebra.trace R A x = 0 := by
  apply isNilpotent_iff_eq_zero.mp
  exact LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (Algebra.lmul R A))

theorem algebraTraceForm_nilpotent {R A : Type*} [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] {x : A} (hx : IsNilpotent x) (y : A) :
    Algebra.traceForm R A x y = 0 := by
  rw [Algebra.traceForm_apply]
  apply algebraTrace_nilpotent
  exact (Commute.all x y).isNilpotent_mul_right hx

theorem algebraTrace_eq_of_sub_nilpotent {R A : Type*} [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] {x y : A} (h : IsNilpotent (x - y)) :
    Algebra.trace R A x = Algebra.trace R A y := by
  have hzero := algebraTrace_nilpotent (R := R) h
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem nilradical_annihilates_traceForm {R A : Type*} [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] {x : A} (hx : x ∈ nilradical A) (y : A) :
    Algebra.traceForm R A x y = 0 :=
  algebraTraceForm_nilpotent (mem_nilradical.mp hx) y

def quotientNilradicalTrace (R A : Type*) [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] : A ⧸ nilradical A →ₗ[R] R :=
  ((nilradical A).restrictScalars R).liftQ (Algebra.trace R A)
    (fun x hx => algebraTrace_nilpotent (mem_nilradical.mp hx)) |>.comp
      (Submodule.Quotient.restrictScalarsEquiv R (nilradical A)).symm.toLinearMap

theorem quotientNilradicalTrace_mk {R A : Type*} [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] (x : A) :
    quotientNilradicalTrace R A (Ideal.Quotient.mk (nilradical A) x) =
      Algebra.trace R A x := by
  rfl

theorem algebraTrace_idempotent_nonneg {A : Type*} [CommRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] {e : A} (he : IsIdempotentElem e) :
    0 ≤ Algebra.trace ℝ A e := by
  have hf : IsIdempotentElem (Algebra.lmul ℝ A e) := he.map (Algebra.lmul ℝ A)
  rw [Algebra.trace_apply, (LinearMap.IsIdempotentElem.isProj_range _ hf).trace]
  positivity

theorem algebraTrace_idempotent_pos {A : Type*} [CommRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] {e : A} (he : IsIdempotentElem e) (hne : e ≠ 0) :
    0 < Algebra.trace ℝ A e := by
  have hf : IsIdempotentElem (Algebra.lmul ℝ A e) := he.map (Algebra.lmul ℝ A)
  have htrace : Algebra.trace ℝ A e ≠ 0 := by
    intro hz
    have hzero := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf hz
    have hvalue := congrArg (fun f : Module.End ℝ A => f 1) hzero
    apply hne
    simpa using hvalue
  exact lt_of_le_of_ne (algebraTrace_idempotent_nonneg he) (Ne.symm htrace)

theorem quotientNilradicalTrace_idempotent_pos {A : Type*} [CommRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] {e : A ⧸ nilradical A}
    (he : IsIdempotentElem e) (hne : e ≠ 0) :
    0 < quotientNilradicalTrace ℝ A e := by
  let π := Ideal.Quotient.mk (nilradical A)
  have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
    intro x hx
    exact mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  obtain ⟨e', he', hmap⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hker e
    (Ideal.Quotient.mk_surjective e) he
  rw [← hmap, quotientNilradicalTrace_mk]
  apply algebraTrace_idempotent_pos he'
  intro hz
  apply hne
  rw [← hmap, hz, map_zero]

end Erdos1131


end
end PrivateSource_TraceNilpotents


/- Source module ReducedAlgebra. -/
section PrivateSource_ReducedAlgebra

/-! The reduced algebra and the positive trace weights on its field factors. -/

open Module
open scoped BigOperators Classical

noncomputable section

namespace Erdos1131

section RealAlgebra

variable (A : Type*) [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A]

local instance : IsArtinianRing A := IsArtinianRing.of_finite ℝ A

abbrev ResidueProduct := ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal

def reducedProductEquiv : (A ⧸ nilradical A) ≃ₐ[ℝ] ResidueProduct A :=
  (IsArtinianRing.quotNilradicalEquivPi A).restrictScalars ℝ

def reducedProductTrace : ResidueProduct A →ₗ[ℝ] ℝ :=
  (quotientNilradicalTrace ℝ A).comp (reducedProductEquiv A).symm.toLinearMap

theorem reducedProductTrace_equiv (x : A ⧸ nilradical A) :
    reducedProductTrace A (reducedProductEquiv A x) = quotientNilradicalTrace ℝ A x := by
  simp [reducedProductTrace]

theorem residue_real_or_complex (m : MaximalSpectrum A) :
    Nonempty ((A ⧸ m.asIdeal) ≃ₐ[ℝ] ℝ) ∨ Nonempty ((A ⧸ m.asIdeal) ≃ₐ[ℝ] ℂ) := by
  letI : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Real.nonempty_algEquiv_or (A ⧸ m.asIdeal)

theorem reducedProductTrace_coordinate_pos (m : MaximalSpectrum A) :
    0 < reducedProductTrace A (Pi.single m 1) := by
  classical
  have he : IsIdempotentElem (Pi.single m (1 : A ⧸ m.asIdeal) : ResidueProduct A) := by
    simp [IsIdempotentElem, ← Pi.single_mul]
  have hne : (Pi.single m (1 : A ⧸ m.asIdeal) : ResidueProduct A) ≠ 0 := by
    intro h
    have hvalue := congrFun h m
    simpa using hvalue
  apply quotientNilradicalTrace_idempotent_pos
    (he.map (reducedProductEquiv A).symm.toRingHom)
  intro h
  apply hne
  exact (reducedProductEquiv A).symm.injective (by simpa using h)

end RealAlgebra

end Erdos1131


end
end PrivateSource_ReducedAlgebra


/- Source module ComplexTraceForm. -/
section PrivateSource_ComplexTraceForm

/-! A complex field factor contributes one positive and one negative square. -/

open Module

noncomputable section

namespace Erdos1131

def multiplicativeQuadratic {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (L : A →ₗ[R] R) : QuadraticForm R A :=
  LinearMap.BilinMap.toQuadraticMap (LinearMap.compr₂ (Algebra.lmul R A).toLinearMap L)

theorem multiplicativeQuadratic_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (L : A →ₗ[R] R) (x : A) : multiplicativeQuadratic L x = L (x * x) := rfl

theorem realLinear_complex_apply (L : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = L 1 * z.re + L Complex.I * z.im := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring

theorem complex_multiplicativeQuadratic_apply (L : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    multiplicativeQuadratic L z = L 1 * (z.re ^ 2 - z.im ^ 2) +
      2 * L Complex.I * z.re * z.im := by
  rw [multiplicativeQuadratic_apply, realLinear_complex_apply]
  simp only [Complex.mul_re, Complex.mul_im]
  ring

def complexDiagonalEquiv (a b : ℝ) : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.re + b / a * z.im, z.im]
  invFun u := ((u 0 - b / a * u 1 : ℝ) : ℂ) + (u 1 : ℂ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_add' z w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    ext i
    fin_cases i <;> simp <;> ring

def complexDiagonalWeights (a b : ℝ) : Fin 2 → ℝ := ![a, -(a + b ^ 2 / a)]

theorem complex_multiplicativeQuadratic_equivalent (L : ℂ →ₗ[ℝ] ℝ) (ha : L 1 ≠ 0) :
    QuadraticMap.Equivalent (multiplicativeQuadratic L)
      (QuadraticMap.weightedSumSquares ℝ (complexDiagonalWeights (L 1) (L Complex.I))) := by
  refine ⟨{ complexDiagonalEquiv (L 1) (L Complex.I) with map_app' := ?_ }⟩
  intro z
  rw [QuadraticMap.weightedSumSquares_apply, complex_multiplicativeQuadratic_apply]
  simp only [Fin.sum_univ_two, complexDiagonalWeights, complexDiagonalEquiv,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp
  ring

theorem complex_multiplicativeQuadratic_sigPos (L : ℂ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigPos (multiplicativeQuadratic L) = 1 := by
  classical
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (complex_multiplicativeQuadratic_equivalent L ha.ne')]
  have hnegative : -(L 1 + (L Complex.I) ^ 2 / L 1) < 0 := by
    have := div_nonneg (sq_nonneg (L Complex.I)) ha.le
    linarith
  have hset : {i : Fin 2 | 0 < complexDiagonalWeights (L 1) (L Complex.I) i} = {0} := by
    ext i
    fin_cases i <;> simp [complexDiagonalWeights, ha] <;> linarith
  rw [hset, Set.ncard_singleton]

theorem complex_multiplicativeQuadratic_sigNeg (L : ℂ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigNeg (multiplicativeQuadratic L) = 1 := by
  classical
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (complex_multiplicativeQuadratic_equivalent L ha.ne')]
  have hnegative : -(L 1 + (L Complex.I) ^ 2 / L 1) < 0 := by
    have := div_nonneg (sq_nonneg (L Complex.I)) ha.le
    linarith
  have hset : {i : Fin 2 | complexDiagonalWeights (L 1) (L Complex.I) i < 0} = {1} := by
    ext i
    fin_cases i <;> simp [complexDiagonalWeights, ha, not_lt_of_ge ha.le] <;> linarith
  rw [hset, Set.ncard_singleton]

end Erdos1131


end
end PrivateSource_ComplexTraceForm


/- Source module QuadraticProduct. -/
section PrivateSource_QuadraticProduct

/-! Inertia indices add over a finite product of quadratic spaces. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem ncard_sigma_predicate {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p : Sigma α → Prop) :
    {a | p a}.ncard = ∑ i, {a : α i | p ⟨i, a⟩}.ncard := by
  classical
  let e : {a : Sigma α // p a} ≃ (Σ i, {a : α i // p ⟨i, a⟩}) :=
    { toFun := fun a => ⟨a.val.fst, a.val.snd, a.property⟩
      invFun := fun a => ⟨⟨a.fst, a.snd.val⟩, a.snd.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    {a | p a}.ncard = Fintype.card {a : Sigma α // p a} :=
      (Set.fintypeCard_eq_ncard _).symm
    _ = Fintype.card (Σ i, {a : α i // p ⟨i, a⟩}) := Fintype.card_congr e
    _ = ∑ i, Fintype.card {a : α i // p ⟨i, a⟩} := Fintype.card_sigma
    _ = ∑ i, {a : α i | p ⟨i, a⟩}.ncard := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Set.fintypeCard_eq_ncard {a : α i | p ⟨i, a⟩}

def weightedPiIsometry {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) :
    (QuadraticMap.pi fun i => QuadraticMap.weightedSumSquares ℝ (w i)).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (fun a : Sigma α => w a.fst a.snd)) where
  toLinearEquiv := (LinearEquiv.piCurry ℝ (fun i (_ : α i) => ℝ)).symm
  map_app' x := by
    simp only [QuadraticMap.weightedSumSquares_apply, QuadraticMap.pi_apply,
      LinearEquiv.piCurry_symm_apply]
    rw [Fintype.sum_sigma]
    rfl

theorem sigPos_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)] [∀ i, Module.Finite ℝ (M i)]
    (Q : ∀ i, QuadraticForm ℝ (M i)) :
    sigPos (QuadraticMap.pi Q) = ∑ i, sigPos (Q i) := by
  classical
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  choose w hw using fun i => (Q i).equivalent_weightedSumSquares
  have h := (QuadraticMap.Equivalent.pi hw).trans ⟨weightedPiIsometry w⟩
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares h, ncard_sigma_predicate]
  apply Finset.sum_congr rfl
  intro i hi
  exact (QuadraticForm.sigPos_of_equiv_weightedSumSquares (hw i)).symm

theorem sigNeg_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)] [∀ i, Module.Finite ℝ (M i)]
    (Q : ∀ i, QuadraticForm ℝ (M i)) :
    sigNeg (QuadraticMap.pi Q) = ∑ i, sigNeg (Q i) := by
  have hneg : QuadraticMap.pi (fun i => -Q i) = -QuadraticMap.pi Q := by
    ext x
    simp [QuadraticMap.pi_apply]
  simpa only [sigNeg, hneg] using sigPos_pi (fun i => -Q i)

end Erdos1131


end
end PrivateSource_QuadraticProduct


/- Source module TraceProduct. -/
section PrivateSource_TraceProduct

/-! Decompose the trace quadratic form into its residue-field factors. -/

open Module
open scoped BigOperators Classical

noncomputable section

namespace Erdos1131

def productCoordinateFunctional {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra ℝ (A i)]
    (L : (∀ i, A i) →ₗ[ℝ] ℝ) (i : ι) : A i →ₗ[ℝ] ℝ :=
  L.comp (LinearMap.single ℝ A i)

theorem multiplicativeQuadratic_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra ℝ (A i)]
    (L : (∀ i, A i) →ₗ[ℝ] ℝ) :
    multiplicativeQuadratic L =
      QuadraticMap.pi (fun i => multiplicativeQuadratic (productCoordinateFunctional L i)) := by
  ext x
  simp only [multiplicativeQuadratic_apply, QuadraticMap.pi_apply,
    productCoordinateFunctional, LinearMap.comp_apply, LinearMap.single_apply]
  rw [← map_sum]
  exact congrArg L (Finset.univ_sum_single (x * x)).symm

section RealAlgebra

variable (A : Type*) [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A]

local instance : IsArtinianRing A := IsArtinianRing.of_finite ℝ A
local instance : Fintype (MaximalSpectrum A) := Fintype.ofFinite _

def nilradicalProjectionLinear : A →ₗ[ℝ] A ⧸ nilradical A :=
  (Ideal.Quotient.mkₐ ℝ (nilradical A)).toLinearMap

theorem traceQuadratic_eq_pullback :
    multiplicativeQuadratic (Algebra.trace ℝ A) =
      (multiplicativeQuadratic (quotientNilradicalTrace ℝ A)).comp
        (nilradicalProjectionLinear A) := by
  ext x
  change Algebra.trace ℝ A (x * x) = quotientNilradicalTrace ℝ A
    (Ideal.Quotient.mk (nilradical A) x * Ideal.Quotient.mk (nilradical A) x)
  rw [← map_mul, quotientNilradicalTrace_mk]

theorem reducedTraceQuadratic_product_equivalent :
    QuadraticMap.Equivalent (multiplicativeQuadratic (quotientNilradicalTrace ℝ A))
      (multiplicativeQuadratic (reducedProductTrace A)) := by
  refine ⟨{ (reducedProductEquiv A).toLinearEquiv with map_app' := ?_ }⟩
  intro x
  change quotientNilradicalTrace ℝ A
    ((reducedProductEquiv A).symm (reducedProductEquiv A x * reducedProductEquiv A x)) =
      quotientNilradicalTrace ℝ A (x * x)
  rw [← map_mul, AlgEquiv.symm_apply_apply]

theorem traceQuadratic_sigPos_product :
    sigPos (multiplicativeQuadratic (Algebra.trace ℝ A)) =
      ∑ m : MaximalSpectrum A,
        sigPos (multiplicativeQuadratic (productCoordinateFunctional (reducedProductTrace A) m)) := by
  rw [traceQuadratic_eq_pullback,
    sigPos_comp_surjective _ _ (Ideal.Quotient.mk_surjective :
      Function.Surjective (nilradicalProjectionLinear A)),
    (reducedTraceQuadratic_product_equivalent A).sigPos_eq,
    multiplicativeQuadratic_product, sigPos_pi]

theorem traceQuadratic_sigNeg_product :
    sigNeg (multiplicativeQuadratic (Algebra.trace ℝ A)) =
      ∑ m : MaximalSpectrum A,
        sigNeg (multiplicativeQuadratic (productCoordinateFunctional (reducedProductTrace A) m)) := by
  rw [traceQuadratic_eq_pullback,
    sigNeg_comp_surjective _ _ (Ideal.Quotient.mk_surjective :
      Function.Surjective (nilradicalProjectionLinear A)),
    (reducedTraceQuadratic_product_equivalent A).sigNeg_eq,
    multiplicativeQuadratic_product, sigNeg_pi]

theorem traceCoordinateFunctional_one_pos (m : MaximalSpectrum A) :
    0 < productCoordinateFunctional (reducedProductTrace A) m 1 :=
  reducedProductTrace_coordinate_pos A m

end RealAlgebra

end Erdos1131


end
end PrivateSource_TraceProduct


/- Source module RealTraceForm. -/
section PrivateSource_RealTraceForm

/-! A real field factor with positive trace weight contributes one positive square. -/

noncomputable section

namespace Erdos1131

theorem realLinear_real_apply (L : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : L x = L 1 * x := by
  have h := L.map_smul x 1
  simpa only [smul_eq_mul, mul_one, mul_comm] using h

theorem real_multiplicativeQuadratic_equivalent (L : ℝ →ₗ[ℝ] ℝ) :
    QuadraticMap.Equivalent (multiplicativeQuadratic L)
      (QuadraticMap.weightedSumSquares ℝ (fun _ : Unit => L 1)) := by
  refine ⟨{ (LinearEquiv.funUnique Unit ℝ ℝ).symm with map_app' := ?_ }⟩
  intro x
  rw [multiplicativeQuadratic_apply, realLinear_real_apply L (x * x)]
  simp [QuadraticMap.weightedSumSquares_apply, LinearEquiv.funUnique,
    mul_assoc]

theorem real_multiplicativeQuadratic_sigPos (L : ℝ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigPos (multiplicativeQuadratic L) = 1 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (real_multiplicativeQuadratic_equivalent L)]
  simp [ha]

theorem real_multiplicativeQuadratic_sigNeg (L : ℝ →ₗ[ℝ] ℝ) (ha : 0 < L 1) :
    sigNeg (multiplicativeQuadratic L) = 0 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (real_multiplicativeQuadratic_equivalent L)]
  simp [not_lt_of_ge ha.le]

end Erdos1131


end
end PrivateSource_RealTraceForm


/- Source module TraceSignature. -/
section PrivateSource_TraceSignature

/-! The signature of a finite real algebra's trace form counts its real residue fields. -/

open Module
open scoped BigOperators Classical

noncomputable section

namespace Erdos1131

theorem multiplicativeQuadratic_transport {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℝ A] [Algebra ℝ B] (L : A →ₗ[ℝ] ℝ) (e : A ≃ₐ[ℝ] B) :
    QuadraticMap.Equivalent (multiplicativeQuadratic L)
      (multiplicativeQuadratic (L.comp e.symm.toLinearMap)) := by
  refine ⟨{ e.toLinearEquiv with map_app' := ?_ }⟩
  intro x
  change L (e.symm (e x * e x)) = L (x * x)
  rw [← map_mul, AlgEquiv.symm_apply_apply]

def HasRealResidue {A : Type*} [CommRing A] [Algebra ℝ A] (m : MaximalSpectrum A) : Prop :=
  Nonempty ((A ⧸ m.asIdeal) ≃ₐ[ℝ] ℝ)

def realResidueCardinality (A : Type*) [CommRing A] [Algebra ℝ A] : ℕ :=
  Nat.card {m : MaximalSpectrum A // HasRealResidue m}

section RealAlgebra

variable (A : Type*) [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A]

local instance : IsArtinianRing A := IsArtinianRing.of_finite ℝ A
local instance : Fintype (MaximalSpectrum A) := Fintype.ofFinite _

theorem traceCoordinateFunctional_sigPos (m : MaximalSpectrum A) :
    sigPos (multiplicativeQuadratic
      (productCoordinateFunctional (reducedProductTrace A) m)) = 1 := by
  let L := productCoordinateFunctional (reducedProductTrace A) m
  have hpos := traceCoordinateFunctional_one_pos A m
  rcases residue_real_or_complex A m with hr | hc
  · obtain ⟨e⟩ := hr
    rw [(multiplicativeQuadratic_transport L e).sigPos_eq]
    apply real_multiplicativeQuadratic_sigPos
    simpa using hpos
  · obtain ⟨e⟩ := hc
    rw [(multiplicativeQuadratic_transport L e).sigPos_eq]
    apply complex_multiplicativeQuadratic_sigPos
    simpa using hpos

theorem traceCoordinateFunctional_sigNeg (m : MaximalSpectrum A) :
    sigNeg (multiplicativeQuadratic
      (productCoordinateFunctional (reducedProductTrace A) m)) =
        if HasRealResidue m then 0 else 1 := by
  let L := productCoordinateFunctional (reducedProductTrace A) m
  have hpos := traceCoordinateFunctional_one_pos A m
  by_cases hr : HasRealResidue m
  · rw [ite_eq_left hr]
    obtain ⟨e⟩ := hr
    rw [(multiplicativeQuadratic_transport L e).sigNeg_eq]
    apply real_multiplicativeQuadratic_sigNeg
    simpa using hpos
  · obtain ⟨e⟩ := (residue_real_or_complex A m).resolve_left hr
    rw [ite_eq_right hr, (multiplicativeQuadratic_transport L e).sigNeg_eq]
    apply complex_multiplicativeQuadratic_sigNeg
    simpa using hpos

theorem traceQuadratic_sigPos (A : Type*) [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] :
    sigPos (multiplicativeQuadratic (Algebra.trace ℝ A)) = Nat.card (MaximalSpectrum A) := by
  rw [traceQuadratic_sigPos_product]
  simp_rw [traceCoordinateFunctional_sigPos]
  simp [Nat.card_eq_fintype_card]

theorem traceQuadratic_sigNeg :
    sigNeg (multiplicativeQuadratic (Algebra.trace ℝ A)) =
      Nat.card {m : MaximalSpectrum A // ¬HasRealResidue m} := by
  rw [traceQuadratic_sigNeg_product]
  simp_rw [traceCoordinateFunctional_sigNeg]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hr : HasRealResidue m <;> simp [hr]

theorem traceQuadratic_signature :
    (sigPos (multiplicativeQuadratic (Algebra.trace ℝ A)) : ℤ) -
      (sigNeg (multiplicativeQuadratic (Algebra.trace ℝ A)) : ℤ) =
        (realResidueCardinality A : ℤ) := by
  rw [traceQuadratic_sigPos, traceQuadratic_sigNeg, realResidueCardinality]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hle := Fintype.card_subtype_le (HasRealResidue (A := A))
  omega

end RealAlgebra

end Erdos1131


end
end PrivateSource_TraceSignature


/- Source module RealCharacters. -/
section PrivateSource_RealCharacters

/-! Real characters correspond bijectively to real residue fields. -/

noncomputable section

namespace Erdos1131

variable {A : Type*} [CommRing A] [Algebra ℝ A]

theorem realCharacter_surjective (f : A →ₐ[ℝ] ℝ) : Function.Surjective f := by
  intro r
  refine ⟨algebraMap ℝ A r, ?_⟩
  simpa using f.commutes r

def realCharacterMaximal (f : A →ₐ[ℝ] ℝ) : MaximalSpectrum A :=
  ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f (realCharacter_surjective f)⟩

theorem realCharacter_hasRealResidue (f : A →ₐ[ℝ] ℝ) :
    HasRealResidue (realCharacterMaximal f) :=
  ⟨Ideal.quotientKerAlgEquivOfSurjective (realCharacter_surjective f)⟩

def characterToRealResidue (f : A →ₐ[ℝ] ℝ) :
    {m : MaximalSpectrum A // HasRealResidue m} :=
  ⟨realCharacterMaximal f, realCharacter_hasRealResidue f⟩

theorem realCharacters_eq_of_ker_eq (f g : A →ₐ[ℝ] ℝ) (h : RingHom.ker f = RingHom.ker g) :
    f = g := by
  ext x
  have hx : x - algebraMap ℝ A (f x) ∈ RingHom.ker f := by
    simp [RingHom.mem_ker, map_sub, f.commutes]
  rw [h] at hx
  have hz : g x - f x = 0 := by
    simpa [RingHom.mem_ker, map_sub, g.commutes] using hx
  exact (sub_eq_zero.mp hz).symm

theorem characterToRealResidue_injective :
    Function.Injective (characterToRealResidue (A := A)) := by
  intro f g h
  apply realCharacters_eq_of_ker_eq f g
  exact congrArg (fun m : {m : MaximalSpectrum A // HasRealResidue m} => m.val.asIdeal) h

theorem characterToRealResidue_surjective :
    Function.Surjective (characterToRealResidue (A := A)) := by
  rintro ⟨m, ⟨e⟩⟩
  let f : A →ₐ[ℝ] ℝ := e.toAlgHom.comp (Ideal.Quotient.mkₐ ℝ m.asIdeal)
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply MaximalSpectrum.ext
  ext x
  change f x = 0 ↔ x ∈ m.asIdeal
  change e (Ideal.Quotient.mk m.asIdeal x) = 0 ↔ x ∈ m.asIdeal
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    simpa using hx
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

def realCharactersEquiv :
    (A →ₐ[ℝ] ℝ) ≃ {m : MaximalSpectrum A // HasRealResidue m} :=
  Equiv.ofBijective characterToRealResidue
    ⟨characterToRealResidue_injective, characterToRealResidue_surjective⟩

theorem card_realCharacters (A : Type*) [CommRing A] [Algebra ℝ A] :
    Nat.card (A →ₐ[ℝ] ℝ) = realResidueCardinality A :=
  Nat.card_congr realCharactersEquiv

theorem traceQuadratic_signature_characters (A : Type*) [CommRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] :
    (sigPos (multiplicativeQuadratic (Algebra.trace ℝ A)) : ℤ) -
      (sigNeg (multiplicativeQuadratic (Algebra.trace ℝ A)) : ℤ) =
        (Nat.card (A →ₐ[ℝ] ℝ) : ℤ) := by
  rw [card_realCharacters, traceQuadratic_signature]

end Erdos1131


end
end PrivateSource_RealCharacters


/- Source module QuotientZeros. -/
section PrivateSource_QuotientZeros

/-! Real solutions of the defining equations are the quotient's real characters. -/

noncomputable section

namespace Erdos1131.MonomialReduction

def RelationZeroSet {k : ℕ} (m : ℕ) (tails : Fin k → MvPolynomial (Fin k) ℝ) :=
  {u : Fin k → ℝ // ∀ i, MvPolynomial.aeval u (relation m tails i) = 0}

theorem relationIdeal_le_evalKer {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (u : RelationZeroSet m tails) :
    relationIdeal m tails ≤ RingHom.ker (MvPolynomial.aeval u.val) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact u.property i

def zeroCharacter {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (u : RelationZeroSet m tails) : RelationQuotient m tails →ₐ[ℝ] ℝ :=
  Ideal.Quotient.liftₐ (relationIdeal m tails) (MvPolynomial.aeval u.val)
    (fun _ hp => relationIdeal_le_evalKer tails u hp)

def characterCoordinates {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (f : RelationQuotient m tails →ₐ[ℝ] ℝ) (i : Fin k) : ℝ :=
  f (Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.X i))

theorem character_eval_polynomial {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (f : RelationQuotient m tails →ₐ[ℝ] ℝ) (p : MvPolynomial (Fin k) ℝ) :
    f (Ideal.Quotient.mk (relationIdeal m tails) p) =
      MvPolynomial.aeval (characterCoordinates tails f) p := by
  have h : f.comp (Ideal.Quotient.mkₐ ℝ (relationIdeal m tails)) =
      MvPolynomial.aeval (characterCoordinates tails f) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [characterCoordinates]
  exact congrArg (fun g : MvPolynomial (Fin k) ℝ →ₐ[ℝ] ℝ => g p) h

theorem characterCoordinates_zero {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (f : RelationQuotient m tails →ₐ[ℝ] ℝ) (i : Fin k) :
    MvPolynomial.aeval (characterCoordinates tails f) (relation m tails i) = 0 := by
  rw [← character_eval_polynomial]
  have hz : Ideal.Quotient.mk (relationIdeal m tails) (relation m tails i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [hz, map_zero]

def characterZero {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (f : RelationQuotient m tails →ₐ[ℝ] ℝ) : RelationZeroSet m tails :=
  ⟨characterCoordinates tails f, characterCoordinates_zero tails f⟩

theorem characterZero_zeroCharacter {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (u : RelationZeroSet m tails) : characterZero tails (zeroCharacter tails u) = u := by
  apply Subtype.ext
  funext i
  simp [characterZero, characterCoordinates, zeroCharacter, Ideal.Quotient.liftₐ,
    Ideal.Quotient.lift_mk]

theorem zeroCharacter_characterZero {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ)
    (f : RelationQuotient m tails →ₐ[ℝ] ℝ) : zeroCharacter tails (characterZero tails f) = f := by
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change MvPolynomial.aeval (characterCoordinates tails f) p =
    f (Ideal.Quotient.mk (relationIdeal m tails) p)
  exact (character_eval_polynomial tails f p).symm

def zerosEquivCharacters {k m : ℕ} (tails : Fin k → MvPolynomial (Fin k) ℝ) :
    RelationZeroSet m tails ≃ (RelationQuotient m tails →ₐ[ℝ] ℝ) where
  toFun := zeroCharacter tails
  invFun := characterZero tails
  left_inv := characterZero_zeroCharacter tails
  right_inv := zeroCharacter_characterZero tails

theorem finite_relationZeroSet {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ℝ) (htails : LowerDegree m tails) :
    Finite (RelationZeroSet m tails) := by
  letI : Module.Finite ℝ (RelationQuotient m tails) :=
    Module.Finite.of_basis (quotientBasis hm tails htails)
  letI : IsArtinianRing (RelationQuotient m tails) := IsArtinianRing.of_finite ℝ _
  exact Finite.of_equiv {p : MaximalSpectrum (RelationQuotient m tails) // HasRealResidue p}
    (realCharactersEquiv.symm.trans (zerosEquivCharacters tails).symm)

end Erdos1131.MonomialReduction


end
end PrivateSource_QuotientZeros


/- Source module HermiteSignature. -/
section PrivateSource_HermiteSignature

/-! The Hermite signature identity, including quotients with nilpotent elements. -/

open Module

noncomputable section

namespace Erdos1131

def matrixSignature {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℤ :=
  (sigPos M.toQuadraticForm' : ℤ) - (sigNeg M.toQuadraticForm' : ℤ)

theorem traceMatrix_equivalent {A : Type*} [CommRing A] [Algebra ℝ A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ A) :
    QuadraticMap.Equivalent (multiplicativeQuadratic (Algebra.trace ℝ A))
      ((Algebra.traceForm ℝ A).toMatrix b).toQuadraticForm' := by
  refine ⟨{ b.equivFun with map_app' := ?_ }⟩
  intro x
  change (Matrix.toLinearMap₂' ℝ ((Algebra.traceForm ℝ A).toMatrix b))
      (b.equivFun x) (b.equivFun x) = Algebra.trace ℝ A (x * x)
  rw [Matrix.toLinearMap₂'_apply', LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
  simp

theorem traceMatrix_signature {A : Type*} [CommRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ A) :
    matrixSignature ((Algebra.traceForm ℝ A).toMatrix b) = (Nat.card (A →ₐ[ℝ] ℝ) : ℤ) := by
  rw [matrixSignature, ← (traceMatrix_equivalent b).sigPos_eq,
    ← (traceMatrix_equivalent b).sigNeg_eq]
  exact traceQuadratic_signature_characters A

end Erdos1131

namespace Erdos1131.MonomialReduction

theorem hermiteMatrix_signature {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ℝ) (htails : LowerDegree m tails) :
    matrixSignature (hermiteMatrix hm tails htails) = (Nat.card (RelationZeroSet m tails) : ℤ) := by
  classical
  letI : Module.Finite ℝ (RelationQuotient m tails) :=
    Module.Finite.of_basis (quotientBasis hm tails htails)
  rw [hermiteMatrix, traceMatrix_signature]
  exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_congr (zerosEquivCharacters tails)).symm

end Erdos1131.MonomialReduction


end
end PrivateSource_HermiteSignature


/- Source module SymmetricNullity. -/
section PrivateSource_SymmetricNullity

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


end
end PrivateSource_SymmetricNullity


/- Source module SignatureContinuity. -/
section PrivateSource_SignatureContinuity

/-! Constant nullity forces locally constant inertia in a continuous symmetric family. -/

open Filter
open scoped Topology Matrix

noncomputable section

namespace Erdos1131

theorem continuous_matrix_quadratic {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (M : X → Matrix ι ι ℝ)
    (hM : ∀ i j, Continuous (fun x => M x i j)) :
    Continuous (fun z : X × (ι → ℝ) => (M z.fst).toQuadraticForm' z.snd) := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
  fun_prop

theorem matrixSignature_eventually_constant {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (M : X → Matrix ι ι ℝ)
    (hM : ∀ i j, Continuous (fun x => M x i j))
    (hsym : ∀ x, (M x).IsSymm) (x₀ : X)
    (hnull : ∀ᶠ x in 𝓝 x₀, (M x).charpoly.natTrailingDegree =
      (M x₀).charpoly.natTrailingDegree) :
    ∀ᶠ x in 𝓝 x₀, matrixSignature (M x) = matrixSignature (M x₀) := by
  have hcontinuous := continuous_matrix_quadratic M hM
  have hpos := sigPos_eventually_ge (fun x => (M x).toQuadraticForm') hcontinuous x₀
  have hneg := sigNeg_eventually_ge (fun x => (M x).toQuadraticForm') hcontinuous x₀
  filter_upwards [hpos, hneg, hnull] with x hpx hnx hnullx
  have hx := matrix_inertia_add_trailingDegree (M x) (hsym x)
  have hx₀ := matrix_inertia_add_trailingDegree (M x₀) (hsym x₀)
  have hp : sigPos (M x).toQuadraticForm' = sigPos (M x₀).toQuadraticForm' := by omega
  have hn : sigNeg (M x).toQuadraticForm' = sigNeg (M x₀).toQuadraticForm' := by omega
  simp only [matrixSignature, hp, hn]

end Erdos1131


end
end PrivateSource_SignatureContinuity


/- Source module PolynomialDifferentiation. -/
section PrivateSource_PolynomialDifferentiation

/-! Coordinate differentiation and the normalized-gradient equations. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def coordinateLine {k : ℕ} (u : Fin k → ℝ) (i : Fin k) (t : ℝ) : Fin k → ℝ :=
  u + t • Pi.single i 1

theorem coordinateLine_zero {k : ℕ} (u : Fin k → ℝ) (i : Fin k) :
    coordinateLine u i 0 = u := by simp [coordinateLine]

theorem coordinateLine_hasDerivAt {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) :
    HasDerivAt (fun t => coordinateLine u i t j) (if j = i then 1 else 0) 0 := by
  by_cases hji : j = i
  · subst j
    convert! (hasDerivAt_const (0 : ℝ) (u i)).add (hasDerivAt_id (0 : ℝ)) using 1 <;>
      simp [coordinateLine] <;> rfl
  · simpa [coordinateLine, Pi.single_apply, hji] using hasDerivAt_const (0 : ℝ) (u j)

theorem differentiable_eval₂ {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) :
    Differentiable ℝ (fun u : Fin k → ℝ => p.eval₂ φ u) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    fun_prop
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (by fun_prop)

theorem hasDerivAt_eval₂_coordinateLine {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) (i : Fin k) :
    HasDerivAt (fun t => p.eval₂ φ (coordinateLine u i t))
      ((MvPolynomial.pderiv i p).eval₂ φ u) 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero, MvPolynomial.eval₂_C]
      using hasDerivAt_const (0 : ℝ) (φ a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;>
      simp only [map_add, MvPolynomial.eval₂_add] <;> rfl
  | mul_X p j hp =>
    have hproduct := hp.mul (coordinateLine_hasDerivAt u i j)
    convert! hproduct using 1
    · ext t
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply]
    · by_cases hji : j = i
      · subst j
        simp [coordinateLine, mul_comm, add_comm]
      · simp [MvPolynomial.pderiv_X_of_ne hji, coordinateLine, hji, mul_comm]

theorem fderiv_eval₂_coordinate {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) (i : Fin k) :
    (fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u) (Pi.single i 1) =
      (MvPolynomial.pderiv i p).eval₂ φ u := by
  have hline := (differentiable_eval₂ φ p u).hasFDerivAt.hasLineDerivAt (Pi.single i 1)
  change HasDerivAt (fun t : ℝ => p.eval₂ φ (coordinateLine u i t))
    ((fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u) (Pi.single i 1)) 0 at hline
  exact hline.unique (hasDerivAt_eval₂_coordinateLine φ p u i)

theorem fderiv_eval₂_eq_zero_iff {A : Type*} [CommRing A] {k : ℕ}
    (φ : A →+* ℝ) (p : MvPolynomial (Fin k) A) (u : Fin k → ℝ) :
    fderiv ℝ (fun v : Fin k → ℝ => p.eval₂ φ v) u = 0 ↔
      ∀ i, (MvPolynomial.pderiv i p).eval₂ φ u = 0 := by
  constructor
  · intro h i
    rw [← fderiv_eval₂_coordinate φ p u i, h]
    simp
  · intro h
    ext v
    have hv : v = ∑ i : Fin k, v i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply, smul_eq_mul]
    rw [hv, map_sum]
    simp [fderiv_eval₂_coordinate, h]

def augmentedPolynomial (k : ℕ) : MvPolynomial (Fin k) ParameterRing :=
  parametricThreshold k + ∑ i : Fin k, MvPolynomial.X i ^ (clearedDegree k + 2)

theorem evaluate_augmentedPolynomial {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    evaluateParametricSystem t u (augmentedPolynomial k) =
      HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t) u := by
  unfold augmentedPolynomial
  rw [map_add, evaluate_parametricThreshold, map_sum]
  have hdegree : clearedDegree k + 2 = 2 * ((k + 1) * k + 1) := by
    unfold clearedDegree
    omega
  simp only [map_pow, evaluateParametricSystem, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, HomogeneousLift.lift, HomogeneousLift.penalty, hdegree]

theorem pderiv_augmentedPolynomial {k : ℕ} (i : Fin k) :
    MvPolynomial.pderiv i (augmentedPolynomial k) =
      MvPolynomial.pderiv i (parametricThreshold k) +
        ((clearedDegree k + 2 : ℕ) : MvPolynomial (Fin k) ParameterRing) *
          MvPolynomial.X i ^ (clearedDegree k + 1) := by
  classical
  unfold augmentedPolynomial
  rw [map_add, map_sum]
  congr 1
  simp [MvPolynomial.pderiv_X, Pi.single_apply]

theorem evaluate_pderiv_augmentedPolynomial {k : ℕ} (t : ℝ) (u : Fin k → ℝ) (i : Fin k) :
    evaluateParametricSystem t u (MvPolynomial.pderiv i (augmentedPolynomial k)) =
      ((clearedDegree k + 2 : ℕ) : ℝ) * evaluateParametricSystem t u (normalizedGradient k i) := by
  have hcoefficient : evaluateParametricSystem t u
      (MvPolynomial.C (Polynomial.C (((clearedDegree k + 2 : ℕ) : ℚ)⁻¹))) =
      (((clearedDegree k + 2 : ℕ) : ℝ)⁻¹) := by
    simp only [evaluateParametricSystem, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      specializeParameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    rw [map_inv₀, map_natCast]
  have hcoordinate : evaluateParametricSystem t u (MvPolynomial.X i) = u i := by
    simp [evaluateParametricSystem]
  rw [pderiv_augmentedPolynomial]
  unfold normalizedGradient
  simp only [map_add, map_mul, map_pow, map_natCast, hcoefficient, hcoordinate]
  have hdegree : ((clearedDegree k + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show clearedDegree k + 2 ≠ 0 by omega)
  field_simp
  ring

theorem normalizedGradient_zero_iff_critical {k : ℕ} (t : ℝ) (u : Fin k → ℝ) :
    (∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0) ↔
      fderiv ℝ (HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t)) u = 0 := by
  have hfunctions : (fun v : Fin k → ℝ => (augmentedPolynomial k).eval₂ (specializeParameter t) v) =
      HomogeneousLift.lift ((k + 1) * k) (thresholdExpression k t) := by
    funext v
    exact evaluate_augmentedPolynomial t v
  rw [← hfunctions, fderiv_eval₂_eq_zero_iff]
  have hdegree : (((clearedDegree k + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show clearedDegree k + 2 ≠ 0 by omega)
  change (∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0) ↔
    ∀ i, evaluateParametricSystem t u (MvPolynomial.pderiv i (augmentedPolynomial k)) = 0
  simp only [evaluate_pderiv_augmentedPolynomial, mul_eq_zero, hdegree, false_or]

theorem normalizedGradient_original_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    {u | ∀ i, evaluateParametricSystem t u (normalizedGradient k i) = 0} = {0} ↔
      t ≤ minimum (k + 1) := by
  simp only [normalizedGradient_zero_iff_critical]
  exact original_critical_point_threshold hk t

end Erdos1131


end
end PrivateSource_PolynomialDifferentiation


/- Source module NormalizedTrace. -/
section PrivateSource_NormalizedTrace

/-! The specialized Hermite matrix detects the original interpolation threshold. -/

noncomputable section

namespace Erdos1131

theorem aeval_specialize {k : ℕ} (t : ℝ) (u : Fin k → ℝ)
    (p : MvPolynomial (Fin k) ParameterRing) :
    MvPolynomial.aeval u (p.map (specializeParameter t)) = evaluateParametricSystem t u p := by
  change MvPolynomial.eval₂ (RingHom.id ℝ) u (p.map (specializeParameter t)) =
    MvPolynomial.eval₂ (specializeParameter t) u p
  rw [MvPolynomial.eval₂_map]
  rfl

theorem specialized_relation_eval {k : ℕ} (t : ℝ) (u : Fin k → ℝ) (i : Fin k) :
    MvPolynomial.aeval u
        (MonomialReduction.relation (clearedDegree k + 1)
          (specializedTails k (specializeParameter t)) i) =
      evaluateParametricSystem t u (normalizedGradient k i) := by
  have h := congrFun (reduction_relation_eq_gradient k) i
  rw [← h, ← aeval_specialize, MonomialReduction.relation_map]
  rfl

abbrev NormalizedZeroSet (k : ℕ) (t : ℝ) :=
  MonomialReduction.RelationZeroSet (clearedDegree k + 1)
    (specializedTails k (specializeParameter t))

theorem specializedHermite_signature (k : ℕ) (t : ℝ) :
    matrixSignature (specializedHermiteMatrix k (specializeParameter t)) =
      (Nat.card (NormalizedZeroSet k t) : ℤ) :=
  MonomialReduction.hermiteMatrix_signature _ _ _

theorem normalized_origin_zero {k : ℕ} (hk : 0 < k) (t : ℝ) :
    ∀ i, evaluateParametricSystem t 0 (normalizedGradient k i) = 0 := by
  apply (normalizedGradient_zero_iff_critical t 0).mpr
  exact HomogeneousLift.lift_fderiv_zero
    (Nat.mul_pos (Nat.succ_pos k) hk) (threshold_homogeneous k t)
    (threshold_differentiable k t 0)

theorem nat_card_set_eq_one_iff {α : Type*} (s : Set α) (x : α) (hx : x ∈ s) :
    Nat.card s = 1 ↔ s = {x} := by
  constructor
  · intro h
    have hsub := (Nat.card_eq_one_iff_unique.mp h).1
    ext y
    constructor
    · intro hy
      have heq := congrArg Subtype.val (hsub.elim (⟨y, hy⟩ : s) (⟨x, hx⟩ : s))
      exact Set.mem_singleton_iff.mpr heq
    · intro hy
      simpa only [Set.mem_singleton_iff.mp hy] using hx
  · intro h
    rw [h]
    simp

theorem specializedHermite_signature_threshold {k : ℕ} (hk : 0 < k) (t : ℝ) :
    matrixSignature (specializedHermiteMatrix k (specializeParameter t)) = 1 ↔
      t ≤ minimum (k + 1) := by
  rw [specializedHermite_signature]
  have hcast : (Nat.card (NormalizedZeroSet k t) : ℤ) = 1 ↔
      Nat.card (NormalizedZeroSet k t) = 1 := by omega
  rw [hcast]
  let s : Set (Fin k → ℝ) := {u | ∀ i, MvPolynomial.aeval u
    (MonomialReduction.relation (clearedDegree k + 1)
      (specializedTails k (specializeParameter t)) i) = 0}
  have hz : (0 : Fin k → ℝ) ∈ s := by
    simpa only [s, Set.mem_setOf_eq, specialized_relation_eval] using normalized_origin_zero hk t
  change Nat.card s = 1 ↔ _
  rw [nat_card_set_eq_one_iff s 0 hz]
  simpa only [s, specialized_relation_eval] using normalizedGradient_original_threshold hk t

end Erdos1131


end
end PrivateSource_NormalizedTrace


/- Source module BoundaryPolynomial. -/
section PrivateSource_BoundaryPolynomial

/-! The nonzero coefficient polynomial controlling exceptional parameters. -/

noncomputable section

namespace Erdos1131

def boundaryIndex (k : ℕ) : ℕ := (hermiteCharacteristicPolynomial k).natTrailingDegree

def boundaryPolynomial (k : ℕ) : Polynomial ℚ :=
  (hermiteCharacteristicPolynomial k).coeff (boundaryIndex k)

theorem boundaryPolynomial_ne_zero (k : ℕ) : boundaryPolynomial k ≠ 0 :=
  Polynomial.coeff_natTrailingDegree_ne_zero.mpr (hermiteCharacteristicPolynomial_monic k).ne_zero

theorem hermiteCharacteristicPolynomial_coeff_below (k j : ℕ) (hj : j < boundaryIndex k) :
    (hermiteCharacteristicPolynomial k).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj

theorem specialized_charpoly_coeff_boundary {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    (specializedHermiteMatrix k φ).charpoly.coeff (boundaryIndex k) = φ (boundaryPolynomial k) := by
  rw [specializedHermiteMatrix_charpoly, Polynomial.coeff_map]
  rfl

theorem specialized_charpoly_coeff_below {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) (j : ℕ) (hj : j < boundaryIndex k) :
    (specializedHermiteMatrix k φ).charpoly.coeff j = 0 := by
  rw [specializedHermiteMatrix_charpoly, Polynomial.coeff_map,
    hermiteCharacteristicPolynomial_coeff_below k j hj, map_zero]

theorem specialized_charpoly_trailingDegree {S : Type*} [CommRing S] [Nontrivial S]
    (k : ℕ) (φ : ParameterRing →+* S) (hφ : φ (boundaryPolynomial k) ≠ 0) :
    (specializedHermiteMatrix k φ).charpoly.natTrailingDegree = boundaryIndex k := by
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rwa [specialized_charpoly_coeff_boundary]
  · apply Polynomial.le_natTrailingDegree (Matrix.charpoly_monic _).ne_zero
    intro j hj
    exact specialized_charpoly_coeff_below k φ j hj

def boundaryRoots (k : ℕ) : Set ℝ := (boundaryPolynomial k).rootSet ℝ

theorem boundaryRoots_finite (k : ℕ) : (boundaryRoots k).Finite :=
  Polynomial.rootSet_finite _ _

theorem mem_boundaryRoots (k : ℕ) (t : ℝ) :
    t ∈ boundaryRoots k ↔ specializeParameter t (boundaryPolynomial k) = 0 := by
  rw [boundaryRoots, Polynomial.mem_rootSet_of_ne (boundaryPolynomial_ne_zero k)]
  rfl

theorem charpoly_trailingDegree_off_boundary (k : ℕ) (t : ℝ) (ht : t ∉ boundaryRoots k) :
    (specializedHermiteMatrix k (specializeParameter t)).charpoly.natTrailingDegree =
      boundaryIndex k := by
  apply specialized_charpoly_trailingDegree
  exact (mem_boundaryRoots k t).not.mp ht

end Erdos1131


end
end PrivateSource_BoundaryPolynomial


/- Source module MinimumBoundary. -/
section PrivateSource_MinimumBoundary

/-! The original minimum is a real root of the explicit boundary polynomial. -/

open Filter
open scoped Topology

noncomputable section

namespace Erdos1131

theorem continuous_specializeParameter (p : ParameterRing) :
    Continuous (fun t : ℝ => specializeParameter t p) := by
  convert (p.map (algebraMap ℚ ℝ)).continuous using 1
  ext t
  simp [specializeParameter, Polynomial.eval_map]

theorem continuous_specializedHermite_entry (k : ℕ)
    (a b : BoundedIndex k (clearedDegree k)) :
    Continuous (fun t : ℝ => specializedHermiteMatrix k (specializeParameter t) a b) := by
  simp only [specializedHermiteMatrix_eq_map, Matrix.map_apply]
  exact continuous_specializeParameter (parametricHermiteMatrix k a b)

theorem hermiteSignature_eventually_constant (k : ℕ) (t : ℝ) (ht : t ∉ boundaryRoots k) :
    ∀ᶠ s in 𝓝 t, matrixSignature (specializedHermiteMatrix k (specializeParameter s)) =
      matrixSignature (specializedHermiteMatrix k (specializeParameter t)) := by
  have hvalue : specializeParameter t (boundaryPolynomial k) ≠ 0 :=
    (mem_boundaryRoots k t).not.mp ht
  have hnonzero : ∀ᶠ s in 𝓝 t, specializeParameter s (boundaryPolynomial k) ≠ 0 :=
    (isOpen_ne.preimage (continuous_specializeParameter (boundaryPolynomial k))).mem_nhds hvalue
  apply matrixSignature_eventually_constant
    (fun s => specializedHermiteMatrix k (specializeParameter s))
    (continuous_specializedHermite_entry k)
    (fun s => specializedHermiteMatrix_isSymm k (specializeParameter s)) t
  filter_upwards [hnonzero] with s hs
  rw [specialized_charpoly_trailingDegree k (specializeParameter s) hs,
    specialized_charpoly_trailingDegree k (specializeParameter t) hvalue]

theorem minimum_mem_boundaryRoots {k : ℕ} (hk : 0 < k) :
    minimum (k + 1) ∈ boundaryRoots k := by
  by_contra hroot
  have hloc := hermiteSignature_eventually_constant k (minimum (k + 1)) hroot
  have hsig : matrixSignature
      (specializedHermiteMatrix k (specializeParameter (minimum (k + 1)))) = 1 :=
    (specializedHermite_signature_threshold hk _).mpr le_rfl
  have hle : ∀ᶠ s in 𝓝 (minimum (k + 1)), s ≤ minimum (k + 1) := by
    filter_upwards [hloc] with s hs
    exact (specializedHermite_signature_threshold hk s).mp (hs.trans hsig)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hle
  have hp : minimum (k + 1) + ε / 2 ∈ Metric.ball (minimum (k + 1)) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    rw [abs_of_pos (by positivity)]
    linarith
  have hbad := hball hp
  change minimum (k + 1) + ε / 2 ≤ minimum (k + 1) at hbad
  linarith

theorem minimum_in_open_interval {k : ℕ} (hk : 0 < k) :
    minimum (k + 1) ∈ Set.Ioo (0 : ℝ) 2 := by
  constructor
  · have hn : 0 < k + 1 := Nat.succ_pos _
    exact lt_of_lt_of_le (by positivity) (minimum_lower_bound hn)
  · exact minimum_lt_two (by omega)

end Erdos1131


end
end PrivateSource_MinimumBoundary


/- Source module WeightedReduction. -/
section PrivateSource_WeightedReduction

/-! Parameter-degree bounds are preserved by the terminating monomial reduction. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

def WeightBound {k : ℕ} (bound : ℕ) (p : MvPolynomial (Fin k) ParameterRing) : Prop :=
  ∀ a, p.coeff a ≠ 0 → a.degree + 2 * (p.coeff a).natDegree ≤ bound

theorem weightBound_mono {k a b : ℕ} {p : MvPolynomial (Fin k) ParameterRing}
    (hab : a ≤ b) (hp : WeightBound a p) : WeightBound b p :=
  fun c hc => (hp c hc).trans hab

theorem weightBound_monomial {k : ℕ} (a : Fin k →₀ ℕ) :
    WeightBound a.degree (MvPolynomial.monomial a (1 : ParameterRing)) := by
  classical
  intro b hb
  by_cases h : b = a
  · subst b
    simp
  · simp [MvPolynomial.coeff_monomial] at hb
    exact (h hb.symm).elim

theorem weightBound_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin k) ParameterRing) (bound : ℕ)
    (hp : ∀ i ∈ s, WeightBound bound (p i)) : WeightBound bound (∑ i ∈ s, p i) := by
  classical
  intro a ha
  have hsum : ∑ i ∈ s, (p i).coeff a ≠ 0 := by
    simpa only [MvPolynomial.coeff_sum] using ha
  obtain ⟨i, hi, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdegree : a.degree ≤ bound := by
    have := hp i hi a hcoeff
    omega
  have hpieces : ∀ j ∈ s, ((p j).coeff a).natDegree ≤ (bound - a.degree) / 2 := by
    intro j hj
    by_cases hz : (p j).coeff a = 0
    · simp [hz]
    · have := hp j hj a hz
      omega
  have hbound := Polynomial.natDegree_sum_le_of_forall_le s
    (fun j => (p j).coeff a) hpieces
  rw [MvPolynomial.coeff_sum]
  omega

theorem weightBound_C_mul {k bound : ℕ} (q : ParameterRing)
    {p : MvPolynomial (Fin k) ParameterRing} (hp : WeightBound bound p) :
    WeightBound (bound + 2 * q.natDegree) (MvPolynomial.C q * p) := by
  intro a ha
  rw [MvPolynomial.coeff_C_mul] at ha ⊢
  have hnonzero : p.coeff a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  have hweight := hp a hnonzero
  have hdegree := Polynomial.natDegree_mul_le (p := q) (q := p.coeff a)
  omega

theorem normalMonomial_weightBound {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (hweight : ∀ i, WeightBound m (tails i)) (a : Fin k →₀ ℕ) :
    WeightBound a.degree (normalMonomial tails htails a) := by
  classical
  rw [normalMonomial]
  split_ifs with h
  · apply weightBound_sum
    intro b hb
    have hrec := normalMonomial_weightBound tails htails hweight
      (a - Finsupp.single h.choose m + b.val)
    have hcoefficient : (tails h.choose).coeff b.val ≠ 0 :=
      MvPolynomial.mem_support_iff.mp b.property
    have htail := hweight h.choose b.val hcoefficient
    have hsingle : Finsupp.single h.choose m ≤ a :=
      Finsupp.single_le_iff.mpr h.choose_spec
    have hdegree : (a - Finsupp.single h.choose m).degree + m = a.degree := by
      have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hsingle)
      simpa only [map_add, Finsupp.degree_single] using hd
    apply weightBound_mono _ (weightBound_C_mul ((tails h.choose).coeff b.val) hrec)
    rw [map_add]
    omega
  · exact weightBound_monomial a
termination_by a.degree
decreasing_by exact replacement_degree_lt h.choose_spec (htails h.choose b.val b.property)

end Erdos1131.MonomialReduction


end
end PrivateSource_WeightedReduction


/- Source module ParametricWeights. -/
section PrivateSource_ParametricWeights

/-! The normalized-gradient tails have the required parameter-weight bounds. -/

noncomputable section

namespace Erdos1131

theorem parametricThreshold_coefficient_degree (k : ℕ) (a : Fin k →₀ ℕ) :
    ((parametricThreshold k).coeff a).natDegree ≤ 1 := by
  unfold parametricThreshold liftRationalCoefficients
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem reductionTails_coefficient_degree (k : ℕ) (i : Fin k) (a : Fin k →₀ ℕ) :
    ((reductionTails k i).coeff a).natDegree ≤ 1 := by
  unfold reductionTails
  rw [MvPolynomial.coeff_neg, Polynomial.natDegree_neg, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_pderiv]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply Polynomial.natDegree_mul_le.trans
  have hp := parametricThreshold_coefficient_degree k (a + Finsupp.single i 1)
  simpa using hp

theorem reductionTails_weightBound (k : ℕ) (i : Fin k) :
    MonomialReduction.WeightBound (clearedDegree k + 1) (reductionTails k i) := by
  intro a ha
  have hdegree : a.degree ≤ (reductionTails k i).totalDegree :=
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr ha)
  have htail : (reductionTails k i).totalDegree ≤ clearedDegree k - 1 := by
    simpa only [reductionTails, MvPolynomial.totalDegree_neg]
      using normalizedGradient_tail_totalDegree_le k i
  have hparameter := reductionTails_coefficient_degree k i a
  have hk : 0 < k := by
    have hi := i.isLt
    omega
  have hd : 0 < clearedDegree k := by
    unfold clearedDegree
    positivity
  omega

theorem normalized_normalMonomial_weightBound (k : ℕ) (a : Fin k →₀ ℕ) :
    MonomialReduction.WeightBound a.degree
      (MonomialReduction.normalMonomial (reductionTails k) (reductionTails_lower k) a) :=
  MonomialReduction.normalMonomial_weightBound _ _ (reductionTails_weightBound k) _

end Erdos1131


end
end PrivateSource_ParametricWeights


/- Source module QuotientCoordinates. -/
section PrivateSource_QuotientCoordinates

/-! Quotient coordinates are the coefficients of the unique reduced representative. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem quotientBasis_repr_mk {R : Type*} [CommRing R] {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (p : MvPolynomial (Fin k) R) (b : BoundedIndex k (m - 1)) :
    (quotientBasis hm tails htails).repr (Ideal.Quotient.mk (relationIdeal m tails) p) b =
      (normalForm tails htails p).coeff (boundedExponent b) := by
  classical
  have hlinear : (quotientBasis hm tails htails).coord b =
      (MvPolynomial.lcoeff R (boundedExponent b)).comp (quotientNormalForm tails htails) := by
    apply (quotientBasis hm tails htails).ext
    intro a
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [LinearMap.comp_apply,
      quotientBasis_apply, quotientMonomial, quotientNormalForm_mk,
      normalForm_boundedMonomial hm, MvPolynomial.lcoeff_apply, boundedMonomial_coeff]
    simp only [eq_comm]
  exact LinearMap.congr_fun hlinear (Ideal.Quotient.mk (relationIdeal m tails) p)

end Erdos1131.MonomialReduction


end
end PrivateSource_QuotientCoordinates


/- Source module TraceDegrees. -/
section PrivateSource_TraceDegrees

/-! Every parameter entry of the Hermite matrix has degree at most k times d. -/

open Module
open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem trace_monomial_eq_sum {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) :
    Algebra.trace ParameterRing (RelationQuotient m tails)
        (Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1)) =
      ∑ b : BoundedIndex k (m - 1),
        (normalMonomial tails htails (a + boundedExponent b)).coeff (boundedExponent b) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (quotientBasis hm tails htails), Matrix.trace]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, quotientBasis_apply,
    quotientMonomial, boundedMonomial, ← map_mul, MvPolynomial.monomial_mul_monomial,
    one_mul, quotientBasis_repr_mk, normalForm_monomial_one]

theorem trace_monomial_degree_le {k m : ℕ} (hm : 0 < m)
    (tails : Fin k → MvPolynomial (Fin k) ParameterRing) (htails : LowerDegree m tails)
    (hweight : ∀ i, WeightBound m (tails i)) (a : Fin k →₀ ℕ) :
    (Algebra.trace ParameterRing (RelationQuotient m tails)
      (Ideal.Quotient.mk (relationIdeal m tails) (MvPolynomial.monomial a 1))).natDegree ≤
        a.degree / 2 := by
  classical
  rw [trace_monomial_eq_sum hm tails htails]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b hb
  by_cases hz : (normalMonomial tails htails (a + boundedExponent b)).coeff (boundedExponent b) = 0
  · simp [hz]
  · have h := normalMonomial_weightBound tails htails hweight (a + boundedExponent b)
      (boundedExponent b) hz
    rw [map_add] at h
    omega

end Erdos1131.MonomialReduction

namespace Erdos1131

theorem boundedExponent_degree_le {k d : ℕ} (a : BoundedIndex k d) :
    (boundedExponent a).degree ≤ k * d := by
  rw [Finsupp.degree_eq_sum]
  calc
    ∑ i, boundedExponent a i ≤ ∑ _ : Fin k, d :=
      Finset.sum_le_sum (fun i _ => boundedExponent_le a i)
    _ = k * d := by simp

theorem parametricHermiteMatrix_entry_degree (k : ℕ)
    (a b : BoundedIndex k (clearedDegree k)) :
    (parametricHermiteMatrix k a b).natDegree ≤ k * clearedDegree k := by
  rw [parametricHermiteMatrix, MonomialReduction.hermiteMatrix_apply]
  have h := MonomialReduction.trace_monomial_degree_le
    (Nat.zero_lt_succ (clearedDegree k)) (reductionTails k) (reductionTails_lower k)
    (reductionTails_weightBound k) (boundedExponent a + boundedExponent b)
  have ha := boundedExponent_degree_le a
  have hb := boundedExponent_degree_le b
  rw [map_add] at h
  omega

end Erdos1131


end
end PrivateSource_TraceDegrees


/- Source module CoefficientDegrees. -/
section PrivateSource_CoefficientDegrees

/-! A parameter-degree bound for every characteristic coefficient. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def CoefficientDegreeBound (bound : ℕ) (p : Polynomial ParameterRing) : Prop :=
  ∀ j, (p.coeff j).natDegree ≤ bound

theorem coefficientDegreeBound_mono {a b : ℕ} {p : Polynomial ParameterRing}
    (hab : a ≤ b) (hp : CoefficientDegreeBound a p) : CoefficientDegreeBound b p :=
  fun j => (hp j).trans hab

theorem coefficientDegreeBound_zero (bound : ℕ) : CoefficientDegreeBound bound 0 := by
  intro j
  simp

theorem coefficientDegreeBound_C {bound : ℕ} (p : ParameterRing) (hp : p.natDegree ≤ bound) :
    CoefficientDegreeBound bound (Polynomial.C p) := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using hp
  · simp [Polynomial.coeff_C, hj]

theorem coefficientDegreeBound_X : CoefficientDegreeBound 0 Polynomial.X := by
  intro j
  simp only [Polynomial.coeff_X]
  split_ifs <;> simp

theorem coefficientDegreeBound_neg {bound : ℕ} {p : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound bound p) : CoefficientDegreeBound bound (-p) := by
  intro j
  simpa only [Polynomial.coeff_neg, Polynomial.natDegree_neg] using hp j

theorem coefficientDegreeBound_sub {bound : ℕ} {p q : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound bound p) (hq : CoefficientDegreeBound bound q) :
    CoefficientDegreeBound bound (p - q) := by
  intro j
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp j) (hq j))

theorem coefficientDegreeBound_sum {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ParameterRing) (bound : ℕ)
    (hp : ∀ i ∈ s, CoefficientDegreeBound bound (p i)) :
    CoefficientDegreeBound bound (∑ i ∈ s, p i) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact Polynomial.natDegree_sum_le_of_forall_le s (fun i => (p i).coeff j)
    (fun i hi => hp i hi j)

theorem coefficientDegreeBound_mul {a b : ℕ} {p q : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound a p) (hq : CoefficientDegreeBound b q) :
    CoefficientDegreeBound (a + b) (p * q) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c hc
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp c.fst) (hq c.snd))

theorem coefficientDegreeBound_prod {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ParameterRing) (bound : ℕ) :
    (∀ i ∈ s, CoefficientDegreeBound bound (p i)) →
      CoefficientDegreeBound (s.card * bound) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hp
    simpa only [Finset.prod_empty, Finset.card_empty, zero_mul, Polynomial.C_1]
      using coefficientDegreeBound_C (1 : ParameterRing) (by simp)
  | @insert i s hi ih =>
    intro hp
    rw [Finset.prod_insert hi]
    have hprod := coefficientDegreeBound_mul (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm] using hprod

theorem coefficientDegreeBound_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ParameterRing)) (bound : ℕ)
    (hM : ∀ i j, CoefficientDegreeBound bound (M i j)) :
    CoefficientDegreeBound (Fintype.card ι * bound) M.det := by
  classical
  rw [Matrix.det_apply]
  apply coefficientDegreeBound_sum
  intro σ hσ
  have hp := coefficientDegreeBound_prod Finset.univ (fun i => M (σ i) i) bound
    (fun i _ => hM (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul, Finset.card_univ] using hp
  · simpa only [hs, Units.neg_smul, one_smul, Finset.card_univ]
      using coefficientDegreeBound_neg hp

theorem characteristic_coefficient_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ParameterRing) (bound : ℕ) (hM : ∀ i j, (M i j).natDegree ≤ bound) (j : ℕ) :
    (M.charpoly.coeff j).natDegree ≤ Fintype.card ι * bound := by
  apply coefficientDegreeBound_det M.charmatrix bound _ j
  intro a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.charmatrix_apply_eq]
    exact coefficientDegreeBound_sub
      (coefficientDegreeBound_mono (Nat.zero_le bound) coefficientDegreeBound_X)
      (coefficientDegreeBound_C _ (hM a a))
  · rw [Matrix.charmatrix_apply_ne M a b hab]
    exact coefficientDegreeBound_neg (coefficientDegreeBound_C _ (hM a b))

theorem boundaryPolynomial_degree (k : ℕ) :
    (boundaryPolynomial k).natDegree ≤
      k * clearedDegree k * (clearedDegree k + 1) ^ k := by
  have h := characteristic_coefficient_degree (parametricHermiteMatrix k)
    (k * clearedDegree k) (parametricHermiteMatrix_entry_degree k) (boundaryIndex k)
  simpa only [boundaryPolynomial, hermiteCharacteristicPolynomial, card_boundedIndex,
    Nat.mul_comm] using h

end Erdos1131


end
end PrivateSource_CoefficientDegrees


/- Source module RootSelection. -/
section PrivateSource_RootSelection

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


end
end PrivateSource_RootSelection


/- Source module PolynomialEnergy. -/
section PrivateSource_PolynomialEnergy

/-! Finite coefficient coordinates for the interpolation energy. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

def coefficientPolynomial {n : ℕ} (c : Fin n → ℝ) : ℝ[X] :=
  ∑ j, Polynomial.monomial j.val (c j)

theorem coefficientPolynomial_eval {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    (coefficientPolynomial c).eval x = ∑ j, c j * x ^ j.val := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem coefficientPolynomial_coeff {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    (coefficientPolynomial c).coeff j.val = c j := by
  classical
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

theorem coefficientPolynomial_degree_lt {n : ℕ} (c : Fin n → ℝ) :
    (coefficientPolynomial c).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ n).mpr
  intro j hj
  classical
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : i.val ≠ j := by
    have := i.isLt
    omega
  simp [Polynomial.coeff_monomial, hne]

theorem coefficientPolynomial_of_polynomial {n : ℕ} (p : ℝ[X]) (hp : p.degree < n) :
    coefficientPolynomial (fun j : Fin n => p.coeff j.val) = p := by
  ext j
  by_cases hj : j < n
  · exact coefficientPolynomial_coeff _ ⟨j, hj⟩
  · have hjn : n ≤ j := by omega
    rw [(Polynomial.degree_lt_iff_coeff_zero _ n).mp
      (coefficientPolynomial_degree_lt _) j hjn,
      (Polynomial.degree_lt_iff_coeff_zero _ n).mp hp j hjn]

theorem coefficientPolynomial_ne_zero {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) :
    coefficientPolynomial c ≠ 0 := by
  intro hp
  apply hc
  funext j
  have h := congrArg (fun p : ℝ[X] => p.coeff j.val) hp
  simpa only [coefficientPolynomial_coeff, Polynomial.coeff_zero, Pi.zero_apply] using h

theorem continuous_coefficientPolynomial_eval (n : ℕ) :
    Continuous (fun z : (Fin n → ℝ) × ℝ => (coefficientPolynomial z.fst).eval z.snd) := by
  simp only [coefficientPolynomial_eval]
  fun_prop

def rowEnergy {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (coefficientPolynomial c).eval x ^ 2

theorem rowEnergy_nonneg {n : ℕ} (c : Fin n → ℝ) : 0 ≤ rowEnergy c := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  positivity

theorem rowEnergy_pos {n : ℕ} (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) :
    0 < rowEnergy c := by
  have href := referenceNodes_admissible hn
  have hnonzero := coefficientPolynomial_ne_zero hc
  have hex : ∃ j : Fin n, (coefficientPolynomial c).eval (referenceNodes n j) ≠ 0 := by
    by_contra! h
    apply hnonzero
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ href.1.injOn
    · simpa only [Finset.card_univ, Fintype.card_fin] using coefficientPolynomial_degree_lt c
    · simp
    · intro j hj
      simp [h j]
  obtain ⟨j, hj⟩ := hex
  change 0 < ∫ x in (-1 : ℝ)..1, (coefficientPolynomial c).eval x ^ 2
  apply intervalIntegral.integral_pos (by norm_num)
    ((coefficientPolynomial c).continuous.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · exact ⟨referenceNodes n j, href.2 j, sq_pos_of_ne_zero hj⟩

theorem rowEnergy_eq_moments {n : ℕ} (c : Fin n → ℝ) :
    rowEnergy c = ∑ j, ∑ l, c j * c l *
      (∫ x in (-1 : ℝ)..1, x ^ (j.val + l.val)) := by
  classical
  have hterm (j l : Fin n) (x : ℝ) :
      (c j * x ^ j.val) * (c l * x ^ l.val) = c j * c l * x ^ (j.val + l.val) := by
    rw [pow_add]
    ring
  have hint (j l : Fin n) : IntervalIntegrable
      (fun x : ℝ => c j * c l * x ^ (j.val + l.val)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hintSum (j : Fin n) : IntervalIntegrable
      (fun x : ℝ => ∑ l, c j * c l * x ^ (j.val + l.val)) volume (-1) 1 := by
    have hfun : (∑ l : Fin n, fun x : ℝ => c j * c l * x ^ (j.val + l.val)) =
        (fun x : ℝ => ∑ l, c j * c l * x ^ (j.val + l.val)) := by
      funext x
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum Finset.univ (fun l _ => hint j l)
  unfold rowEnergy
  simp_rw [coefficientPolynomial_eval, pow_two, Finset.sum_mul_sum, hterm]
  rw [intervalIntegral.integral_finsetSum
    (f := fun j x => ∑ l, c j * c l * x ^ (j.val + l.val)) (fun j _ => hintSum j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_finsetSum
    (f := fun l x => c j * c l * x ^ (j.val + l.val)) (fun l _ => hint j l)]
  simp only [intervalIntegral.integral_const_mul]

def coefficientEnergy {n : ℕ} (c : Fin n → Fin n → ℝ) : ℝ := ∑ i, rowEnergy (c i)

theorem coefficientEnergy_nonneg {n : ℕ} (c : Fin n → Fin n → ℝ) :
    0 ≤ coefficientEnergy c := Finset.sum_nonneg (fun i _ => rowEnergy_nonneg (c i))

theorem coefficientEnergy_pos {n : ℕ} (hn : 0 < n) {c : Fin n → Fin n → ℝ} (hc : c ≠ 0) :
    0 < coefficientEnergy c := by
  have hi : ∃ i, c i ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => rowEnergy_nonneg (c j))
    ⟨i, Finset.mem_univ i, rowEnergy_pos hn hi⟩

theorem continuous_coefficientEnergy (n : ℕ) :
    Continuous (coefficientEnergy (n := n)) := by
  unfold coefficientEnergy
  simp_rw [rowEnergy_eq_moments]
  fun_prop

theorem coefficientEnergy_smul {n : ℕ} (r : ℝ) (c : Fin n → Fin n → ℝ) :
    coefficientEnergy (r • c) = r ^ 2 * coefficientEnergy c := by
  unfold coefficientEnergy
  simp_rw [rowEnergy_eq_moments, Pi.smul_apply, smul_eq_mul]
  have hterm (i j l : Fin n) (a : ℝ) :
      r * c i j * (r * c i l) * a = r ^ 2 * (c i j * c i l * a) := by ring
  simp_rw [hterm, ← Finset.mul_sum]

end Erdos1131


end
end PrivateSource_PolynomialEnergy


/- Source module InterpolationStates. -/
section PrivateSource_InterpolationStates

/-! A closed coefficient-and-node description of admissible interpolation. -/

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section

namespace Erdos1131

abbrev InterpolationState (n : ℕ) := (Fin n → ℝ) × (Fin n → Fin n → ℝ)

def ValidInterpolationState {n : ℕ} (z : InterpolationState n) : Prop :=
  z.fst ∈ nodeBox n ∧ ∀ i j,
    (coefficientPolynomial (z.snd i)).eval (z.fst j) = if i = j then 1 else 0

theorem continuous_state_evaluation (n : ℕ) (i j : Fin n) :
    Continuous (fun z : InterpolationState n =>
      (coefficientPolynomial (z.snd i)).eval (z.fst j)) := by
  have hpair : Continuous (fun z : InterpolationState n => (z.snd i, z.fst j)) :=
    (((continuous_apply i).comp continuous_snd).prodMk
      ((continuous_apply j).comp continuous_fst))
  exact (continuous_coefficientPolynomial_eval n).comp hpair

theorem validInterpolationState_closed (n : ℕ) :
    IsClosed {z : InterpolationState n | ValidInterpolationState z} := by
  have hset : {z : InterpolationState n | ValidInterpolationState z} =
      (Prod.fst ⁻¹' nodeBox n) ∩ ⋂ i : Fin n, ⋂ j : Fin n, {z : InterpolationState n |
        (coefficientPolynomial (z.snd i)).eval (z.fst j) = if i = j then 1 else 0} := by
    ext z
    simp [ValidInterpolationState]
  rw [hset]
  apply IsClosed.inter ((isCompact_nodeBox n).isClosed.preimage continuous_fst)
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq (continuous_state_evaluation n i j) continuous_const

theorem validState_admissible {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) : Admissible z.fst := by
  constructor
  · intro i j hij
    by_contra hne
    have hself := hz.2 i i
    have hother := hz.2 i j
    rw [hij] at hself
    simp only [ite_eq_left, ite_eq_right hne] at hself hother
    linarith
  · intro i
    exact hz.1 i

theorem validState_polynomial {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) (i : Fin n) :
    coefficientPolynomial (z.snd i) = cardinalPolynomial z.fst i := by
  have hinj := (validState_admissible hz).1
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hinj.injOn
  · simpa only [Finset.card_univ, Fintype.card_fin] using coefficientPolynomial_degree_lt (z.snd i)
  · simpa only [Finset.card_univ, Fintype.card_fin] using cardinalPolynomial_degree_lt hinj i
  · intro j hj
    exact (hz.2 i j).trans (cardinal_at_node hinj i j).symm

theorem validState_energy {n : ℕ} {z : InterpolationState n}
    (hz : ValidInterpolationState z) : coefficientEnergy z.snd = energy z.fst := by
  unfold coefficientEnergy rowEnergy energy squareSum
  simp_rw [validState_polynomial hz]
  rw [intervalIntegral.integral_finsetSum
    (f := fun i x => cardinal z.fst i x ^ 2) (fun i _ =>
      ((cardinalPolynomial z.fst i).continuous.pow 2).intervalIntegrable _ _)]
  rfl

def stateOfNodes {n : ℕ} (nodes : Fin n → ℝ) : InterpolationState n :=
  (nodes, fun i j => (cardinalPolynomial nodes i).coeff j.val)

theorem stateOfNodes_valid {n : ℕ} {nodes : Fin n → ℝ} (h : Admissible nodes) :
    ValidInterpolationState (stateOfNodes nodes) := by
  constructor
  · intro i
    exact h.2 i
  · intro i j
    change (coefficientPolynomial (fun a : Fin n => (cardinalPolynomial nodes i).coeff a.val)).eval
      (nodes j) = if i = j then 1 else 0
    rw [coefficientPolynomial_of_polynomial _ (cardinalPolynomial_degree_lt h.1 i)]
    exact cardinal_at_node h.1 i j

theorem validStates_nonempty {n : ℕ} (hn : 0 < n) :
    Set.Nonempty {z : InterpolationState n | ValidInterpolationState z} :=
  ⟨stateOfNodes (referenceNodes n), stateOfNodes_valid (referenceNodes_admissible hn)⟩

end Erdos1131


end
end PrivateSource_InterpolationStates


/- Source module HomogeneousLowerBound. -/
section PrivateSource_HomogeneousLowerBound

/-! A positive homogeneous quadratic function controls the coefficient norm. -/

noncomputable section

namespace Erdos1131

theorem positive_homogeneous_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : E → ℝ) (hcontinuous : Continuous p)
    (hhom : ∀ r : ℝ, ∀ x, p (r • x) = r ^ 2 * p x)
    (hpos : ∀ x, x ≠ 0 → 0 < p x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ p x := by
  have hzero : p 0 = 0 := by
    simpa using hhom 0 (0 : E)
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
    refine ⟨1, by norm_num, ?_⟩
    intro x
    rw [Subsingleton.elim x 0, norm_zero, hzero]
    norm_num
  | inr hnontrivial =>
    letI : ProperSpace E := FiniteDimensional.proper ℝ E
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    have hnormz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hzunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp [norm_smul, norm_inv, hnormz]
    obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      ⟨_, hzunit⟩ hcontinuous.continuousOn
    have hyne : y ≠ 0 := by
      intro h
      simp [h] at hy
    refine ⟨p y, hpos y hyne, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, hzero]
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let u : E := ‖x‖⁻¹ • x
      have hu : u ∈ Metric.sphere (0 : E) 1 := by
        simp [u, norm_smul, norm_inv, hnorm]
      have hscale : ‖x‖ • u = x := by
        simp [u, smul_smul, hnorm]
      have hpx : p x = ‖x‖ ^ 2 * p u := by
        rw [← hscale, hhom]
        rw [hscale]
      rw [hpx, mul_comm (p y)]
      exact mul_le_mul_of_nonneg_left (hmin hu) (sq_nonneg ‖x‖)

end Erdos1131


end
end PrivateSource_HomogeneousLowerBound


/- Source module MinimumAttainment. -/
section PrivateSource_MinimumAttainment

/-! The original interpolation infimum is attained at distinct nodes. -/

noncomputable section

namespace Erdos1131

theorem coefficientEnergy_lower_bound {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin n → Fin n → ℝ, c * ‖v‖ ^ 2 ≤ coefficientEnergy v :=
  positive_homogeneous_lower_bound coefficientEnergy (continuous_coefficientEnergy n)
    coefficientEnergy_smul (fun v hv => coefficientEnergy_pos hn hv)

theorem minimum_validState_exists {n : ℕ} (hn : 0 < n) :
    ∃ z : InterpolationState n, ValidInterpolationState z ∧
      ∀ w : InterpolationState n, ValidInterpolationState w →
        coefficientEnergy z.snd ≤ coefficientEnergy w.snd := by
  obtain ⟨z₀, hz₀⟩ := validStates_nonempty hn
  obtain ⟨c, hc, hlower⟩ := coefficientEnergy_lower_bound hn
  let E₀ := coefficientEnergy z₀.snd
  let B := max ‖z₀.snd‖ (E₀ / c + 1)
  have hE₀ : 0 ≤ E₀ := coefficientEnergy_nonneg z₀.snd
  have hB : 0 ≤ B := (norm_nonneg z₀.snd).trans (le_max_left _ _)
  have hB₁ : 1 ≤ B := by
    have hratio : 0 ≤ E₀ / c := div_nonneg hE₀ hc.le
    have hmax := le_max_right ‖z₀.snd‖ (E₀ / c + 1)
    dsimp only [B]
    linarith
  have hstrict : E₀ < c * B ^ 2 := by
    have hratio : c * (E₀ / c) = E₀ := by field_simp [ne_of_gt hc]
    have hmax : E₀ / c + 1 ≤ B := le_max_right _ _
    have hCB := mul_le_mul_of_nonneg_left hmax hc.le
    have hsq : B ≤ B ^ 2 := by nlinarith
    have hCBsq := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  let K : Set (InterpolationState n) :=
    (nodeBox n ×ˢ Metric.closedBall 0 B) ∩ {z | ValidInterpolationState z}
  have hcompact : IsCompact K :=
    ((isCompact_nodeBox n).prod (isCompact_closedBall (0 : Fin n → Fin n → ℝ) B)).inter_right
      (validInterpolationState_closed n)
  have hz₀K : z₀ ∈ K := by
    refine ⟨⟨hz₀.1, ?_⟩, hz₀⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_left ‖z₀.snd‖ (E₀ / c + 1)
  obtain ⟨z, hzK, hzmin⟩ := hcompact.exists_isMinOn ⟨z₀, hz₀K⟩
    ((continuous_coefficientEnergy n).comp continuous_snd).continuousOn
  refine ⟨z, hzK.2, ?_⟩
  intro w hw
  by_cases hwK : w ∈ K
  · exact hzmin hwK
  · have hwBall : w.snd ∉ Metric.closedBall 0 B := by
      intro hball
      exact hwK ⟨⟨hw.1, hball⟩, hw⟩
    have hwNorm : B < ‖w.snd‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hwBall
    have hsq : B ^ 2 ≤ ‖w.snd‖ ^ 2 := by nlinarith [norm_nonneg w.snd]
    have hout : E₀ < coefficientEnergy w.snd :=
      hstrict.trans_le ((mul_le_mul_of_nonneg_left hsq hc.le).trans (hlower w.snd))
    exact (hzmin hz₀K).trans hout.le

theorem minimum_attained (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ, Admissible nodes ∧ energy nodes = minimum n := by
  obtain ⟨z, hz, hmin⟩ := minimum_validState_exists hn
  refine ⟨z.fst, validState_admissible hz, le_antisymm ?_ (minimum_le_energy (validState_admissible hz))⟩
  unfold minimum
  apply le_csInf (attainableValues_nonempty hn)
  rintro v ⟨nodes, hnodes, henergy⟩
  have h := hmin (stateOfNodes nodes) (stateOfNodes_valid hnodes)
  rw [validState_energy hz, validState_energy (stateOfNodes_valid hnodes)] at h
  simpa only [stateOfNodes, henergy] using h

end Erdos1131


end
end PrivateSource_MinimumAttainment


/- Source module CompleteSolution. -/
section PrivateSource_CompleteSolution

/-! The full exact-minimum conclusion for every positive number of nodes. -/

noncomputable section

namespace Erdos1131

/-- The root-selection formula is achieved and bounds every admissible configuration. -/
theorem erdos1131_solution (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ,
      Admissible nodes ∧
      energy nodes = algebraicMinimum n hn ∧
      ∀ other : Fin n → ℝ, Admissible other → algebraicMinimum n hn ≤ energy other := by
  obtain ⟨nodes, hnodes, henergy⟩ := minimum_attained n hn
  refine ⟨nodes, hnodes, henergy.trans (algebraicMinimum_eq_minimum n hn).symm, ?_⟩
  intro other hother
  rw [algebraicMinimum_eq_minimum n hn]
  exact minimum_le_energy hother

end Erdos1131


end
end PrivateSource_CompleteSolution


#print axioms Erdos1131.erdos1131_solution

#print axioms Erdos1131.algebraicMinimum_eq_minimum

#print axioms Erdos1131.minimum_attained

#print axioms Erdos1131.boundaryPolynomial_degree
