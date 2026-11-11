import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic

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
