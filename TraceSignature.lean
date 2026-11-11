import TraceProduct
import RealTraceForm

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
