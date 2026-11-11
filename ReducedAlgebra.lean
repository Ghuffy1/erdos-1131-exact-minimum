import TraceNilpotents
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.Complex.Polynomial.Basic

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
