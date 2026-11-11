import ReducedAlgebra
import ComplexTraceForm
import QuadraticProduct
import QuadraticSurjection

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
