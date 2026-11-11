import QuotientZeros
import Mathlib.LinearAlgebra.Matrix.BilinearForm

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
