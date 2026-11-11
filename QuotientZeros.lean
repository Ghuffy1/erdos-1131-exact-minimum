import TraceConstruction
import RealCharacters

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
