import TraceSignature

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
