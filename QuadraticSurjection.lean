import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

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
