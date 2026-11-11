import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

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
