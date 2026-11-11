import HermiteSignature
import PolynomialDifferentiation

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
