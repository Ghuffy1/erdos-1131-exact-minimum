import QuadraticContinuity
import SymmetricNullity

/-! Constant nullity forces locally constant inertia in a continuous symmetric family. -/

open Filter
open scoped Topology Matrix

noncomputable section

namespace Erdos1131

theorem continuous_matrix_quadratic {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (M : X → Matrix ι ι ℝ)
    (hM : ∀ i j, Continuous (fun x => M x i j)) :
    Continuous (fun z : X × (ι → ℝ) => (M z.fst).toQuadraticForm' z.snd) := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
  fun_prop

theorem matrixSignature_eventually_constant {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] (M : X → Matrix ι ι ℝ)
    (hM : ∀ i j, Continuous (fun x => M x i j))
    (hsym : ∀ x, (M x).IsSymm) (x₀ : X)
    (hnull : ∀ᶠ x in 𝓝 x₀, (M x).charpoly.natTrailingDegree =
      (M x₀).charpoly.natTrailingDegree) :
    ∀ᶠ x in 𝓝 x₀, matrixSignature (M x) = matrixSignature (M x₀) := by
  have hcontinuous := continuous_matrix_quadratic M hM
  have hpos := sigPos_eventually_ge (fun x => (M x).toQuadraticForm') hcontinuous x₀
  have hneg := sigNeg_eventually_ge (fun x => (M x).toQuadraticForm') hcontinuous x₀
  filter_upwards [hpos, hneg, hnull] with x hpx hnx hnullx
  have hx := matrix_inertia_add_trailingDegree (M x) (hsym x)
  have hx₀ := matrix_inertia_add_trailingDegree (M x₀) (hsym x₀)
  have hp : sigPos (M x).toQuadraticForm' = sigPos (M x₀).toQuadraticForm' := by omega
  have hn : sigNeg (M x).toQuadraticForm' = sigNeg (M x₀).toQuadraticForm' := by omega
  simp only [matrixSignature, hp, hn]

end Erdos1131
