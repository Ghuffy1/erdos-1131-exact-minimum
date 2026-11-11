import TraceDegrees
import BoundaryPolynomial

/-! A parameter-degree bound for every characteristic coefficient. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131

def CoefficientDegreeBound (bound : ℕ) (p : Polynomial ParameterRing) : Prop :=
  ∀ j, (p.coeff j).natDegree ≤ bound

theorem coefficientDegreeBound_mono {a b : ℕ} {p : Polynomial ParameterRing}
    (hab : a ≤ b) (hp : CoefficientDegreeBound a p) : CoefficientDegreeBound b p :=
  fun j => (hp j).trans hab

theorem coefficientDegreeBound_zero (bound : ℕ) : CoefficientDegreeBound bound 0 := by
  intro j
  simp

theorem coefficientDegreeBound_C {bound : ℕ} (p : ParameterRing) (hp : p.natDegree ≤ bound) :
    CoefficientDegreeBound bound (Polynomial.C p) := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using hp
  · simp [Polynomial.coeff_C, hj]

theorem coefficientDegreeBound_X : CoefficientDegreeBound 0 Polynomial.X := by
  intro j
  simp only [Polynomial.coeff_X]
  split_ifs <;> simp

theorem coefficientDegreeBound_neg {bound : ℕ} {p : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound bound p) : CoefficientDegreeBound bound (-p) := by
  intro j
  simpa only [Polynomial.coeff_neg, Polynomial.natDegree_neg] using hp j

theorem coefficientDegreeBound_sub {bound : ℕ} {p q : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound bound p) (hq : CoefficientDegreeBound bound q) :
    CoefficientDegreeBound bound (p - q) := by
  intro j
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp j) (hq j))

theorem coefficientDegreeBound_sum {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ParameterRing) (bound : ℕ)
    (hp : ∀ i ∈ s, CoefficientDegreeBound bound (p i)) :
    CoefficientDegreeBound bound (∑ i ∈ s, p i) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact Polynomial.natDegree_sum_le_of_forall_le s (fun i => (p i).coeff j)
    (fun i hi => hp i hi j)

theorem coefficientDegreeBound_mul {a b : ℕ} {p q : Polynomial ParameterRing}
    (hp : CoefficientDegreeBound a p) (hq : CoefficientDegreeBound b q) :
    CoefficientDegreeBound (a + b) (p * q) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c hc
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp c.fst) (hq c.snd))

theorem coefficientDegreeBound_prod {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ParameterRing) (bound : ℕ) :
    (∀ i ∈ s, CoefficientDegreeBound bound (p i)) →
      CoefficientDegreeBound (s.card * bound) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hp
    simpa only [Finset.prod_empty, Finset.card_empty, zero_mul, Polynomial.C_1]
      using coefficientDegreeBound_C (1 : ParameterRing) (by simp)
  | @insert i s hi ih =>
    intro hp
    rw [Finset.prod_insert hi]
    have hprod := coefficientDegreeBound_mul (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm] using hprod

theorem coefficientDegreeBound_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ParameterRing)) (bound : ℕ)
    (hM : ∀ i j, CoefficientDegreeBound bound (M i j)) :
    CoefficientDegreeBound (Fintype.card ι * bound) M.det := by
  classical
  rw [Matrix.det_apply]
  apply coefficientDegreeBound_sum
  intro σ hσ
  have hp := coefficientDegreeBound_prod Finset.univ (fun i => M (σ i) i) bound
    (fun i _ => hM (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul, Finset.card_univ] using hp
  · simpa only [hs, Units.neg_smul, one_smul, Finset.card_univ]
      using coefficientDegreeBound_neg hp

theorem characteristic_coefficient_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ParameterRing) (bound : ℕ) (hM : ∀ i j, (M i j).natDegree ≤ bound) (j : ℕ) :
    (M.charpoly.coeff j).natDegree ≤ Fintype.card ι * bound := by
  apply coefficientDegreeBound_det M.charmatrix bound _ j
  intro a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.charmatrix_apply_eq]
    exact coefficientDegreeBound_sub
      (coefficientDegreeBound_mono (Nat.zero_le bound) coefficientDegreeBound_X)
      (coefficientDegreeBound_C _ (hM a a))
  · rw [Matrix.charmatrix_apply_ne M a b hab]
    exact coefficientDegreeBound_neg (coefficientDegreeBound_C _ (hM a b))

theorem boundaryPolynomial_degree (k : ℕ) :
    (boundaryPolynomial k).natDegree ≤
      k * clearedDegree k * (clearedDegree k + 1) ^ k := by
  have h := characteristic_coefficient_degree (parametricHermiteMatrix k)
    (k * clearedDegree k) (parametricHermiteMatrix_entry_degree k) (boundaryIndex k)
  simpa only [boundaryPolynomial, hermiteCharacteristicPolynomial, card_boundedIndex,
    Nat.mul_comm] using h

end Erdos1131
