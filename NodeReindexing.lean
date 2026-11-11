import Erdos1131
import Mathlib.Data.Finset.Sort

/-! Permuting nodes preserves the original objective. -/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Erdos1131

theorem cardinalPolynomial_degree_lt {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (i : Fin n) :
    (cardinalPolynomial nodes i).degree < n := by
  rw [cardinalPolynomial, Lagrange.degree_basis hinj.injOn (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot, WithBot.coe_lt_coe]
  have hi := i.isLt
  omega

theorem cardinalPolynomial_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    cardinalPolynomial (nodes ∘ e) i = cardinalPolynomial nodes (e i) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (hinj.comp e.injective).injOn
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      cardinalPolynomial_degree_lt (hinj.comp e.injective) i
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      cardinalPolynomial_degree_lt hinj (e i)
  · intro j hj
    change cardinal (nodes ∘ e) i ((nodes ∘ e) j) = cardinal nodes (e i) (nodes (e j))
    rw [cardinal_at_node (hinj.comp e.injective), cardinal_at_node hinj]
    simp only [e.injective.eq_iff]

theorem squareSum_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) (x : ℝ) :
    squareSum (nodes ∘ e) x = squareSum nodes x := by
  simp only [squareSum, cardinal, cardinalPolynomial_reindex hinj e]
  exact Equiv.sum_comp e (fun i => (cardinalPolynomial nodes i).eval x ^ 2)

theorem energy_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) (e : Equiv.Perm (Fin n)) :
    energy (nodes ∘ e) = energy nodes := by
  unfold energy
  simp_rw [squareSum_reindex hinj e]

theorem admissible_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (h : Admissible nodes) (e : Equiv.Perm (Fin n)) : Admissible (nodes ∘ e) :=
  ⟨h.1.comp e.injective, fun i => h.2 (e i)⟩

theorem exists_strictMono_reindex {n : ℕ} {nodes : Fin n → ℝ}
    (hinj : Function.Injective nodes) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (nodes ∘ e) := by
  classical
  let s := Finset.univ.image nodes
  have hcard : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let f : Fin n → s := fun i => ⟨nodes i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hinj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hix⟩
  let original : Fin n ≃ s := Equiv.ofBijective f hf
  let sorted : Fin n ≃o s := s.orderIsoOfFin hcard
  let e : Equiv.Perm (Fin n) := sorted.toEquiv.trans original.symm
  have hvalues (i : Fin n) : nodes (e i) = (sorted i).val := by
    change nodes (original.symm (sorted i)) = (sorted i).val
    exact congrArg Subtype.val (original.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  change nodes (e i) < nodes (e j)
  rw [hvalues i, hvalues j]
  exact sorted.strictMono hij

end Erdos1131
