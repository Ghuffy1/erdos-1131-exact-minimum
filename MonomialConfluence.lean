import MonomialReduction

/-! Independence of the first chosen pure-power reduction. -/

open scoped BigOperators

noncomputable section

namespace Erdos1131.MonomialReduction

theorem expand_two_reductions {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ)
    (ih : ∀ b, b.degree < a.degree → ∀ i, m ≤ b i →
      normalMonomial tails htails b =
        normalForm tails htails (MvPolynomial.monomial (b - Finsupp.single i m) 1 * tails i))
    (i j : Fin k) (hi : m ≤ a i) (hj : m ≤ a j) (hij : i ≠ j) :
    normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) =
      ∑ b ∈ (tails i).support, ∑ c ∈ (tails j).support,
        MvPolynomial.C ((tails i).coeff b) * MvPolynomial.C ((tails j).coeff c) *
          normalMonomial tails htails (a - Finsupp.single i m - Finsupp.single j m + b + c) := by
  rw [normalForm_monomial_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have hsmall := replacement_degree_lt hi (htails i b hb)
  have hlarge := removed_coordinate_ge (b := b) hj hij
  rw [ih (a - Finsupp.single i m + b) hsmall j hlarge,
    subtract_after_add hj hij, normalForm_monomial_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem normalMonomial_rule {R : Type*} [CommRing R] {k m : ℕ}
    (tails : Fin k → MvPolynomial (Fin k) R) (htails : LowerDegree m tails)
    (a : Fin k →₀ ℕ) (i : Fin k) (hi : m ≤ a i) :
    normalMonomial tails htails a =
      normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) := by
  classical
  have h : ∃ j, m ≤ a j := ⟨i, hi⟩
  let j := h.choose
  have hj : m ≤ a j := h.choose_spec
  have hstep := normalMonomial_step tails htails a h
  change normalMonomial tails htails a =
    normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single j m) 1 * tails j) at hstep
  by_cases hij : i = j
  · rw [hij]
    exact hstep
  · have ih (b : Fin k →₀ ℕ) (hb : b.degree < a.degree) (index : Fin k) (hindex : m ≤ b index) :
        normalMonomial tails htails b =
          normalForm tails htails (MvPolynomial.monomial (b - Finsupp.single index m) 1 * tails index) :=
      normalMonomial_rule tails htails b index hindex
    calc
      normalMonomial tails htails a =
          normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single j m) 1 * tails j) := hstep
      _ = ∑ b ∈ (tails j).support, ∑ c ∈ (tails i).support,
          MvPolynomial.C ((tails j).coeff b) * MvPolynomial.C ((tails i).coeff c) *
            normalMonomial tails htails (a - Finsupp.single j m - Finsupp.single i m + b + c) :=
        expand_two_reductions tails htails a ih j i hj hi (Ne.symm hij)
      _ = ∑ c ∈ (tails i).support, ∑ b ∈ (tails j).support,
          MvPolynomial.C ((tails i).coeff c) * MvPolynomial.C ((tails j).coeff b) *
            normalMonomial tails htails (a - Finsupp.single i m - Finsupp.single j m + c + b) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro b hb
        rw [subtract_comm a j i]
        have hexponent : a - Finsupp.single i m - Finsupp.single j m + b + c =
            a - Finsupp.single i m - Finsupp.single j m + c + b :=
          add_right_comm _ b c
        rw [hexponent]
        ring
      _ = normalForm tails htails (MvPolynomial.monomial (a - Finsupp.single i m) 1 * tails i) :=
        (expand_two_reductions tails htails a ih i j hi hj hij).symm
termination_by a.degree
decreasing_by exact hb

end Erdos1131.MonomialReduction
