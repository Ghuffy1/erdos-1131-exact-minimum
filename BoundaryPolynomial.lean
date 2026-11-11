import TraceConstruction
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Roots

/-! The nonzero coefficient polynomial controlling exceptional parameters. -/

noncomputable section

namespace Erdos1131

def boundaryIndex (k : ℕ) : ℕ := (hermiteCharacteristicPolynomial k).natTrailingDegree

def boundaryPolynomial (k : ℕ) : Polynomial ℚ :=
  (hermiteCharacteristicPolynomial k).coeff (boundaryIndex k)

theorem boundaryPolynomial_ne_zero (k : ℕ) : boundaryPolynomial k ≠ 0 :=
  Polynomial.coeff_natTrailingDegree_ne_zero.mpr (hermiteCharacteristicPolynomial_monic k).ne_zero

theorem hermiteCharacteristicPolynomial_coeff_below (k j : ℕ) (hj : j < boundaryIndex k) :
    (hermiteCharacteristicPolynomial k).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj

theorem specialized_charpoly_coeff_boundary {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) :
    (specializedHermiteMatrix k φ).charpoly.coeff (boundaryIndex k) = φ (boundaryPolynomial k) := by
  rw [specializedHermiteMatrix_charpoly, Polynomial.coeff_map]
  rfl

theorem specialized_charpoly_coeff_below {S : Type*} [CommRing S]
    (k : ℕ) (φ : ParameterRing →+* S) (j : ℕ) (hj : j < boundaryIndex k) :
    (specializedHermiteMatrix k φ).charpoly.coeff j = 0 := by
  rw [specializedHermiteMatrix_charpoly, Polynomial.coeff_map,
    hermiteCharacteristicPolynomial_coeff_below k j hj, map_zero]

theorem specialized_charpoly_trailingDegree {S : Type*} [CommRing S] [Nontrivial S]
    (k : ℕ) (φ : ParameterRing →+* S) (hφ : φ (boundaryPolynomial k) ≠ 0) :
    (specializedHermiteMatrix k φ).charpoly.natTrailingDegree = boundaryIndex k := by
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rwa [specialized_charpoly_coeff_boundary]
  · apply Polynomial.le_natTrailingDegree (Matrix.charpoly_monic _).ne_zero
    intro j hj
    exact specialized_charpoly_coeff_below k φ j hj

def boundaryRoots (k : ℕ) : Set ℝ := (boundaryPolynomial k).rootSet ℝ

theorem boundaryRoots_finite (k : ℕ) : (boundaryRoots k).Finite :=
  Polynomial.rootSet_finite _ _

theorem mem_boundaryRoots (k : ℕ) (t : ℝ) :
    t ∈ boundaryRoots k ↔ specializeParameter t (boundaryPolynomial k) = 0 := by
  rw [boundaryRoots, Polynomial.mem_rootSet_of_ne (boundaryPolynomial_ne_zero k)]
  rfl

theorem charpoly_trailingDegree_off_boundary (k : ℕ) (t : ℝ) (ht : t ∉ boundaryRoots k) :
    (specializedHermiteMatrix k (specializeParameter t)).charpoly.natTrailingDegree =
      boundaryIndex k := by
  apply specialized_charpoly_trailingDegree
  exact (mem_boundaryRoots k t).not.mp ht

end Erdos1131
