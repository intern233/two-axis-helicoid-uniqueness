import TwoAxisHelicoid.SlantedBasisReduction
import TwoAxisHelicoid.RectangularFixedLocus

namespace TwoAxisHelicoid
open Complex Set

/-- For an actual conjugation-invariant torus with primitive real period two,
connectedness of the fixed set forces the rhombic, not rectangular, lattice.
The remaining hypothesis is precisely the normalized real period marking. -/
theorem connected_conjugation_fixed_locus_forces_rhombic {t x : ℝ} (ht : 0 < t)
    (hL : ConjugationInvariantLattice (slantedPeriodPair x t ht))
    (hconn : IsPreconnected {q : PeriodTorus (slantedPeriodPair x t ht) |
      periodTorusConjugation (slantedPeriodPair x t ht) hL q = q}) :
    ∃ k : ℤ, x = 1+2*(k : ℝ) ∧
      (slantedPeriodPair x t ht).lattice = (rhombicPeriodPair t ht).lattice := by
  obtain ⟨n,rfl⟩ := slanted_conjugation_invariance_integer ht hL
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hpar with heven | hodd
  · have hn : n = 2*(n/2) := by omega
    have hx : (n : ℝ) = 2*((n/2 : ℤ) : ℝ) := by exact_mod_cast hn
    have hv : I*t ∈ (slantedPeriodPair (n : ℝ) t ht).lattice := by
      rw [hx]
      exact slanted_even_integer_has_vertical_period ht (n/2)
    exact False.elim (slanted_fixed_locus_not_preconnected_of_vertical_period ht hL hv hconn)
  · have hn : n = 1+2*(n/2) := by omega
    have hx : (n : ℝ) = 1+2*((n/2 : ℤ) : ℝ) := by exact_mod_cast hn
    refine ⟨n/2,hx,?_⟩
    rw [hx,slanted_lattice_even_shift ht 1 (n/2),slanted_one_lattice_eq_rhombic ht]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.connected_conjugation_fixed_locus_forces_rhombic
