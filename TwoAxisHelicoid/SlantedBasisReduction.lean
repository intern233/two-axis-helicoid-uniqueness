import TwoAxisHelicoid.SlantedLattice
import TwoAxisHelicoid.RhombicRegularPaths

namespace TwoAxisHelicoid
open Complex Set

theorem slanted_lattice_even_shift {t : ℝ} (ht : 0 < t) (x : ℝ) (k : ℤ) :
    (slantedPeriodPair (x+2*(k : ℝ)) t ht).lattice = (slantedPeriodPair x t ht).lattice := by
  ext z
  rw [slanted_mem_lattice_iff ht,slanted_mem_lattice_iff ht]
  constructor
  · rintro ⟨m,n,hr,hi⟩
    refine ⟨m+n*k,n,?_,hi⟩
    rw [hr]
    push_cast
    ring
  · rintro ⟨m,n,hr,hi⟩
    refine ⟨m-n*k,n,?_,hi⟩
    rw [hr]
    push_cast
    ring

theorem slanted_one_lattice_eq_rhombic {t : ℝ} (ht : 0 < t) :
    (slantedPeriodPair 1 t ht).lattice = (rhombicPeriodPair t ht).lattice := by
  ext z
  rw [slanted_mem_lattice_iff ht,rhombic_mem_lattice_iff ht]
  simp only [mul_one]

theorem slanted_even_integer_has_vertical_period {t : ℝ} (ht : 0 < t) (k : ℤ) :
    I*t ∈ (slantedPeriodPair (2*(k : ℝ)) t ht).lattice := by
  apply PeriodPair.mem_lattice.mpr
  refine ⟨-k,1,?_⟩
  simp only [slantedPeriodPair,Int.cast_neg,Int.cast_one,one_mul]
  push_cast
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.slanted_lattice_even_shift
