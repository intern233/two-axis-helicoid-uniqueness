import TwoAxisHelicoid.ConjugateLatticeRealBasis

namespace TwoAxisHelicoid
open Complex Set

/-- A conjugation-invariant genuine complex lattice admits a primitive positive
real period and a second generator with positive imaginary part. Both periods
are constructed from discreteness, rather than assumed as a marking. -/
theorem conjugation_lattice_real_basis (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) :
    ∃ (r : ℝ) (w : ℂ), 0 < r ∧ 0 < w.im ∧ (r : ℂ) ∈ L.lattice ∧ w ∈ L.lattice ∧
      ∀ z : ℂ, z ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ)*r+(n : ℂ)*w = z := by
  obtain ⟨r,hr,hrg⟩ := conjugation_lattice_has_real_generator L hL
  obtain ⟨t,ht,htg⟩ := conjugation_lattice_has_imaginary_generator L hL
  have hrmem : r ∈ latticeRealSubgroup L := by
    rw [← hrg]
    exact AddSubgroup.mem_zmultiples r
  have htmem : t ∈ latticeImaginarySubgroup L := by
    rw [← htg]
    exact AddSubgroup.mem_zmultiples t
  obtain ⟨w,hw,hwi⟩ := htmem
  refine ⟨r,w,hr,by simpa [hwi] using ht,hrmem,hw,?_⟩
  intro z
  constructor
  · intro hz
    have hzi : z.im ∈ AddSubgroup.zmultiples t := by
      rw [htg]
      exact ⟨z,hz,rfl⟩
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hzi
    have hrem : z-(n : ℂ)*w ∈ L.lattice :=
      L.lattice.sub_mem hz (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hw)
    have hremi : (z-(n : ℂ)*w).im = 0 := by
      simp only [Complex.sub_im,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,
        zero_mul,add_zero,hwi]
      simpa only [zsmul_eq_mul,sub_eq_zero] using hn.symm
    have hre : ((z-(n : ℂ)*w).re : ℂ) = z-(n : ℂ)*w := by
      apply Complex.ext <;> simp [hremi]
    have hrr : (z-(n : ℂ)*w).re ∈ AddSubgroup.zmultiples r := by
      rw [hrg]
      change ((z-(n : ℂ)*w).re : ℂ) ∈ L.lattice
      rwa [hre]
    obtain ⟨m,hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hrr
    refine ⟨m,n,?_⟩
    have hmc : (m : ℂ)*r = ((z-(n : ℂ)*w).re : ℂ) := by
      exact_mod_cast (show (m : ℝ)*r = (z-(n : ℂ)*w).re by simpa only [zsmul_eq_mul] using hm)
    rw [hmc,hre]
    ring
  · rintro ⟨m,n,rfl⟩
    exact L.lattice.add_mem
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hrmem)
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hw)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conjugation_lattice_real_basis
