import TwoAxisHelicoid.RhombicLattice

namespace TwoAxisHelicoid
open Complex

theorem rhombic_mem_lattice_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    z ∈ (rhombicPeriodPair t ht).lattice ↔
      ∃ m n : ℤ, z.re = 2*m+n ∧ z.im = n*t := by
  constructor
  · intro hz
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hz
    refine ⟨m,n,?_,?_⟩ <;> rw [← he]
    · simp [rhombicPeriodPair,Complex.mul_re]
      ring
    · simp [rhombicPeriodPair,Complex.mul_im]
  · rintro ⟨m,n,hr,hi⟩
    apply PeriodPair.mem_lattice.mpr
    refine ⟨m,n,?_⟩
    apply Complex.ext
    · simp [rhombicPeriodPair,Complex.mul_re,hr]
      ring
    · simp [rhombicPeriodPair,Complex.mul_im,hi]

theorem rhombic_midline_not_mem {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (x:ℂ)+I*((t/2:ℝ):ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,_,hi⟩ := (rhombic_mem_lattice_iff ht _).mp hz
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add] at hi
  have hn : (n:ℝ) = 1/2 := by nlinarith
  have hn0 : (0:ℤ) < n := by exact_mod_cast (show (0:ℝ) < n by linarith)
  have hn1 : n < (1:ℤ) := by exact_mod_cast (show (n:ℝ) < 1 by linarith)
  omega

theorem rhombic_sloping_line_not_mem {t : ℝ} (ht : 0 < t) (s : ℝ) :
    (-1:ℂ)+(s:ℂ)*(1+I*t) ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp hz
  norm_num [Complex.mul_re,Complex.mul_im] at hr hi
  have hn : (n:ℝ) = s := (hi.resolve_right ht.ne').symm
  have hm : (2:ℤ)*m = -1 := by exact_mod_cast (show (2:ℝ)*m = -1 by linarith)
  omega

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_sloping_line_not_mem
