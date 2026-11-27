import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

noncomputable def slantedPeriodPair (x t : ℝ) (ht : 0 < t) : PeriodPair where
  ω₁ := 2
  ω₂ := x+I*t
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp [Complex.real_smul,Complex.mul_re,Complex.mul_im] at hi hr
    have hb : b = 0 := hi.resolve_right ht.ne'
    refine ⟨?_,hb⟩
    rw [hb] at hr
    linarith

noncomputable def rectangularPeriodPair (t : ℝ) (ht : 0 < t) : PeriodPair := slantedPeriodPair 0 t ht

theorem slanted_mem_lattice_iff {t : ℝ} (ht : 0 < t) (x : ℝ) (z : ℂ) :
    z ∈ (slantedPeriodPair x t ht).lattice ↔
      ∃ m n : ℤ, z.re = 2*m+n*x ∧ z.im = n*t := by
  constructor
  · intro h
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp h
    refine ⟨m,n,?_,?_⟩ <;> rw [← he]
    · simp [slantedPeriodPair,Complex.mul_re]
      ring
    · simp [slantedPeriodPair,Complex.mul_im]
  · rintro ⟨m,n,hr,hi⟩
    apply PeriodPair.mem_lattice.mpr
    refine ⟨m,n,?_⟩
    apply Complex.ext
    · simp [slantedPeriodPair,Complex.mul_re,hr]
      ring
    · simp [slantedPeriodPair,Complex.mul_im,hi]

/-- Once a real primitive period is normalized to two, conjugation invariance
forces the other generator's real part to be an integer. -/
theorem slanted_conjugation_invariance_integer {t x : ℝ} (ht : 0 < t)
    (hL : ConjugationInvariantLattice (slantedPeriodPair x t ht)) :
    ∃ n : ℤ, x = (n : ℝ) := by
  have h := hL _ (slantedPeriodPair x t ht).ω₂_mem_lattice
  obtain ⟨m,n,hr,hi⟩ := (slanted_mem_lattice_iff ht x _).mp h
  change (conj ((x : ℂ)+I*t)).re = 2*m+n*x at hr
  change (conj ((x : ℂ)+I*t)).im = n*t at hi
  simp [Complex.mul_re,Complex.mul_im] at hr hi
  have hn : (n : ℝ) = -1 := by nlinarith
  refine ⟨m,?_⟩
  rw [hn] at hr
  linarith

theorem rectangular_conjugation_invariant {t : ℝ} (ht : 0 < t) :
    ConjugationInvariantLattice (rectangularPeriodPair t ht) := by
  intro z hz
  obtain ⟨m,n,hr,hi⟩ := (slanted_mem_lattice_iff ht 0 z).mp hz
  apply (slanted_mem_lattice_iff ht 0 (conj z)).mpr
  refine ⟨m,-n,?_,?_⟩
  · simpa using hr
  · simp only [Complex.conj_im,Int.cast_neg,neg_mul]
    exact congrArg Neg.neg hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.slanted_conjugation_invariance_integer
