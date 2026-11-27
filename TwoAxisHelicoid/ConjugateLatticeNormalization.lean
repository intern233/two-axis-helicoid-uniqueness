import TwoAxisHelicoid.ConjugateLatticeBasis
import TwoAxisHelicoid.PeriodTorusScaling
import TwoAxisHelicoid.RhombicMarkingCriterion

namespace TwoAxisHelicoid
open Complex Set

/-- Conjugation invariance alone supplies the real marking needed for the
classification of connected real complex tori. -/
theorem conjugation_lattice_slanted_normalization (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) :
    ∃ (c x t : ℝ) (_hc : 0 < c) (ht : 0 < t),
      ∀ z : ℂ, z ∈ L.lattice ↔ (c : ℂ)*z ∈ (slantedPeriodPair x t ht).lattice := by
  obtain ⟨r,w,hr,hwi,_,_,hbasis⟩ := conjugation_lattice_real_basis L hL
  let c : ℝ := 2/r
  have hc : 0 < c := div_pos (by norm_num) hr
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have ht : 0 < c*w.im := mul_pos hc hwi
  have hcr : (c : ℂ)*(r : ℂ) = 2 := by
    exact_mod_cast (show c*r = 2 by dsimp [c]; field_simp)
  have hcw : (c : ℂ)*w = ((c*w.re : ℝ) : ℂ)+I*((c*w.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  refine ⟨c,c*w.re,c*w.im,hc,ht,?_⟩
  intro z
  rw [hbasis,PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    change (m : ℂ)*2+(n : ℂ)*(((c*w.re : ℝ) : ℂ)+I*((c*w.im : ℝ) : ℂ)) = (c : ℂ)*z
    rw [← hcr,← hcw,← he]
    ring
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    apply mul_left_cancel₀ hcC
    change (m : ℂ)*2+(n : ℂ)*(((c*w.re : ℝ) : ℂ)+I*((c*w.im : ℝ) : ℂ)) = (c : ℂ)*z at he
    rw [← hcr,← hcw] at he
    convert he using 1
    ring

/-- For any actual conjugation-invariant complex lattice, connectedness of the
conjugation fixed set forces a positive real scaling to the rhombic lattice.
No pre-existing real period marking is required. -/
theorem conjugation_connected_torus_rhombic_normalization (L : PeriodPair)
    (hL : ConjugationInvariantLattice L)
    (hconn : IsPreconnected {q : PeriodTorus L | periodTorusConjugation L hL q = q}) :
    ∃ (c t : ℝ) (_hc : 0 < c) (ht : 0 < t),
      ∀ z : ℂ, z ∈ L.lattice ↔ (c : ℂ)*z ∈ (rhombicPeriodPair t ht).lattice := by
  obtain ⟨c,x,t,hc,ht,hp⟩ := conjugation_lattice_slanted_normalization L hL
  have hM := real_scaling_conjugation_invariant L (slantedPeriodPair x t ht) hc.ne' hp hL
  have hconnM := real_scaling_fixed_locus_preconnected L (slantedPeriodPair x t ht)
    hc.ne' hp hL hM hconn
  obtain ⟨_,_,he⟩ := connected_conjugation_fixed_locus_forces_rhombic ht hM hconnM
  refine ⟨c,t,hc,ht,?_⟩
  intro z
  rw [← he]
  exact hp z

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conjugation_connected_torus_rhombic_normalization
