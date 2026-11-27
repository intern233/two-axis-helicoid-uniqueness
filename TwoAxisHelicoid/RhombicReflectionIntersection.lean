import TwoAxisHelicoid.RhombicFixedLoci

namespace TwoAxisHelicoid
open Complex Set

theorem rhombic_reflections_common_fixed_points {t : ℝ} (ht : 0 < t)
    (q : PeriodTorus (rhombicPeriodPair t ht)) :
    (rhombicHorizontalReflection ht q = q ∧ rhombicVerticalReflection ht q = q) ↔
      q = 0 ∨ q = periodTorusProjection (rhombicPeriodPair t ht) 1 := by
  constructor
  · rintro ⟨hh,hv⟩
    obtain ⟨x,rfl⟩ := (rhombic_horizontal_fixed_iff_real ht q).mp hh
    obtain ⟨n,hn⟩ := (rhombic_vertical_fixed_projection_iff ht (x : ℂ)).mp hv
    change x = (n : ℝ) at hn
    subst x
    have hp : n%2 = 0 ∨ n%2 = 1 := by omega
    rcases hp with he | ho
    · left
      apply (periodTorusProjection_eq_zero _ _).mpr
      apply (rhombic_mem_lattice_iff ht _).mpr
      refine ⟨n/2,0,?_,by simp⟩
      norm_cast
      omega
    · right
      apply (periodTorusProjection_eq_iff _ _ _).mpr
      apply (rhombic_mem_lattice_iff ht _).mpr
      refine ⟨-(n/2),0,?_,by simp⟩
      simp only [Complex.sub_re,Complex.one_re,Complex.ofReal_re,Int.cast_neg,Int.cast_zero,add_zero]
      have hn : 1-n = 2*(-(n/2)) := by omega
      exact_mod_cast hn
  · rintro (rfl | rfl)
    · change rhombicHorizontalReflection ht (periodTorusProjection _ 0) = periodTorusProjection _ 0 ∧
        rhombicVerticalReflection ht (periodTorusProjection _ 0) = periodTorusProjection _ 0
      simp
    · constructor
      · rw [rhombicHorizontalReflection_projection]
        simp
      · apply (rhombic_vertical_fixed_projection_iff ht 1).mpr
        exact ⟨1,by simp⟩

theorem rhombic_common_fixed_points_distinct {t : ℝ} (ht : 0 < t) :
    periodTorusProjection (rhombicPeriodPair t ht) 1 ≠ 0 := by
  apply (periodTorusProjection_eq_zero _ _).not.mpr
  simpa [rhombicPeriodPair] using (rhombicPeriodPair t ht).ω₁_div_two_notMem_lattice

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_reflections_common_fixed_points
