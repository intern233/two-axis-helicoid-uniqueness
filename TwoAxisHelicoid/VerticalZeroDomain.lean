import TwoAxisHelicoid.VerticalBranchContinuity

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG verticalA

/-- A zero in the geometric unit interval itself forces the full allowed
height domain; no a priori upper bound on the height is assumed. -/
theorem thetaG_zero_height_domain {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hz : thetaG t a = 0) :
    t < ellipticVerticalUpper := by
  apply (existsUnique_thetaG_zero_full_domain ht).mp
  refine ⟨a,⟨ha,hz⟩,?_⟩
  intro b hb
  apply (thetaG_strictAnti_unit_of_pos ht).injOn hb.1 ha
  exact congrArg Complex.re (hb.2.trans hz.symm)

theorem thetaG_zero_iff_verticalA {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    thetaG t a = 0 ↔ t < ellipticVerticalUpper ∧ a = verticalA t := by
  constructor
  · intro hz
    have hdomain := thetaG_zero_height_domain ht ha hz
    exact ⟨hdomain,verticalA_unique ⟨ht,hdomain⟩ ha hz⟩
  · rintro ⟨hdom,rfl⟩
    exact (verticalA_spec ⟨ht,hdom⟩).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.thetaG_zero_iff_verticalA
