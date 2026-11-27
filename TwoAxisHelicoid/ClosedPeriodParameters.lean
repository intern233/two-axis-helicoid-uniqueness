import TwoAxisHelicoid.RootCommonPeriod

namespace TwoAxisHelicoid
open Set

/-- Parameters of the actual two-period problem, with no numerical or sign
assumptions beyond the equations themselves. -/
structure ClosedPeriodParameters where
  t : ℝ
  a : ℝ
  height_pos : 0 < t
  abscissa_mem : a ∈ Ioo (0 : ℝ) 1
  vertical_closed : thetaG t a = 0
  horizontal_closed : thetaHorizontalPeriod t a = 0

theorem exists_certified_closed_parameters :
    ∃ p : ClosedPeriodParameters, p.t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      p.a ∈ Ioo (rootALower : ℝ) rootAUpper := by
  obtain ⟨t,a,ht,ha,hG,hH⟩ := exists_root_common_period_zero
  have ht0 : 0 < t := (by norm_num [rootTLower] : (0 : ℝ) < rootTLower).trans ht.1
  have ha01 : a ∈ Ioo (0 : ℝ) 1 :=
    ⟨(by norm_num [rootALower] : (0 : ℝ) < rootALower).trans ha.1,
      ha.2.trans (by norm_num [rootAUpper] : (rootAUpper : ℝ) < 1)⟩
  exact ⟨⟨t,a,ht0,ha01,hG,hH⟩,ht,ha⟩

noncomputable def certifiedClosedParameters : ClosedPeriodParameters :=
  Classical.choose exists_certified_closed_parameters

theorem certifiedClosedParameters_bounds :
    certifiedClosedParameters.t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      certifiedClosedParameters.a ∈ Ioo (rootALower : ℝ) rootAUpper :=
  Classical.choose_spec exists_certified_closed_parameters

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certifiedClosedParameters
