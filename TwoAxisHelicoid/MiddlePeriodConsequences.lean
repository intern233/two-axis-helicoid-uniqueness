import TwoAxisHelicoid.FullPeriodRoot

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG thetaHorizontalPeriod actualPeriodAlong

theorem middle_height_in_full_domain {t : ℝ}
    (ht : t ∈ Icc (17/20 : ℝ) (9/10)) :
    t ∈ Ioo (0 : ℝ) ellipticVerticalUpper := by
  refine ⟨lt_of_lt_of_le (by norm_num) ht.1,?_⟩
  exact lt_of_le_of_lt ht.2 (lt_trans (by norm_num) ellipticVerticalUpper_location.1)

theorem root_height_in_middle {t : ℝ}
    (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) :
    t ∈ Icc (17/20 : ℝ) (9/10) := by
  constructor
  · exact le_trans (by norm_num [rootTLower]) ht.1.le
  · exact le_trans ht.2.le (by norm_num [rootTUpper])

/-- Analytic consequence used after the separate kernel-checked certificate
has supplied its derivative bound on the whole closed middle interval. -/
theorem actualPeriodAlong_strictAntiOn_middle_of_deriv_neg
    (hderiv : ∀ t ∈ Icc (17/20 : ℝ) (9/10), deriv actualPeriodAlong t < 0) :
    StrictAntiOn actualPeriodAlong (Icc (17/20 : ℝ) (9/10)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (actualPeriodAlong_continuousOn.mono (fun _ ht => middle_height_in_full_domain ht))
  intro t ht
  have hti : t ∈ Ioo (17/20 : ℝ) (9/10) := by simpa only [interior_Icc] using ht
  exact hderiv t ⟨hti.1.le,hti.2.le⟩

theorem existsUnique_actualPeriodAlong_root_middle_of_strictAnti
    (hmono : StrictAntiOn actualPeriodAlong (Icc (17/20 : ℝ) (9/10))) :
    ∃! t : ℝ, t ∈ Icc (17/20 : ℝ) (9/10) ∧ actualPeriodAlong t = 0 := by
  obtain ⟨t,ht,_⟩ := existsUnique_actualPeriodAlong_root_locally
  refine ⟨t,⟨root_height_in_middle ht.1,ht.2⟩,?_⟩
  intro s hs
  exact hmono.injOn hs.1 (root_height_in_middle ht.1) (hs.2.trans ht.2.symm)

theorem existsUnique_common_period_middle_of_strictAnti
    (hmono : StrictAntiOn actualPeriodAlong (Icc (17/20 : ℝ) (9/10))) :
    ∃! p : ℝ × ℝ, p.1 ∈ Icc (17/20 : ℝ) (9/10) ∧
      p.2 ∈ Ioo (0 : ℝ) 1 ∧ thetaG p.1 p.2 = 0 ∧ thetaHorizontalPeriod p.1 p.2 = 0 := by
  obtain ⟨t,ht,hu⟩ := existsUnique_actualPeriodAlong_root_middle_of_strictAnti hmono
  have ha := verticalA_spec (middle_height_in_full_domain ht.1)
  refine ⟨(t,verticalA t),⟨ht.1,ha.1,ha.2,?_⟩,?_⟩
  · simpa only [actualPeriodAlong] using ht.2
  intro p hp
  have hpa : p.2 = verticalA p.1 :=
    verticalA_unique (middle_height_in_full_domain hp.1) hp.2.1 hp.2.2.1
  have hzero : actualPeriodAlong p.1 = 0 := by
    unfold actualPeriodAlong
    rw [← hpa]
    exact hp.2.2.2
  have hpt := hu p.1 ⟨hp.1,hzero⟩
  exact Prod.ext hpt (hpa.trans (congrArg verticalA hpt))

theorem actualPeriodAlong_middle_root_location_of_strictAnti
    (hmono : StrictAntiOn actualPeriodAlong (Icc (17/20 : ℝ) (9/10)))
    {t : ℝ} (ht : t ∈ Icc (17/20 : ℝ) (9/10)) (hz : actualPeriodAlong t = 0) :
    t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      verticalA t ∈ Ioo (rootALower : ℝ) rootAUpper ∧ deriv actualPeriodAlong t < -8 := by
  obtain ⟨s,_,hs,ha,hzero,hd⟩ := exists_actualPeriodAlong_certified_simple_zero
  have he : t = s := hmono.injOn ht (root_height_in_middle hs) (hz.trans hzero.symm)
  subst t
  exact ⟨hs,ha,hd⟩

theorem actualPeriodAlong_middle_endpoint_signs_of_strictAnti
    (hmono : StrictAntiOn actualPeriodAlong (Icc (17/20 : ℝ) (9/10))) :
    0 < actualPeriodAlong (17/20) ∧ actualPeriodAlong (9/10) < 0 := by
  obtain ⟨t,ht,_⟩ := existsUnique_actualPeriodAlong_root_locally
  have htm := root_height_in_middle ht.1
  have hl : (17/20 : ℝ) < t := lt_trans (by norm_num [rootTLower]) ht.1.1
  have hu : t < (9/10 : ℝ) := lt_trans ht.1.2 (by norm_num [rootTUpper])
  have hleft := hmono (by norm_num : (17/20 : ℝ) ∈ Icc (17/20) (9/10)) htm hl
  have hright := hmono htm (by norm_num : (9/10 : ℝ) ∈ Icc (17/20) (9/10)) hu
  simpa only [ht.2] using And.intro hleft hright

end TwoAxisHelicoid
