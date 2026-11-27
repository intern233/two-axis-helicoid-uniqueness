import TwoAxisHelicoid.RightDerivativeLimit
import TwoAxisHelicoid.RightEndpointCertificate

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

noncomputable def rightExtendedPeriod : ℝ → ℝ :=
  Function.update actualPeriodAlong ellipticVerticalUpper (-Real.pi/ellipticVerticalUpper)

theorem rightExtendedPeriod_hasDerivWithinAt :
    HasDerivWithinAt rightExtendedPeriod
      (-deriv ellipticFReal ellipticVerticalUpper+ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)
      (Iio ellipticVerticalUpper) ellipticVerticalUpper := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : ellipticVerticalUpper ∉ Iio ellipticVerticalUpper)).mpr
  apply actualPeriodAlong_right_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ ellipticVerticalUpper := ne_of_lt ht
  simp [slope_def_field,rightExtendedPeriod,Function.update_of_ne hne]
  ring

theorem actualPeriodAlong_deriv_eventually_certified_right :
    ∀ᶠ t in 𝓝[<] ellipticVerticalUpper,
      (1336523172824375/10^16:ℝ) < deriv actualPeriodAlong t ∧
        deriv actualPeriodAlong t < (1336532383070600/10^16:ℝ) :=
  actualPeriodAlong_deriv_right_limit.eventually
    (Ioo_mem_nhds actual_right_slope_certificate.1 actual_right_slope_certificate.2)

theorem actualPeriodAlong_strictMono_negative_near_right :
    ∃ l : ℝ, 0 < l ∧ l < ellipticVerticalUpper ∧
      StrictMonoOn actualPeriodAlong (Ioo l ellipticVerticalUpper) ∧
      ∀ t ∈ Ioo l ellipticVerticalUpper, actualPeriodAlong t < 0 := by
  have hpos : ∀ᶠ t in 𝓝[<] ellipticVerticalUpper, 0 < deriv actualPeriodAlong t :=
    actualPeriodAlong_deriv_right_limit.eventually (eventually_gt_nhds actual_right_slope_pos)
  have hs : {t | 0 < deriv actualPeriodAlong t ∧ actualPeriodAlong t < 0} ∈ 𝓝[<] ellipticVerticalUpper :=
    hpos.and actualPeriodAlong_eventually_negative_right
  obtain ⟨b,hb,hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hs
  obtain ⟨l,hl,hlT⟩ := exists_between (max_lt (show b < ellipticVerticalUpper from hb) ellipticVerticalUpper_pos)
  have hl0 : 0 < l := (le_max_right b 0).trans_lt hl
  have hbl : b < l := (le_max_left b 0).trans_lt hl
  refine ⟨l,hl0,hlT,?_,?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioo l ellipticVerticalUpper)
    · intro t ht
      exact (actualPeriodAlong_hasDerivAt ⟨hl0.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
    · intro t ht
      have hm := interior_subset ht
      exact (hsub ⟨hbl.trans hm.1,hm.2⟩).1
  · intro t ht
    exact (hsub ⟨hbl.trans ht.1,ht.2⟩).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rightExtendedPeriod_hasDerivWithinAt
#print axioms TwoAxisHelicoid.actualPeriodAlong_strictMono_negative_near_right
