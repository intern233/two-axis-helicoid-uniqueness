import TwoAxisHelicoid.CenteredActualCompleteness
import TwoAxisHelicoid.CenteredActualEnd
import TwoAxisHelicoid.OriginalPeriodBridge

namespace TwoAxisHelicoid
open Complex Set
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

/-- All geometric conclusions of manuscript Proposition 6.3, for the
same explicit centered map on the actual once-punctured complex torus.
Completeness uses its standard induced Riemannian length metric;
minimality uses the first/second fundamental-form formula in its actual
atlas. This statement makes no assertion of global embeddedness. -/
structure ClosedImmersionProperties {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) : Prop where
  analytic : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) ω (centeredActualTorusImmersion ht ha hc hG hH)
  immersion : ∀ q, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ)
    (centeredActualTorusImmersion ht ha hc hG hH) q
  minimal : ∀ q, coordinateMeanCurvature
    (centeredActualTorusImmersion ht ha hc hG hH ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) = 0
  proper : IsProperMap (centeredActualTorusImmersion ht ha hc hG hH)
  complete : @CompleteSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht))
    (centeredActualInducedMetricSpace ht ha hc hG hH).toUniformSpace
  helicoidal : HasHelicoidalC1End (centeredActualTorusImmersion ht ha hc hG hH)
  horizontal_axis : ∀ r : ℝ, ∃ q, centeredActualTorusImmersion ht ha hc hG hH q = ![r,0,0]
  vertical_axis : ∀ r : ℝ, ∃ q, centeredActualTorusImmersion ht ha hc hG hH q = ![0,0,r]

theorem actual_closed_immersion_properties {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) : ClosedImmersionProperties ht ha hc hG hH where
  analytic := centeredActualTorusImmersion_contMDiff ht ha hc hG hH
  immersion := centeredActualTorusImmersion_isDiffImmersionAt ht ha hc hG hH
  minimal := centeredActualTorusImmersion_chart_mean_curvature_zero ht ha hc hG hH
  proper := centeredActualTorusImmersion_isProperMap ht ha hc hG hH
  complete := centeredActualInducedMetric_complete ht ha hc hG hH
  helicoidal := centeredActualTorusImmersion_hasHelicoidalC1End ht ha hc hG hH
  horizontal_axis := (centeredActualTorusImmersion_contains_axes ht ha hc hG hH).1
  vertical_axis := (centeredActualTorusImmersion_contains_axes ht ha hc hG hH).2

/-- The original scalar hypothesis of Proposition 6.3 produces the whole
geometric conclusion, without assuming either closing equation separately. -/
theorem original_period_zero_converse_immersion {t c : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) (hc : c ≠ 0)
    (hH : originalPeriodAlong t = 0) :
    ∃ (ha : verticalA t ∈ Ioo (0 : ℝ) 1)
      (hG : thetaG t (verticalA t) = 0) (hP : thetaHorizontalPeriod t (verticalA t) = 0),
      ClosedImmersionProperties ht.1 ha hc hG hP := by
  have ha := verticalA_spec ht
  have hP : thetaHorizontalPeriod t (verticalA t) = 0 := by
    change actualPeriodAlong t = 0
    rw [← originalPeriodAlong_eq_actual ht]
    exact hH
  exact ⟨ha.1,ha.2,hP,actual_closed_immersion_properties ht.1 ha.1 hc ha.2 hP⟩

/-- An unconditional instance obtained from the exact certified common
period zero. The same map has all eight properties above. -/
theorem certified_converse_immersion :
    ClosedImmersionProperties certifiedClosedParameters.height_pos
      certifiedClosedParameters.abscissa_mem (by norm_num : (1 : ℝ) ≠ 0)
      certifiedClosedParameters.vertical_closed certifiedClosedParameters.horizontal_closed :=
  actual_closed_immersion_properties _ _ _ _ _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_period_zero_converse_immersion
#print axioms TwoAxisHelicoid.certified_converse_immersion
