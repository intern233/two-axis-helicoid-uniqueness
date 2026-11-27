import TwoAxisHelicoid.CenteredActualImmersion
import TwoAxisHelicoid.ActualIntrinsicMetric

namespace TwoAxisHelicoid
open Complex Bundle Set Filter Manifold
open scoped Topology ContDiff Manifold Bundle
set_option maxHeartbeats 1000000

/-- The standard induced length metric of the centered immersion. -/
@[instance_reducible] noncomputable def centeredActualInducedEMetricSpace {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    EMetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
  euclideanImmersionEMetricSpace (centeredActualEuclideanImmersion ht ha hc hG hH)
    ((centeredActualEuclideanImmersion_contMDiff ht ha hc hG hH).of_le le_top)
    (centeredActualEuclideanImmersion_mvfderiv_injective ht ha hc hG hH)

@[instance_reducible] noncomputable def centeredActualInducedMetricSpace {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    MetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) := by
  let : EMetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
    centeredActualInducedEMetricSpace ht ha hc hG hH
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

theorem centeredActualInducedMetric_complete {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    @CompleteSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht))
      (centeredActualInducedMetricSpace ht ha hc hG hH).toUniformSpace := by
  simpa only [centeredActualInducedMetricSpace,centeredActualInducedEMetricSpace] using!
    proper_euclideanImmersion_complete (centeredActualEuclideanImmersion ht ha hc hG hH)
      ((centeredActualEuclideanImmersion_contMDiff ht ha hc hG hH).of_le le_top)
      (centeredActualEuclideanImmersion_mvfderiv_injective ht ha hc hG hH)
      (centeredActualEuclideanImmersion_isProperMap ht ha hc hG hH)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.centeredActualInducedMetric_complete
