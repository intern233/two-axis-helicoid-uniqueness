import TwoAxisHelicoid.ActualIntrinsicCompleteness
import TwoAxisHelicoid.ConnectedEMetric

namespace TwoAxisHelicoid
open Complex Bundle Set Filter Manifold
open scoped Topology ContDiff Manifold Bundle
set_option maxHeartbeats 1000000

instance puncturedPeriodTorusConnectedSpace (L : PeriodPair) :
    ConnectedSpace (PuncturedPeriodTorus L) :=
  isConnected_iff_connectedSpace.mp (periodTorus_punctured_isConnected L)

/-- The actual induced Riemannian distance is finite on the connected
punctured torus, so it defines an ordinary metric with the original topology. -/
@[instance_reducible] noncomputable def actualTorusInducedMetricSpace {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    MetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) := by
  let : EMetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
    actualTorusInducedEMetricSpace ht ha hc hG hH
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

theorem actualTorusInducedMetric_complete {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    @CompleteSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht))
      (actualTorusInducedMetricSpace ht ha hc hG hH).toUniformSpace := by
  simpa only [actualTorusInducedMetricSpace] using!
    actualTorusImmersion_intrinsically_complete ht ha hc hG hH

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualTorusInducedMetric_complete
