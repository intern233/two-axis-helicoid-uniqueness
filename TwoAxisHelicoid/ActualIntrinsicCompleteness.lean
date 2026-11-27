import TwoAxisHelicoid.ActualEuclideanManifoldImmersion
import TwoAxisHelicoid.ProperImmersionCompleteness

namespace TwoAxisHelicoid
open Complex Bundle Set Filter Topology
open scoped Topology ContDiff Manifold Bundle
set_option maxHeartbeats 1000000

/-- The genuine induced length distance of the explicitly constructed,
periodically closed punctured torus immersion. -/
@[instance_reducible] noncomputable def actualTorusInducedEMetricSpace {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    EMetricSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
  euclideanImmersionEMetricSpace (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH)
    ((actualEuclideanPuncturedTorusImmersion_contMDiff ht ha hc hG hH).of_le le_top)
    (actualEuclideanPuncturedTorusImmersion_mvfderiv_injective ht ha hc hG hH)

/-- Intrinsic completeness of the actual immersion, from its already
proved spatial properness and actual injective differential. -/
theorem actualTorusImmersion_intrinsically_complete {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    @CompleteSpace (PuncturedPeriodTorus (rhombicPeriodPair t ht))
      (actualTorusInducedEMetricSpace ht ha hc hG hH).toUniformSpace := by
  simpa only [actualTorusInducedEMetricSpace] using!
    proper_euclideanImmersion_complete (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH)
    ((actualEuclideanPuncturedTorusImmersion_contMDiff ht ha hc hG hH).of_le le_top)
    (actualEuclideanPuncturedTorusImmersion_mvfderiv_injective ht ha hc hG hH)
    (actualEuclideanPuncturedTorusImmersion_isProperMap ht ha hc hG hH)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualTorusImmersion_intrinsically_complete
