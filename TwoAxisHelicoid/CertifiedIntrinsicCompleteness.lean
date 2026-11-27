import TwoAxisHelicoid.ActualIntrinsicMetric
import TwoAxisHelicoid.CertifiedProperImmersion

namespace TwoAxisHelicoid
open Complex Bundle Set Filter Manifold
open scoped Topology ContDiff Manifold Bundle

/-- The certified common period root carries the actual complete induced
Riemannian metric. This statement concerns the constructed immersion and
does not assert that the entire immersion is embedded. -/
@[instance_reducible] noncomputable def certifiedTorusInducedMetricSpace :
    MetricSpace (PuncturedPeriodTorus certifiedPeriodPair) :=
  actualTorusInducedMetricSpace certifiedClosedParameters.height_pos
    certifiedClosedParameters.abscissa_mem (by norm_num : (1 : ℝ) ≠ 0)
    certifiedClosedParameters.vertical_closed certifiedClosedParameters.horizontal_closed

theorem certifiedTorusImmersion_intrinsically_complete :
    @CompleteSpace (PuncturedPeriodTorus certifiedPeriodPair)
      certifiedTorusInducedMetricSpace.toUniformSpace := by
  simpa only [certifiedTorusInducedMetricSpace] using!
    actualTorusInducedMetric_complete certifiedClosedParameters.height_pos
      certifiedClosedParameters.abscissa_mem (by norm_num : (1 : ℝ) ≠ 0)
      certifiedClosedParameters.vertical_closed certifiedClosedParameters.horizontal_closed

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certifiedTorusImmersion_intrinsically_complete
