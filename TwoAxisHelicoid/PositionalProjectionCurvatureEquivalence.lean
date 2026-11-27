import TwoAxisHelicoid.OriginalHeightCurvatureEquivalence
import TwoAxisHelicoid.PositionalEndProjectionCriterion

namespace TwoAxisHelicoid

/-- In the weaker positional formulation, eventual regularity of the
nearest-point projection is equivalent to bounded physical curvature.
The derivative condition needs no quantitative bound on its inverse. -/
theorem positional_physical_curvature_iff_noncritical_projection (s : OriginalPositionallyAsymptoticHelicoid) :
    HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid ↔
      NoncriticalHelicoidEndProjection (coordinateToTube ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position) :=
  (positional_shape_iff_height_graph s).trans (original_positional_height_iff_noncritical s)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_physical_curvature_iff_noncritical_projection
