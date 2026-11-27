import TwoAxisHelicoid.OriginalClassificationAfterUniformization
import TwoAxisHelicoid.FlatTorusCanonicalDifferential

namespace TwoAxisHelicoid

/-- The end theorem cited in Section 2 of TwoAxisHelicoid can be used in place of
the rough curvature estimate. The genus-one differential, conformal
marking and subsequent classification are then proved in Lean. -/
theorem original_one_one_of_finite_end_and_embedded_example
    (bbc : PublishedFiniteOneEndDifferentialGeometry) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    OriginalPositionalTheoremOneOne :=
  original_manuscript_from_one_holomorphic_form bbc
    (genus_one_holomorphic_differential_from_annuli annular_riemann_surface_uniformization_proved) whw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_one_one_of_finite_end_and_embedded_example
