import TwoAxisHelicoid.CertifiedGlobalEmbeddedHelicoid
import TwoAxisHelicoid.PositionalDiskEstimateConclusion

namespace TwoAxisHelicoid

/-- For the weaker positional end the published one-sided disk curvature
estimate suffices. The certified example provides existence in Lean. -/
theorem positional_one_one_from_disk_curvature (cm : OneSidedEmbeddedMinimalDiskEstimate) :
    OriginalPositionalTheoremOneOne :=
  original_positional_one_one_of_end_curvature (positional_end_curvature_from_disk_estimate cm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_one_one_from_disk_curvature
