import TwoAxisHelicoid.PositionalCurvatureFromDiskEstimate
import TwoAxisHelicoid.GraphAppendicesAfterUniformization
import TwoAxisHelicoid.OriginalClassificationAfterUniformization

namespace TwoAxisHelicoid
open Set Topology

/-- The physically stated one-sided disk estimate gives the entire
classification for positional ends once there is an embedded example. -/
theorem positional_one_one_from_disk_curvature_and_example
    (cm : OneSidedEmbeddedMinimalDiskEstimate) (exampleExists : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    OriginalPositionalTheoremOneOne :=
  original_one_one_from_end_curvature_and_existence (positional_end_curvature_from_disk_estimate cm) exampleExists

/-- With the same one-sided curvature estimate, the weak geometric
class satisfies the analytic end gap and class finiteness in B and
the infinite real Morse index in D, even without an existence premise. -/
theorem positional_appendices_from_disk_curvature (cm : OneSidedEmbeddedMinimalDiskEstimate) :
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, HasInfiniteRealSurfaceMorseIndex s.position) :=
  positional_B_and_D_from_end_curvature (positional_end_curvature_from_disk_estimate cm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_one_one_from_disk_curvature_and_example
#print axioms TwoAxisHelicoid.positional_appendices_from_disk_curvature
