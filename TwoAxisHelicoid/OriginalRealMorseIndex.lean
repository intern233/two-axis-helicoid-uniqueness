import TwoAxisHelicoid.RealSurfaceIndexTransfer
import TwoAxisHelicoid.OriginalPhysicalEndFromTwoPoles

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The actual negative variation fields on the two-pole physical end
are smooth in the original real manifold. Their support can be
chosen outside any prescribed compact set of the original surface. -/
theorem original_real_index_of_conformal_poles (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) : HasInfiniteRealSurfaceMorseIndex s.position := by
  have old := smooth_surface_regular_manifold_chart s.smooth s.immersion
  obtain ⟨S,man,charts,_,idx⟩ := original_physical_end_and_index_of_conformal_poles s A
  let _ := s.charts
  exact conformal_index_gives_original_real_index (orig := s.charts) old S man (fun d hd => (charts d hd).2) idx

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_real_index_of_conformal_poles
