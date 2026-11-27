import TwoAxisHelicoid.OriginalPhysicalEndFromTwoPoles
import TwoAxisHelicoid.PublishedGeometricClassification

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The two-pole version of Bernstein--Breiner is the sole literature
input for this physical-chart and negative second-variation conclusion. -/
theorem original_physical_end_and_index_from_published_poles (bbc : PublishedOneHandleEndTheorem)
    (s : OriginalPositionallyAsymptoticHelicoid) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
      (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d ∧ HarmonicImmersionChart s.position d) ∧
      (∃ G : GeometricExteriorCoordinate s.position, G.correction 0=0) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  exact original_physical_end_and_index_of_conformal_poles s A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_physical_end_and_index_from_published_poles
