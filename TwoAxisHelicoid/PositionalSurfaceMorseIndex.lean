import TwoAxisHelicoid.PublishedPoleSurfaceMorseIndex
import TwoAxisHelicoid.PublishedGeometricClassification

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology Manifold ContDiff

/-- Appendix D.2 on the original positionally asymptotic surface, specialized
only from the published end theorem and classical smooth uniformization. -/
theorem positional_helicoid_infinite_morse_index (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
      (∀ d ∈ atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  exact original_smooth_published_poles_infinite_morse_index s.toOriginalSmoothHelicoid
    (compact_genus_one_uniformization_of_classical poincare s.modelTorus) A s.approaches

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_helicoid_infinite_morse_index
