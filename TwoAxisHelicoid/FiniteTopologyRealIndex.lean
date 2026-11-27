import TwoAxisHelicoid.OriginalRealMorseIndex
import TwoAxisHelicoid.FiniteTopologyEndConsequences

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The finite-topology one-ended geometric theorem yields negative
normal variations of arbitrary dimension in the originally specified
smooth structure of each properly embedded minimal handle. -/
theorem original_real_index_from_finite_topology (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (s : OriginalSmoothHelicoid) : HasInfiniteRealSurfaceMorseIndex s.position := by
  have old := smooth_surface_regular_manifold_chart s.smooth s.immersion
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :
      HarmonicImmersionChart s.position e := real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,man,charts,idx⟩ := original_one_handle_index_from_general_end_theorem bbc s
  let _ := s.charts
  exact conformal_index_gives_original_real_index (orig := s.charts) old S man (fun d hd => transfer (charts d hd)) idx

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_real_index_from_finite_topology
