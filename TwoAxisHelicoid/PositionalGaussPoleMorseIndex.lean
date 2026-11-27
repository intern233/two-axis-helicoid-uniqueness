import TwoAxisHelicoid.HalfPlaneGaussMorseIndex
import TwoAxisHelicoid.SurfaceIndexOrthogonalTransport
import TwoAxisHelicoid.PublishedGeometricClassification

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- TwoAxisHelicoid, Proposition D.2 for the actual positional surface class,
using only the meromorphic end theorem. The compact torus
uniformization, the intersection theorem and existence of a separate
representative are unnecessary for the local compact variations. -/
theorem positional_morse_index_from_published_end (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :=
    real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,hm,he,hj⟩ := puncture_pullback_isothermal_atlas A.point A.marking s.position A.spatial A.agrees A.isothermal
  let _ := S
  have manifold : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := hm
  obtain ⟨base,_⟩ := s.axes.vertical 0
  let Z := fun x => A.offset+A.frame (s.position x)
  let Y := fun q => A.offset+A.frame (A.spatial q)
  have eq (x : s.carrier) : Y (A.marking x).1=Z x := congrArg (fun v => A.offset+A.frame v) (A.agrees x)
  obtain ⟨U⟩ := abstract_conformal_filling_gives_double_pole_end base A.point A.marking hj A.chart A.holomorphic
    A.end_mem A.centered Z Y eq A.height A.heightOrder A.gauss A.gaussOrder
  have regular := orthogonal_affine_harmonic_charts s.position (fun d hd => transfer (he d hd)) A.frame A.orthogonal A.offset
  exact ⟨S,hm,he,surface_morse_index_of_orthogonal_affine s.position A.frame.toContinuousLinearEquiv A.offset
    A.orthogonal (geometric_double_pole_end_infinite_morse_index regular U)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_morse_index_from_published_end
