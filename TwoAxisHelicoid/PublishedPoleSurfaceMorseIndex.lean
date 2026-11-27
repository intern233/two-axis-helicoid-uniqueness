import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.MarkedPoleGeometricExterior
import TwoAxisHelicoid.OrthogonalExteriorMorseIndex

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Appendix D.2 on the actual original surface, with the published compact
conformal model and the two meromorphic double poles in the BBC frame.
All exterior height coordinates, negative test functions and their actual
ambient normal variations are derived. -/
theorem original_smooth_published_poles_infinite_morse_index (surface : OriginalSmoothHelicoid)
    (uniform : CompactGenusOneUniformization.{0} surface.modelTorus) (A : PublishedConformalPoleModel surface.position)
    (hend : ApproachesSetAtInfinity (range surface.position) (range (axisRuledHelicoid I surface.axes.pitch 0))) :
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧
      (∀ d ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex surface.position := by
  obtain ⟨S,hm,hcharts,L,f,Y,hf,hi,he,hclosed,him,hreg,hh,hg⟩ :=
    original_smooth_surface_published_poles_to_torus surface uniform A hend
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω surface.carrier := hm
  obtain ⟨T,b,hT,⟨D⟩⟩ := marked_poles_two_lines_geometric_exterior L Y hclosed surface.axes.horizontalDirection
    surface.axes.unit surface.axes.horizontalPoint (him.symm ▸ surface.axes.horizontal) (him.symm ▸ surface.axes.vertical)
    surface.axes.pitch_ne (him.symm ▸ hend) hreg hh hg
  obtain ⟨D'⟩ := geometric_exterior_coordinate_pullback f hf hi (fun x => congrArg (fun u => b+T u) (he x)) D
  exact ⟨S,hm,fun d hd => (hcharts d hd).1,
    orthogonal_exterior_chart_implies_infinite_morse_index surface.topologicalType surface.position
      surface.closedEmbedding.continuous (fun d hd => (hcharts d hd).2) T hT b D'⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_smooth_published_poles_infinite_morse_index
