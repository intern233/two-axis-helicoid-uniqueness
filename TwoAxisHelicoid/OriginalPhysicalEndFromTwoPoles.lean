import TwoAxisHelicoid.PhysicalConformalPoleAlignment
import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.OpenPuncturedCoreConnectivity
import TwoAxisHelicoid.OrthogonalExteriorMorseIndex

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology ContDiff Manifold

/-- For every representative in the manuscript's original positional
class the actual two affine axes intersect. This conclusion uses only
the real minimal immersion and its topology and positional asymptote. -/
theorem original_positional_axes_intersect (s : OriginalPositionallyAsymptoticHelicoid) :
    ∃ r : ℝ, s.axes.horizontalPoint+r • ![s.axes.horizontalDirection.re,s.axes.horizontalDirection.im,0]=
      ![0,0,s.axes.horizontalPoint 2] := by
  let _ := punctured_torus_is_path_connected s.modelTorus
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  exact original_axes_meet_before_compactification s.closedEmbedding charts s.axes s.approaches

/-- Appendix D on the real original surface from the published
compactification, raw pole orders and positional asymptote alone.
The same true exterior in the physical axes has a correction vanishing
at infinity. The construction does not require genus-one uniformization. -/
theorem original_physical_end_and_index_of_conformal_poles (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
      (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d ∧ HarmonicImmersionChart s.position d) ∧
      (∃ G : GeometricExteriorCoordinate s.position, G.correction 0=0) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :
      HarmonicImmersionChart s.position e :=
    real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,man,iso,fill⟩ := puncture_pullback_isothermal_atlas A.point A.marking s.position A.spatial A.agrees A.isothermal
  let _ := S
  let _ := man
  let _ := punctured_torus_is_path_connected s.modelTorus
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  have charts (d : OpenPartialHomeomorph s.carrier ℂ) (hd : d∈atlas ℂ s.carrier) := transfer (iso d hd)
  obtain ⟨b,_⟩ := s.axes.vertical 0
  let X := fun x => A.offset+A.frame (s.position x)
  let Y := fun q => A.offset+A.frame (A.spatial q)
  have agrees (x : s.carrier) : Y (A.marking x).1=X x := congrArg (fun v => A.offset+A.frame v) (A.agrees x)
  obtain ⟨D⟩ := abstract_conformal_filling_gives_double_pole_end b A.point A.marking fill A.chart A.holomorphic
    A.end_mem A.centered X Y agrees A.height A.heightOrder A.gauss A.gaussOrder
  let endData : GeometricDoublePoleInSomeFrame s.position := ⟨A.frame,A.orthogonal,A.offset,D,A.pitch,A.pitch_ne,A.asymptote⟩
  obtain ⟨G,zero⟩ := external_frame_poles_give_physical_exterior s.closedEmbedding charts s.axes s.approaches endData
  have idx := orthogonal_exterior_chart_implies_infinite_morse_index s.topologicalType s.position
    s.closedEmbedding.continuous charts (LinearEquiv.refl ℝ _) (fun _ _ => rfl) 0
    (by simpa only [LinearEquiv.refl_apply,zero_add] using G)
  exact ⟨S,man,fun d hd => ⟨iso d hd,charts d hd⟩,⟨G,zero⟩,idx⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_positional_axes_intersect
#print axioms TwoAxisHelicoid.original_physical_end_and_index_of_conformal_poles
