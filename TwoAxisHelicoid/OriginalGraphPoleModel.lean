import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.MarkedHolomorphicFilling
import TwoAxisHelicoid.MarkedGraphPhysicalPoles
import TwoAxisHelicoid.TorusEndPoleModel
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- For the C¹ definition of a genus-one helicoid the one-point
compact model, its isothermal marking, and the two double poles in
the actual spatial frame are consequences of the hypotheses and
simply connected uniformization. -/
theorem original_graph_independent_conformal_pole_model (s : OriginalHelicoidRepresentative)
    (uni : SimplyConnectedNoncompactUniformization.{0}) : Nonempty (PublishedConformalPoleModel s.position) := by
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := man
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  have non : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let R := axisSpatialNormalization s.axes.pitch_ne ![0,0,0]
  have normalized : ∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart (R ∘ s.position) e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 s.axes.pitch_ne
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling (R.isClosedEmbedding.comp s.closedEmbedding) normalized s.graphEnd
    (topological_plane_uniformization_of_classical uni)
  obtain ⟨L,f,Y,_,_,pos,closed,image,regular⟩ := marked_harmonic_torus_of_filling s.topologicalType
    (compact_genus_one_uniformization_of_classical uni _) s.position s.closedEmbedding charts E hol
  let axes : OriginalHelicoidAxes (range (fun q : PuncturedPeriodTorus L => Y q.1)) :=
    {s.axes with horizontal := fun r => image.symm ▸ s.axes.horizontal r, vertical := fun r => image.symm ▸ s.axes.vertical r}
  have eq : (coordinateToTube ∘ R ∘ s.position) ∘ f.symm=(fun q : PuncturedPeriodTorus L => coordinateToTube (R (Y q.1))) := by
    funext q
    change coordinateToTube (R (s.position (f.symm q)))=coordinateToTube (R (Y q.1))
    rw [← pos (f.symm q),f.apply_symm_apply]
  obtain ⟨height,gauss⟩ := marked_graph_physical_poles L Y closed axes regular (eq ▸ s.graphEnd.comp_homeomorph f.symm)
  exact torus_end_pole_model L f Y pos regular height gauss s.axes.pitch_ne s.positional.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_independent_conformal_pole_model
