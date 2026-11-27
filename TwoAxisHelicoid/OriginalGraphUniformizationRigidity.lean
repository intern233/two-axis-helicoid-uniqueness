import TwoAxisHelicoid.FilledOriginalGraphRigidity
import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.OriginalHelicoidClassification

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- On the original regular minimal surface, the physical single-sheeted
C¹ end determines its conformal puncture, both Weierstrass pole orders
and the complete positive similarity. The only outside theorem used
here is simply connected uniformization. -/
theorem original_graph_similarity_of_classical_uniformization (s : OriginalHelicoidRepresentative)
    (uni : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ (U : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
      (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)), 0<k ∧
      ∀ x, certifiedTorusImmersion (U x)=k • E (s.euclideanPosition x) := by
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := man
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  have non : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let R := axisSpatialNormalization s.axes.pitch_ne ![0,0,0]
  let X := R ∘ s.position
  have closed : IsClosedEmbedding X := R.isClosedEmbedding.comp s.closedEmbedding
  have normalized : ∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart X e := by
    intro e he z hz
    obtain ⟨hh,hc,hi⟩ := charts e he z hz
    exact reference_frame_harmonic_chart hh hc hi s.axes.pitch_ne
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling closed normalized s.graphEnd
    (topological_plane_uniformization_of_classical uni)
  exact filled_graph_surface_certified s.topologicalType (compact_genus_one_uniformization_of_classical uni _)
    s.position s.closedEmbedding charts E hol s.axes s.graphEnd

/-- A published existence input together with classical uniformization
gives one and only one image class of original C¹ representatives. -/
theorem original_graph_unique_class_of_uniformization_and_existence
    (uni : SimplyConnectedNoncompactUniformization.{0}) (whw : Nonempty OriginalHelicoidRepresentative) :
    ∃! c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ s : OriginalHelicoidRepresentative, Quotient.mk (spatialSimilaritySetoid _) s.image=c := by
  apply unique_spatial_image_class_of_common_model (fun s : OriginalHelicoidRepresentative => s.image) (range certifiedTorusImmersion) whw
  intro s
  obtain ⟨U,k,E,hk,h⟩ := original_graph_similarity_of_classical_uniformization s uni
  exact image_similarity_of_surjective_parameters s.euclideanPosition certifiedTorusImmersion U U.surjective k E 0 hk
    (fun x => by simpa only [add_zero] using h x)

/-- The same two external inputs transfer actual global embeddedness to
the certified immersion, including its entire central compact region. -/
theorem certified_embedding_of_uniformization_and_original_existence
    (uni : SimplyConnectedNoncompactUniformization.{0}) (whw : Nonempty OriginalHelicoidRepresentative) :
    IsClosedEmbedding certifiedTorusImmersion := by
  obtain ⟨s⟩ := whw
  obtain ⟨U,k,E,hk,h⟩ := original_graph_similarity_of_classical_uniformization s uni
  let F := E.toDilationEquiv.trans (DilationEquiv.smulTorsor (0 : EuclideanSpace ℝ (Fin 3)) hk.ne')
  have eq : certifiedTorusImmersion=F ∘ s.euclideanPosition ∘ U.symm := by
    funext z
    change certifiedTorusImmersion z=k • E (s.euclideanPosition (U.symm z))+0
    simpa only [U.apply_symm_apply,add_zero] using h (U.symm z)
  rw [eq]
  exact F.toHomeomorph.isClosedEmbedding.comp (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    s.closedEmbedding).comp U.symm.isClosedEmbedding)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_similarity_of_classical_uniformization
#print axioms TwoAxisHelicoid.original_graph_unique_class_of_uniformization_and_existence
#print axioms TwoAxisHelicoid.certified_embedding_of_uniformization_and_original_existence
