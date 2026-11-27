import TwoAxisHelicoid.PositionalBoundedCurvatureGraph
import TwoAxisHelicoid.OriginalGraphManuscriptConclusion
import TwoAxisHelicoid.OriginalGraphAppendices

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

def OriginalPositionallyAsymptoticHelicoid.graphRepresentative (s : OriginalPositionallyAsymptoticHelicoid)
    (bound : HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) : OriginalHelicoidRepresentative :=
  {s.toOriginalSmoothHelicoid with graphEnd := positional_c1_graph_of_bounded_shape s bound}

/-- From the weak positional condition it suffices to bound the shape
operator outside a compact set. All conformal and meromorphic inputs
on each such original surface follow from uniformization. -/
theorem positional_curvature_pointed_normalization (s : OriginalPositionallyAsymptoticHelicoid)
    (bound : HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid)
    (uni : SimplyConnectedNoncompactUniformization.{0}) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  let t := s.graphRepresentative bound
  exact ⟨original_graph_independent_conformal_pole_model t uni,(graph_pointed_cap_and_normalization t uni).2⟩

theorem positional_unique_class_of_bounded_curvature
    (bounded : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid)
    (uni : SimplyConnectedNoncompactUniformization.{0}) (existsSurface : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    (∃! c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk (spatialSimilaritySetoid _) s.image=c) ∧
      IsClosedEmbedding certifiedTorusImmersion := by
  refine ⟨?_,certified_embedding_of_uniformization_and_original_existence uni (existsSurface.map (fun s => s.graphRepresentative (bounded s)))⟩
  apply unique_spatial_image_class_of_common_model (fun s : OriginalPositionallyAsymptoticHelicoid => s.image) (range certifiedTorusImmersion) existsSurface
  intro s
  obtain ⟨U,k,E,hk,e⟩ := original_graph_similarity_of_classical_uniformization (s.graphRepresentative (bounded s)) uni
  exact image_similarity_of_surjective_parameters s.euclideanPosition certifiedTorusImmersion U U.surjective k E 0 hk
    (fun x => by simpa only [OriginalPositionallyAsymptoticHelicoid.graphRepresentative,OriginalSmoothHelicoid.euclideanPosition,add_zero] using e x)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_curvature_pointed_normalization
#print axioms TwoAxisHelicoid.positional_unique_class_of_bounded_curvature
