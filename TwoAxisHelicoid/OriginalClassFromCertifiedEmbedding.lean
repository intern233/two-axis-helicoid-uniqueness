import TwoAxisHelicoid.OriginalExistenceCompactCriterion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The full graph-ended geometric class contains exactly one spatial
similarity class, and the certified model supplies an actual example. -/
theorem graph_similarity_from_certified_embedding (embedding : IsClosedEmbedding certifiedTorusImmersion) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) := by
  intro Q rep
  obtain ⟨s,_⟩ := certified_original_representative_of_injective embedding.injective
  have proved := graph_unique_class_from_annuli annular_riemann_surface_uniformization_proved ⟨s⟩
  exact ⟨proved.1,proved.2.1⟩

/-- For the weaker positional end condition only the universal rough
curvature estimate on original surfaces remains as a premise.
Existence is supplied by the explicit certified closed embedding. -/
theorem positional_classification_from_certified_embedding (embedding : IsClosedEmbedding certifiedTorusImmersion)
    (curvature : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    OriginalPositionalTheoremOneOne := by
  obtain ⟨s,_⟩ := certified_original_representative_of_injective embedding.injective
  exact original_one_one_from_end_curvature_and_existence curvature ⟨s.toPositional⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_similarity_from_certified_embedding
#print axioms TwoAxisHelicoid.positional_classification_from_certified_embedding
