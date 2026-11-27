import TwoAxisHelicoid.CertifiedGlobalEmbeddingFromCertificates
import TwoAxisHelicoid.PlacedGraphPointedConclusion
import TwoAxisHelicoid.CertifiedMarkedExistenceCriterion
import TwoAxisHelicoid.OriginalPublishedEndAlternatives

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The full graph-ended geometric class contains exactly one spatial
similarity class, and the certified model supplies an actual example. -/
theorem original_graph_unique_similarity_class :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) :=
  graph_similarity_from_certified_embedding certified_global_closed_embedding

/-- The pointed form of Theorem 1.1 under the single-sheet C¹ asymptotic
condition of Section 2. The class contains the certified model and every
original representative has the stated marked Gauss divisor and period lattice. -/
theorem original_graph_pointed_one_one : OriginalGraphTheoremOneOne :=
  graph_pointed_one_one_of_certified_embedding certified_global_closed_embedding

/-- The same pointed classification with the physical Euclidean
position of each original graph-ended surface left unrestricted. -/
theorem placed_graph_pointed_one_one : PlacedGraphTheoremOneOne :=
  placed_pointed_graph_of_normalized original_graph_pointed_one_one

/-- The marked example needed in the manuscript's existence argument,
with the two end pole orders and both full axes, constructed at the
unique certified period root. -/
theorem marked_embedded_helicoid_example_proved : PublishedMarkedEmbeddedHelicoidExample :=
  marked_embedded_example_of_certified_injective certified_global_closed_embedding.injective

/-- For the weak positional formulation, the original
Bernstein--Breiner end theorem alone now suffices. -/
theorem original_one_one_from_published_finite_end
    (bbc : PublishedFiniteOneEndDifferentialGeometry) : OriginalPositionalTheoremOneOne :=
  original_one_one_of_finite_end_and_embedded_example bbc marked_embedded_helicoid_example_proved

/-- For the weaker positional end condition only the universal rough
curvature estimate on original surfaces remains as a premise.
Existence is supplied by the explicit certified closed embedding. -/
theorem original_positional_one_one_of_end_curvature
    (curvature : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    OriginalPositionalTheoremOneOne :=
  positional_classification_from_certified_embedding certified_global_closed_embedding curvature

/-- The published finite-topology curvature theorem by itself
suffices for the manuscript's positional formulation, with an
independent explicit embedded example. -/
theorem original_one_one_from_published_curvature
    (mp : PublishedFiniteTopologyGaussianCurvature) : OriginalPositionalTheoremOneOne := by
  apply original_positional_one_one_of_end_curvature
  intro s
  obtain ⟨C,cp,bd⟩ := original_gaussian_bound_of_finite_topology_publication mp s.toOriginalSmoothHelicoid
  exact original_physical_shape_bound_of_gaussian _ cp bd

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_positive_level_injective
#print axioms TwoAxisHelicoid.certified_global_closed_embedding
#print axioms TwoAxisHelicoid.original_graph_unique_similarity_class
#print axioms TwoAxisHelicoid.original_graph_pointed_one_one
#print axioms TwoAxisHelicoid.placed_graph_pointed_one_one
#print axioms TwoAxisHelicoid.marked_embedded_helicoid_example_proved
#print axioms TwoAxisHelicoid.original_one_one_from_published_finite_end
#print axioms TwoAxisHelicoid.original_positional_one_one_of_end_curvature
#print axioms TwoAxisHelicoid.original_one_one_from_published_curvature
