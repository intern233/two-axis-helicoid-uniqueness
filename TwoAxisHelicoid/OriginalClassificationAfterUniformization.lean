import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.AnnularOriginalClassification
import TwoAxisHelicoid.PublishedFiniteTopologyCurvature
import TwoAxisHelicoid.PublishedMarkedEmbeddedExample

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- For every actual graph end the conformal pole model, same-marked cap,
normalized data and real Morse index now follow without an external
geometric or uniformization hypothesis. -/
theorem original_graph_poles_cap_and_index (s : OriginalHelicoidRepresentative) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasPointedOriginalSpinBranchCap s.toPositional ∧
      HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid ∧ HasInfiniteRealSurfaceMorseIndex s.position :=
  ⟨(original_annular_end_pole_model_and_index s annular_riemann_surface_uniformization_proved).1,
    graph_cap_normalization_and_index_from_annuli annular_riemann_surface_uniformization_proved s⟩

/-- Any two embedded original surfaces with full C¹ helicoidal ends
have the same spatial image up to a positive similarity. -/
theorem original_graphs_similar (s t : OriginalHelicoidRepresentative) :
    (spatialSimilaritySetoid _).r s.image t.image := by
  have a := (pointed_original_embedding_and_similarity s.toOriginalSmoothHelicoid (original_graph_poles_cap_and_index s).2.2.1).2
  have b := (pointed_original_embedding_and_similarity t.toOriginalSmoothHelicoid (original_graph_poles_cap_and_index t).2.2.1).2
  exact (spatialSimilaritySetoid _).trans a ((spatialSimilaritySetoid _).symm b)

/-- The full spatial, pointed and rational parameter conclusion of
Theorem 1.1 for the manuscript's one-sided positional class. -/
def OriginalPositionalTheoremOneOne : Prop :=
  let p := certifiedClosedParameters
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
  (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
    IsClosedEmbedding certifiedTorusImmersion ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, HasPointedOriginalSpinBranchCap s ∧
      HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧ HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
    certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
    p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
    p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem original_one_one_from_end_curvature_and_existence
    (curvature : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid)
    (existence : Nonempty OriginalPositionallyAsymptoticHelicoid) : OriginalPositionalTheoremOneOne := by
  have all (s : OriginalPositionallyAsymptoticHelicoid) := original_graph_poles_cap_and_index (s.graphRepresentative (curvature s))
  obtain ⟨uniq,rep,emb⟩ := positional_classification_of_pointed_models (fun s => (all s).2.2.1) existence
  exact ⟨uniq,rep,emb,fun s => ⟨(all s).2.1,(all s).2.2.1,(all s).2.2.2.1⟩,rfl,rfl,
    by convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper],
    by convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]⟩

/-- Only the published finite-topology curvature theorem and published
embedded example remain in this route to the weak original theorem. -/
theorem original_one_one_of_two_publications (mp : PublishedFiniteTopologyGaussianCurvature)
    (whw : PublishedMarkedEmbeddedHelicoidExample) : OriginalPositionalTheoremOneOne := by
  apply original_one_one_from_end_curvature_and_existence _ ((original_c1_representative_of_published_marked_example whw).map fun s => s.toPositional)
  intro s
  obtain ⟨C,cp,bd⟩ := original_gaussian_bound_of_finite_topology_publication mp s.toOriginalSmoothHelicoid
  exact original_physical_shape_bound_of_gaussian _ cp bd

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_one_one_of_two_publications
