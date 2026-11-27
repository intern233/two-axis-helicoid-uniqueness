import TwoAxisHelicoid.FiniteTopologyEndConsequences
import TwoAxisHelicoid.OriginalGraphManuscriptConclusion
import TwoAxisHelicoid.PublishedMarkedEmbeddedExample

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The original geometric proof route from the general differential
end theorem. Each candidate receives a common marked cap, the basic
integer branch, its Gauss divisor, and the certified parameters. -/
theorem manuscript_from_general_finite_topology_end (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (poi : SimplyConnectedNoncompactUniformization.{0}) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalPositionallyAsymptoticHelicoid, HasPointedOriginalSpinBranchCap s ∧
        HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧ HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  have whole := classical_finite_topology_gives_published_one_handle_model bbc
  have cap (s : OriginalPositionallyAsymptoticHelicoid) : HasPointedOriginalSpinBranchCap s := by
    obtain ⟨G⟩ := whole s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact original_pointed_spin_cap_from_comparison s G poi
  have norm (s : OriginalPositionallyAsymptoticHelicoid) := (pointed_spin_cap_certifies_original s (cap s)).2
  obtain ⟨unique,model,embedding⟩ := positional_classification_of_pointed_models norm
    ((original_c1_representative_of_published_marked_example whw).map OriginalHelicoidRepresentative.toPositional)
  refine ⟨unique,model,embedding,fun s => ⟨cap s,norm s,original_pointed_gauss_divisor_of_normalization _ (norm s)⟩,
    rfl,rfl,?_,?_⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_from_general_finite_topology_end
