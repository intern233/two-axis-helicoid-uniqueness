import TwoAxisHelicoid.OriginalSpinCapGaussMarking
import TwoAxisHelicoid.PlacedGraphPointedConclusion
import TwoAxisHelicoid.OriginalPublishedEndAlternatives

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The physical weak-end class with all finite and infinite markings
on one and the same normalized parameter torus for each actual surface. -/
def PlacedPositionalJointTheoremOneOne : Prop :=
  let p := certifiedClosedParameters
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, Quotient.mk Q s.image=c
  (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
    IsClosedEmbedding certifiedTorusImmersion ∧
    (∀ s : PlacedPositionalHelicoid, HasCertifiedSpinCapGaussMarking s.normalized) ∧
    certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
    p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
    p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem placed_positional_joint_of_original (proved : OriginalPositionalTheoremOneOne) :
    PlacedPositionalJointTheoremOneOne := by
  obtain ⟨⟨c,rep,unique⟩,model,embedding,all,params⟩ := proved
  exact ⟨⟨c,(placed_class_iff_original c).mpr rep,fun u hu => unique u ((placed_class_iff_original u).mp hu)⟩,
    (placed_class_iff_original _).mpr model,embedding,
    fun s => certified_spin_cap_gauss_marking_of_pointed_cap s.normalized (all s.normalized).1,params⟩

/-- The published finite-end theorem and the published embedded example
give the weak-end theorem, including the physical placement and a
single marking on each surface. -/
theorem placed_positional_joint_from_finite_end_and_example
    (bbc : PublishedFiniteOneEndDifferentialGeometry) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    PlacedPositionalJointTheoremOneOne :=
  placed_positional_joint_of_original (original_one_one_of_finite_end_and_embedded_example bbc whw)

theorem placed_positional_joint_from_curvature_and_example
    (mp : PublishedFiniteTopologyGaussianCurvature) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    PlacedPositionalJointTheoremOneOne :=
  placed_positional_joint_of_original (original_one_one_of_two_publications mp whw)

/-- For the stronger geometric end definition of Section 2, the published
example alone gives all pointed conclusions for every physical placement. -/
theorem placed_graph_joint_from_published_example (whw : PublishedMarkedEmbeddedHelicoidExample) :
    PlacedGraphTheoremOneOne ∧ ∀ s : PlacedGraphHelicoid, HasCertifiedSpinCapGaussMarking s.normalizedGraph.toPositional :=
  ⟨placed_pointed_graph_of_normalized (graph_pointed_one_one_of_published_example whw),
    fun s => original_graph_certified_spin_cap_gauss_marking s.normalizedGraph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_positional_joint_from_finite_end_and_example
#print axioms TwoAxisHelicoid.placed_positional_joint_from_curvature_and_example
#print axioms TwoAxisHelicoid.placed_graph_joint_from_published_example
