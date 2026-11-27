import TwoAxisHelicoid.OriginalClassFromCertifiedEmbedding

namespace TwoAxisHelicoid
open Set Topology

/-- The full pointed conclusion for the single-sheet C¹ graph ends
specified in Section 2 of TwoAxisHelicoid. The cap, normalization and divisor
refer to the same original representative. -/
def OriginalGraphTheoremOneOne : Prop :=
  let p := certifiedClosedParameters
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  let rep := fun c : Quotient Q => ∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image=c
  (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
    IsClosedEmbedding certifiedTorusImmersion ∧
    (∀ s : OriginalHelicoidRepresentative, HasPointedOriginalSpinBranchCap s.toPositional ∧
      HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
    certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+Complex.I*p.t ∧
    p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
    p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

/-- Existence of any unmarked geometric graph-ended surface suffices
for every pointed and numerical conclusion, including the embedding of
the actual certified model. -/
theorem graph_pointed_one_one_of_nonempty (existence : Nonempty OriginalHelicoidRepresentative) :
    OriginalGraphTheoremOneOne := by
  obtain ⟨unique,represented,embedding⟩ := graph_unique_class_from_annuli
    annular_riemann_surface_uniformization_proved existence
  refine ⟨unique,represented,embedding,?_,rfl,rfl,?_,?_⟩
  · intro s
    have all := graph_cap_normalization_and_index_from_annuli annular_riemann_surface_uniformization_proved s
    exact ⟨all.1,all.2.1,all.2.2.1⟩
  · convert certifiedClosedParameters_bounds.1 using 1
    norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1
    norm_num [rootALower,rootAUpper]

/-- The manuscript's published Weber--Hoffman--Wolf example is the
only external premise in this route for the graph-ended formulation. -/
theorem graph_pointed_one_one_of_published_example (whw : PublishedMarkedEmbeddedHelicoidExample) :
    OriginalGraphTheoremOneOne :=
  graph_pointed_one_one_of_nonempty (original_c1_representative_of_published_marked_example whw)

theorem graph_pointed_one_one_of_certified_embedding (emb : IsClosedEmbedding certifiedTorusImmersion) :
    OriginalGraphTheoremOneOne := by
  obtain ⟨s,_⟩ := certified_original_representative_of_injective emb.injective
  exact graph_pointed_one_one_of_nonempty ⟨s⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_pointed_one_one_of_nonempty
#print axioms TwoAxisHelicoid.graph_pointed_one_one_of_published_example
#print axioms TwoAxisHelicoid.graph_pointed_one_one_of_certified_embedding
