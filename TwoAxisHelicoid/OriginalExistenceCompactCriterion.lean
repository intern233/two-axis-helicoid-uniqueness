import TwoAxisHelicoid.OriginalClassificationAfterUniformization
import TwoAxisHelicoid.PlacedManuscriptConclusion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Embedded existence for true graph ends is equivalent, with no
external theorem, to injectivity on a single compact subset of the
certified punctured torus. The same subset contains both preimages of
every possible spatial double point. -/
theorem graph_existence_iff_compact_injectivity :
    ∃ K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact K ∧
      immersionDoublePoints certifiedTorusImmersion ⊆ K ×ˢ K ∧
      (Nonempty OriginalHelicoidRepresentative ↔ InjOn certifiedTorusImmersion K) := by
  obtain ⟨_,K,hK,all,criterion⟩ := certified_compact_embedding_criterion
  refine ⟨K,hK,all,?_,?_⟩
  · rintro ⟨s⟩
    exact criterion.mp (pointed_original_embedding_and_similarity s.toOriginalSmoothHelicoid
      (original_graph_poles_cap_and_index s).2.2.1).1
  · intro inject
    obtain ⟨s,_⟩ := certified_original_representative_of_injective (criterion.mpr inject).injective
    exact ⟨s⟩

/-- The geometric example in Theorem 1.1 may be completely unmarked
and in arbitrary Euclidean position. Only rough end curvature is
required of the original positional class. -/
theorem placed_one_one_of_end_curvature_and_unmarked_example
    (curvature : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid)
    (exampleExists : Nonempty PlacedPositionalHelicoid) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, HasPointedOriginalSpinBranchCap s.normalized ∧
        HasCertifiedPointedNormalization s.normalized.toOriginalSmoothHelicoid ∧
        HasOriginalPointedGaussDivisor s.normalized.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  obtain ⟨⟨c,hc,unique⟩,model,embedding,cap,parameters⟩ :=
    original_one_one_from_end_curvature_and_existence curvature (exampleExists.map PlacedPositionalHelicoid.normalized)
  exact ⟨⟨c,(placed_class_iff_original c).mpr hc,fun u hu => unique u ((placed_class_iff_original u).mp hu)⟩,
    (placed_class_iff_original _).mpr model,embedding,fun s => cap s.normalized,parameters⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_existence_iff_compact_injectivity
#print axioms TwoAxisHelicoid.placed_one_one_of_end_curvature_and_unmarked_example
