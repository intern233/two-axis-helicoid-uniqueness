import TwoAxisHelicoid.FixedAxisAnalyticGeneratingCores
import TwoAxisHelicoid.OriginalCompactCoreFluxGap
import TwoAxisHelicoid.PlacedGraphPointedConclusion

namespace TwoAxisHelicoid
open Set Topology

/-- Appendix B for the physical graph-ended class. Analytic endpoint signs give
a stationary subsequence of normalized maps. Its actual generating curves
then supply the bounded lengths in the flux proof of the parameter gap.
The result applies to the spatial images in their original placements. -/
theorem placed_graph_B_from_stationary_generating_curves :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (PitchNormalizedBasicImmersion.image '' positiveUnitPitchFamily).Finite ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : PlacedGraphHelicoid, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧
        (spatialSimilaritySetoid _).r s.1.image W.image) ∧
    (range (fun s : PlacedGraphHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.1.image)).Finite := by
  have loops := fixed_axis_analytic_smooth_generating_curves
  obtain ⟨ε,ep,gap⟩ := core_compactness_implies_uniform_parameter_gap
    (smooth_generating_curves_give_subsequential_bounded_cores loops)
  have model (s : PlacedGraphHelicoid) :
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.1.image W.image := by
    obtain ⟨W,hW,rel⟩ := graph_surface_has_positive_pitch_model s.normalizedGraph
    exact ⟨W,hW,gap W hW,(spatialSimilaritySetoid _).trans s.1.image_equivalent_normalized rel⟩
  refine ⟨loops,fixed_axis_positive_pitch_finite_images,⟨ε,ep,?_,model⟩,?_⟩
  · intro W hW
    obtain ⟨U,hU,eq,_⟩ := positive_pitch_representative W hW
    exact eq ▸ gap U hU
  · apply (smooth_generating_core_finite_similarity_classes loops).subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,_,rel⟩ := model s
    exact ⟨W,hW,(Quotient.sound rel).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_graph_B_from_stationary_generating_curves
