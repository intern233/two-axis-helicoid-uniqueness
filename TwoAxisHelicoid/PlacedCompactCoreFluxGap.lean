import TwoAxisHelicoid.OriginalCompactCoreFluxGap
import TwoAxisHelicoid.PositionalCurvatureFromDiskEstimate
import TwoAxisHelicoid.PlacedGraphPointedConclusion

namespace TwoAxisHelicoid
open Set Topology

/-- Undo the axis and pitch placement after transporting the generating
curves in the Hoffman--White class. Both the parameter gap and finiteness
hold in the quotient of the original spatial images. -/
theorem placed_graph_B_by_flux_transport {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : PlacedGraphHelicoid, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧
        (spatialSimilaritySetoid _).r s.1.image W.image) ∧
    (range (fun s : PlacedGraphHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.1.image)).Finite := by
  obtain ⟨_,⟨ε,ep,gap,g⟩,finite⟩ := original_graph_B_from_cutoff_compactness family compact
  refine ⟨⟨ε,ep,gap,?_⟩,finite.subset ?_⟩
  · intro s
    obtain ⟨W,hW,low,rel⟩ := g s.normalizedGraph
    exact ⟨W,hW,low,(spatialSimilaritySetoid _).trans s.1.image_equivalent_normalized rel⟩
  · rintro c ⟨s,eq⟩
    exact (graph_placed_class_iff_original c).mp ⟨s,eq⟩

/-- With merely positional ends the one-sided disk curvature estimate
puts the same physical surface in the graph class before applying the
compactness and flux argument. No example of a surface is required. -/
theorem placed_positional_B_by_flux_transport {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs) (cm : OneSidedEmbeddedMinimalDiskEstimate) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : PlacedPositionalHelicoid, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : PlacedPositionalHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  obtain ⟨_,⟨ε,ep,gap,g⟩,finite⟩ := original_graph_B_from_cutoff_compactness family compact
  let G := fun s : PlacedPositionalHelicoid => s.normalized.graphRepresentative (positional_end_curvature_from_disk_estimate cm s.normalized)
  refine ⟨⟨ε,ep,gap,?_⟩,finite.subset ?_⟩
  · intro s
    obtain ⟨W,hW,low,rel⟩ := g (G s)
    exact ⟨W,hW,low,(spatialSimilaritySetoid _).trans s.image_equivalent_normalized rel⟩
  · rintro _ ⟨s,rfl⟩
    exact ⟨G s,(Quotient.sound s.image_equivalent_normalized).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_graph_B_by_flux_transport
#print axioms TwoAxisHelicoid.placed_positional_B_by_flux_transport
