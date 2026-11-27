import TwoAxisHelicoid.OriginalGraphPoleModel
import TwoAxisHelicoid.PositionalAppendixBEndpoints
import TwoAxisHelicoid.PublishedPoleSurfaceMorseIndex

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- Appendix B.1 and B.2 for original helicoidal C¹ graphs. Only the
endpoint estimates and analyticity of the period are needed after
constructing the actual conformal marking. -/
theorem original_graph_appendix_B (uni : SimplyConnectedNoncompactUniformization.{0}) :
    (∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have present (s : OriginalHelicoidRepresentative) :
      ∃ W∈positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
    obtain ⟨A⟩ := original_graph_independent_conformal_pole_model s uni
    exact positional_poles_give_positive_pitch_representative s.toPositional A
      (compact_genus_one_uniformization_of_classical uni _) marked_rhombic_helicoid_intersection
  constructor
  · intro s
    obtain ⟨W,hW,rel⟩ := present s
    exact ⟨W,hW,analytic_pitch_height_gap W,rel⟩
  · apply analytic_pitch_class_finiteness.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,_,rel⟩ := present s
    exact ⟨W,(Quotient.sound rel).symm⟩

/-- The negative spaces of genuine compactly supported normal variations
on the original graph surface have arbitrarily large dimension. -/
theorem original_graph_infinite_morse_index (s : OriginalHelicoidRepresentative)
    (uni : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
      (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position := by
  obtain ⟨A⟩ := original_graph_independent_conformal_pole_model s uni
  exact original_smooth_published_poles_infinite_morse_index s.toOriginalSmoothHelicoid
    (compact_genus_one_uniformization_of_classical uni _) A s.positional.1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_appendix_B
#print axioms TwoAxisHelicoid.original_graph_infinite_morse_index
