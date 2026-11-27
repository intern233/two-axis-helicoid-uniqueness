import TwoAxisHelicoid.PositionalAppendixBCompactness
import TwoAxisHelicoid.AnalyticPitchClassFiniteness
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem

namespace TwoAxisHelicoid
open Set

/-- The analytic estimates at the two ends of the parameter interval
give the height gap and the finite number of similarity classes for the
original positional surface class. No compact-interval box estimates or
geometric convergence theorem enter this proof. -/
theorem positional_appendix_B_from_analytic_endpoints (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) :
    (∀ W ∈ embeddedPitchFamily, 1/8 < W.t) ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W ∈ positiveUnitPitchFamily, 1/8 < W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have present (s : OriginalPositionallyAsymptoticHelicoid) :
      ∃ W ∈ positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
    obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact positional_poles_give_positive_pitch_representative s A
      (compact_genus_one_uniformization_of_classical poincare _) marked_rhombic_helicoid_intersection
  refine ⟨fun W _ => analytic_pitch_height_gap W,?_,?_⟩
  · intro s
    obtain ⟨W,hW,hS⟩ := present s
    exact ⟨W,hW,analytic_pitch_height_gap W,hS⟩
  · apply analytic_pitch_class_finiteness.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,_,hS⟩ := present s
    exact ⟨W,(Quotient.sound hS).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_appendix_B_from_analytic_endpoints
