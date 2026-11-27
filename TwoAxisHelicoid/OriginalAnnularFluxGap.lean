import TwoAxisHelicoid.AnnularOriginalClassification
import TwoAxisHelicoid.PositionalUnmarkedFluxCompactness

namespace TwoAxisHelicoid
open Set Topology

/-- For Appendix B the meromorphic end model can be derived separately
for each positionally asymptotic candidate from its physical curvature
bound at infinity. The unmarked limit needs neither bound nor marking. -/
theorem positional_flux_gap_from_annuli_and_compactness {I : Type*}
    (ann : AnnularRiemannSurfaceUniformization.{0})
    (shape : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid)
    (family : FixedAxisHelicoidNormalClass I) (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  apply positional_flux_gap_and_finiteness_from_unmarked_cores family compact
  intro s
  obtain ⟨P,_⟩ := original_annular_end_pole_model_and_index (s.graphRepresentative (shape s)) ann
  exact positional_poles_give_positive_pitch_representative s P.some
    (compact_genus_one_uniformization_of_annular_classification ann _) marked_rhombic_helicoid_intersection

/-- Both conclusions of Appendix B in the graph class use only the
annular classification and fixed-axis geometric compactness. The
generating loops and their flux bounds are obtained before the analytic
finite-zero argument. -/
theorem graph_flux_gap_from_annuli_and_compactness {I : Type*}
    (ann : AnnularRiemannSurfaceUniformization.{0})
    (family : FixedAxisHelicoidNormalClass I) (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧ ∀ s : OriginalHelicoidRepresentative,
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have rep (s : OriginalHelicoidRepresentative) :=
    positional_poles_give_positive_pitch_representative s.toPositional
      (original_annular_end_pole_model_and_index s ann).1.some
      (compact_genus_one_uniformization_of_annular_classification ann _) marked_rhombic_helicoid_intersection
  obtain ⟨⟨ε,hε,lb⟩,finite⟩ := normalized_flux_gap_and_finiteness_of_unmarked_cutoffs family compact
  constructor
  · refine ⟨ε,hε,?_,?_⟩
    · intro W hW
      obtain ⟨T,hT,ht,_⟩ := positive_pitch_representative W hW
      exact ht ▸ lb T hT
    · intro s
      obtain ⟨T,hT,h⟩ := rep s
      exact ⟨T,hT,lb T hT,h⟩
  · apply finite.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨T,hT,h⟩ := rep s
    exact ⟨T,hT,(Quotient.sound h).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_flux_gap_from_annuli_and_compactness
#print axioms TwoAxisHelicoid.graph_flux_gap_from_annuli_and_compactness
