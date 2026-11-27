import TwoAxisHelicoid.UnmarkedGeneratingCurveCompactness
import TwoAxisHelicoid.PositionalAppendixBCompactness
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem
import TwoAxisHelicoid.FiniteTopologyEndConsequences
import TwoAxisHelicoid.GenusOneHolomorphicFormExistence

namespace TwoAxisHelicoid
open Set

/-- A uniform flux gap and finiteness for the full positional class.
Only the original surfaces are put in period coordinates. The cutoff
limit in the flux proof is treated in its intrinsic real smooth atlas. -/
theorem positional_flux_gap_and_finiteness_from_unmarked_cores {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs)
    (represent : ∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily,
      (spatialSimilaritySetoid _).r s.image W.image) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  obtain ⟨⟨ε,ep,gap⟩,finite⟩ := normalized_flux_gap_and_finiteness_of_unmarked_cutoffs family compact
  constructor
  · refine ⟨ε,ep,?_,?_⟩
    · intro W hW
      obtain ⟨V,hV,eq,_⟩ := positive_pitch_representative W hW
      exact eq ▸ gap V hV
    · intro s
      obtain ⟨W,hW,same⟩ := represent s
      exact ⟨W,hW,gap W hW,same⟩
  · apply finite.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,same⟩ := represent s
    exact ⟨W,hW,(Quotient.sound same).symm⟩

/-- Manuscript B.1/B.2 from finite-topology end data, one
holomorphic differential on genus one, and compactness of the
actual fixed-axis surfaces at every positive screw cutoff. -/
theorem positional_appendix_B_from_unmarked_geometric_compactness {I : Type*}
    (bbc : PublishedFiniteOneEndDifferentialGeometry) (form : GenusOneHasHolomorphicDifferential.{0})
    (family : FixedAxisHelicoidNormalClass I) (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  apply positional_flux_gap_and_finiteness_from_unmarked_cores family compact
  intro s
  obtain ⟨poles⟩ := classical_finite_topology_gives_published_one_handle_model bbc s.toOriginalSmoothHelicoid
    s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  exact positional_poles_give_positive_pitch_representative s poles
    (genus_one_uniformization_of_holomorphic_differential form _) marked_rhombic_helicoid_intersection

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_flux_gap_and_finiteness_from_unmarked_cores
#print axioms TwoAxisHelicoid.positional_appendix_B_from_unmarked_geometric_compactness
