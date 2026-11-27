import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.OriginalAnnularEndConsequences
import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.PositionalUnmarkedFluxCompactness

namespace TwoAxisHelicoid
open Set Topology

/-- Put a graph-ended physical candidate in the positively normalized
pitch class using the actual end and the integer branch. This construction
precedes counting or locating the horizontal period roots. -/
theorem graph_surface_has_positive_pitch_model (s : OriginalHelicoidRepresentative) :
    ∃ W∈positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
  obtain ⟨poles⟩ := (original_annular_end_pole_model_and_index s annular_riemann_surface_uniformization_proved).1
  exact positional_poles_give_positive_pitch_representative s.toPositional poles
    (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _)
    marked_rhombic_helicoid_intersection

/-- The flux-and-compactness proof of B.1 and B.2 on the geometric class
of the manuscript. It includes the actual two transported generating curves
with uniform derivative convergence on their full compact intervals. The
external input is compactness of the fixed-axis class at the screw cutoffs. -/
theorem original_graph_B_from_cutoff_compactness {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have loops := unmarked_cutoffs_give_smooth_generating_curves family compact
  obtain ⟨ε,positive,gap⟩ := core_compactness_implies_uniform_parameter_gap
    (smooth_generating_curves_give_subsequential_bounded_cores loops)
  have finite := smooth_generating_core_finite_similarity_classes loops
  refine ⟨loops,⟨ε,positive,?_,?_⟩,finite.subset ?_⟩
  · intro W hW
    obtain ⟨U,hU,eq,_⟩ := positive_pitch_representative W hW
    exact eq ▸ gap U hU
  · intro s
    obtain ⟨W,hW,rel⟩ := graph_surface_has_positive_pitch_model s
    exact ⟨W,hW,gap W hW,rel⟩
  · rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,rel⟩ := graph_surface_has_positive_pitch_model s
    exact ⟨W,hW,(Quotient.sound rel).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_surface_has_positive_pitch_model
#print axioms TwoAxisHelicoid.original_graph_B_from_cutoff_compactness
