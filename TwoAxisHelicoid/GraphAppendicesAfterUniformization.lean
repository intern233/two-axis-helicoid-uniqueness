import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.AnnularOriginalClassification
import TwoAxisHelicoid.OriginalGraphAppendices
import TwoAxisHelicoid.FlatTorusCanonicalDifferential

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

universe u

/-- Each compact genus-one complex structure has a nonzero holomorphic
differential, and its canonical divisor is trivial in the marked sense
used for the cap. -/
theorem genus_one_differential_existence_proved : GenusOneHasHolomorphicDifferential.{u} :=
  genus_one_holomorphic_differential_from_annuli annular_riemann_surface_uniformization_proved

/-- The original graph-surface endpoint gap and finiteness in the real
spatial quotient use analytic endpoint estimates and zero isolation. -/
theorem graph_appendix_B_without_uniformization_input :
    (∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have present (s : OriginalHelicoidRepresentative) :
      ∃ W∈positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
    obtain ⟨A⟩ := (original_annular_end_pole_model_and_index s annular_riemann_surface_uniformization_proved).1
    exact positional_poles_give_positive_pitch_representative s.toPositional A
      (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _) marked_rhombic_helicoid_intersection
  constructor
  · intro s
    obtain ⟨W,hW,rel⟩ := present s
    exact ⟨W,hW,analytic_pitch_height_gap W,rel⟩
  · apply analytic_pitch_class_finiteness.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,_,rel⟩ := present s
    exact ⟨W,(Quotient.sound rel).symm⟩

/-- For the original weak positional class the same conclusions of
B and the real infinite-index conclusion of D use the rough physical
curvature bound, independently of embedded existence. -/
theorem positional_B_and_D_from_end_curvature
    (curvature : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, HasInfiniteRealSurfaceMorseIndex s.position) := by
  let g := fun s : OriginalPositionallyAsymptoticHelicoid => s.graphRepresentative (curvature s)
  obtain ⟨gap,fin⟩ := graph_appendix_B_without_uniformization_input
  refine ⟨fun s => gap (g s),fin.subset ?_,fun s =>
    (original_annular_end_pole_model_and_index (g s) annular_riemann_surface_uniformization_proved).2⟩
  rintro x ⟨s,rfl⟩
  exact ⟨g s,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_appendix_B_without_uniformization_input
#print axioms TwoAxisHelicoid.positional_B_and_D_from_end_curvature
