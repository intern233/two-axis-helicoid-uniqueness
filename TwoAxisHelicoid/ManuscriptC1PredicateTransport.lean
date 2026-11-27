import TwoAxisHelicoid.ManuscriptGraphRepresentedClasses
import TwoAxisHelicoid.PlacedHelicoidFrame

namespace TwoAxisHelicoid

def AllManuscriptC1Surfaces (P : OriginalPositionallyAsymptoticHelicoid → Prop) : Prop :=
  ∀ s : ManuscriptC1Surface, P s.graphRepresentative.toPositional

def AllPlacedManuscriptC1Surfaces (P : OriginalPositionallyAsymptoticHelicoid → Prop) : Prop :=
  ∀ s : PlacedPositionalHelicoid,
    HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
      s.frame.homeo ∘ s.position) → P s.normalized

/-- A property of the same normalized surface transfers to both physical
presentations when the single C¹ graph is given outside arbitrary compact sets. -/
theorem original_property_of_all_manuscript_C1_surfaces
    (P : OriginalPositionallyAsymptoticHelicoid → Prop)
    (all : ∀ o : OriginalHelicoidRepresentative, P o.toPositional) :
    AllManuscriptC1Surfaces P ∧ AllPlacedManuscriptC1Surfaces P := by
  constructor
  · exact fun s => all s.graphRepresentative
  · intro s graph
    let o : OriginalHelicoidRepresentative := {
      s.normalized.toOriginalSmoothHelicoid with
      graphEnd := (original_compact_complement_C1_graph_iff s.normalized.toOriginalSmoothHelicoid).mp graph }
    exact all o

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_property_of_all_manuscript_C1_surfaces
