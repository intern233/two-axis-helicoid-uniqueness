import TwoAxisHelicoid.ManuscriptGraphOffCompact
import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.SpatialSimilarityClasses

namespace TwoAxisHelicoid
open Set Topology

def OriginalSmoothHelicoid.HasManuscriptGraph (s : OriginalSmoothHelicoid) : Prop :=
  HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘
    s.position)

abbrev ManuscriptC1Surface := {s : OriginalSmoothHelicoid // s.HasManuscriptGraph}

def ManuscriptC1Surface.graphRepresentative (s : ManuscriptC1Surface) : OriginalHelicoidRepresentative :=
  {s.1 with graphEnd := (original_compact_complement_C1_graph_iff s.1).mp s.2}

/-- Conversion between the two presentations preserves the whole underlying
surface, including its position, axes, and initial real atlas. -/
def manuscriptC1SurfaceEquiv : ManuscriptC1Surface ≃ OriginalHelicoidRepresentative where
  toFun := ManuscriptC1Surface.graphRepresentative
  invFun s := ⟨s.toOriginalSmoothHelicoid,(original_compact_complement_C1_graph_iff _).mpr s.graphEnd⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- The set of represented similarity classes agrees exactly, even when
every manuscript candidate may be placed by an arbitrary ambient isometry. -/
theorem manuscript_C1_represented_class_iff
    (d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
    (∃ s : OriginalHelicoidRepresentative, Quotient.mk _ s.image = d) ↔
      ∃ (s : ManuscriptC1Surface) (U : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
        Quotient.mk (spatialSimilaritySetoid _) (U '' s.1.image) = d := by
  let E := EuclideanSpace ℝ (Fin 3)
  let Q := spatialSimilaritySetoid E
  have placement (X : Set E) (U : E ≃ᵢ E) :
      Quotient.mk Q X = Quotient.mk Q (U '' X) :=
    Quotient.sound (show Q.r X (U '' X) from ⟨U.toDilationEquiv,rfl⟩)
  constructor
  · rintro ⟨s,eq⟩
    let t := manuscriptC1SurfaceEquiv.symm s
    exact ⟨t,IsometryEquiv.refl E,(placement t.1.image _).symm.trans eq⟩
  · rintro ⟨s,U,eq⟩
    exact ⟨s.graphRepresentative,(placement s.1.image U).trans eq⟩

/-- Exactly one similarity class of physical images of the manuscript candidates. -/
def ManuscriptC1UniqueImageClass : Prop :=
  let E := EuclideanSpace ℝ (Fin 3)
  let Q := spatialSimilaritySetoid E
  ∃! d : Quotient Q, ∃ (s : ManuscriptC1Surface) (U : E ≃ᵢ E), Quotient.mk Q (U '' s.1.image) = d

theorem manuscript_C1_unique_class_of_original
    (original : ∃! d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ s : OriginalHelicoidRepresentative, Quotient.mk _ s.image = d) :
    ManuscriptC1UniqueImageClass := by
  obtain ⟨c,represented,only⟩ := original
  exact ⟨c,(manuscript_C1_represented_class_iff c).mp represented,
    fun d hd => only d ((manuscript_C1_represented_class_iff d).mpr hd)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscriptC1SurfaceEquiv
#print axioms TwoAxisHelicoid.manuscript_C1_represented_class_iff

#print axioms TwoAxisHelicoid.manuscript_C1_unique_class_of_original
