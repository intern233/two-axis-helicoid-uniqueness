import TwoAxisHelicoid.ManuscriptGraphRepresentedClasses
import TwoAxisHelicoid.PlacedHelicoidFrame

namespace TwoAxisHelicoid
open Set Topology

/-- A physical position and its own helicoid frame realize this image class. -/
def PlacedManuscriptC1ImageClass
    (d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) : Prop :=
  ∃ s : PlacedPositionalHelicoid,
    HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
      s.frame.homeo ∘ s.position) ∧ Quotient.mk _ s.image = d

/-- The inverse frame of a physical surface identifies the two images as sets. -/
theorem manuscript_inverse_frame_image (s : PlacedPositionalHelicoid) :
    s.frame.isometry.symm '' s.normalized.image = s.image := by
  have forward : s.frame.isometry '' s.image = s.normalized.image := by
    change s.frame.isometry '' range (coordinateToEuclidean ∘ s.position) =
      range (fun x => coordinateToEuclidean (s.frame.homeo (s.position x)))
    rw [← range_comp]
    rfl
  rw [← forward]
  exact s.frame.isometry.toEquiv.symm_image_image s.image

/-- A quotient class represented by an isometric placement of a manuscript
surface is precisely a class represented by a physical candidate. -/
theorem manuscript_C1_placed_image_class_iff
    (d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
    (∃ (s : ManuscriptC1Surface) (U : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
      Quotient.mk (spatialSimilaritySetoid _) (U '' s.1.image) = d) ↔ PlacedManuscriptC1ImageClass d := by
  constructor
  · intro represented
    obtain ⟨s,eq⟩ := (manuscript_C1_represented_class_iff d).mpr represented
    refine ⟨s.toPositional.placed,?_,eq⟩
    change HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘
      HelicoidSpatialFrame.standard.homeo ∘ s.position)
    rw [show (HelicoidSpatialFrame.standard.homeo : (Fin 3 → ℝ) → (Fin 3 → ℝ)) = id from
      funext HelicoidSpatialFrame.standard_apply,Function.id_comp]
    exact (original_compact_complement_C1_graph_iff _).mpr s.graphEnd
  · rintro ⟨s,graph,eq⟩
    let v : ManuscriptC1Surface := ⟨s.normalized.toOriginalSmoothHelicoid,graph⟩
    refine ⟨v,s.frame.isometry.symm,?_⟩
    change Quotient.mk (spatialSimilaritySetoid _) (s.frame.isometry.symm '' s.normalized.image) = d
    rw [manuscript_inverse_frame_image]
    exact eq

def PlacedManuscriptC1UniqueImageClass : Prop := ∃! d, PlacedManuscriptC1ImageClass d

theorem placed_manuscript_C1_unique_class_of_normalized (h : ManuscriptC1UniqueImageClass) :
    PlacedManuscriptC1UniqueImageClass := by
  obtain ⟨d,rep,only⟩ := h
  exact ⟨d,(manuscript_C1_placed_image_class_iff d).mp rep,
    fun c hc => only c ((manuscript_C1_placed_image_class_iff c).mpr hc)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_inverse_frame_image
#print axioms TwoAxisHelicoid.manuscript_C1_placed_image_class_iff
#print axioms TwoAxisHelicoid.placed_manuscript_C1_unique_class_of_normalized
