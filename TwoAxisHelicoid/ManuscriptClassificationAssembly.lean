import TwoAxisHelicoid.ManuscriptCertifiedImageGeometry
import TwoAxisHelicoid.ManuscriptPlacedImageClasses
import TwoAxisHelicoid.ManuscriptC1PredicateTransport

namespace TwoAxisHelicoid
open Set Topology

/-- Both presentations of Section 2, on the same certified embedded model.
The marking predicate is kept as an argument so the individual geometric
proofs can be checked separately. -/
def ManuscriptClassificationWithMarking (P : OriginalPositionallyAsymptoticHelicoid → Prop) : Prop :=
  let E := EuclideanSpace ℝ (Fin 3)
  let Q := spatialSimilaritySetoid E
  let M := range certifiedTorusImmersion
  ManuscriptCertifiedImageGeometry ∧ PlacedManuscriptC1UniqueImageClass ∧
    PlacedManuscriptC1ImageClass (Quotient.mk Q M) ∧
    (∀ s : PlacedPositionalHelicoid,
      HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
        s.frame.homeo ∘ s.position) → ∃ (k : ℝ) (f : E ≃ᵢ E), 0 < k ∧ (fun v => k • f v) '' s.image = M) ∧
    AllManuscriptC1Surfaces P ∧ AllPlacedManuscriptC1Surfaces P

theorem manuscript_classification_of_geometry_and_markings
    (P : OriginalPositionallyAsymptoticHelicoid → Prop) (geometry : ManuscriptCertifiedImageGeometry)
    (normalized : AllManuscriptC1Surfaces P) (placed : AllPlacedManuscriptC1Surfaces P) :
    ManuscriptClassificationWithMarking P := by
  refine ⟨geometry,placed_manuscript_C1_unique_class_of_normalized geometry.1,
    (manuscript_C1_placed_image_class_iff _).mp geometry.2.1,?_,normalized,placed⟩
  intro s graph
  let v : ManuscriptC1Surface := ⟨s.normalized.toOriginalSmoothHelicoid,graph⟩
  have h := geometry.2.2.1 v s.frame.isometry.symm
  change ∃ (k : ℝ) (f : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
    0 < k ∧ (fun x => k • f x) '' (s.frame.isometry.symm '' s.normalized.image) =
      range certifiedTorusImmersion at h
  rwa [manuscript_inverse_frame_image] at h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_classification_of_geometry_and_markings
