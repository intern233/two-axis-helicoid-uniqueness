import TwoAxisHelicoid.PlacedHelicoidFrame
import TwoAxisHelicoid.OriginalManuscriptPublishedInputs

namespace TwoAxisHelicoid
open Complex Set Topology

theorem PlacedPositionalHelicoid.image_equivalent_normalized (s : PlacedPositionalHelicoid) :
    (spatialSimilaritySetoid _).r s.image s.normalized.image := by
  refine ⟨s.frame.isometry.toDilationEquiv,?_⟩
  change s.frame.isometry '' range (coordinateToEuclidean ∘ s.position) =
    range (fun x => coordinateToEuclidean (s.frame.homeo (s.position x)))
  rw [← range_comp]
  rfl

/-- The quotient represented by surfaces in arbitrary physical positions
equals the quotient represented by the axis-normalized class. -/
theorem placed_class_iff_original (c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
    (∃ s : PlacedPositionalHelicoid, Quotient.mk _ s.image = c) ↔
    (∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk _ s.image = c) := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s.normalized,(Quotient.sound s.image_equivalent_normalized).symm⟩
  · rintro ⟨s,rfl⟩
    exact ⟨s.placed,rfl⟩

/-- Theorem 1.1 for the geometric images in their given Euclidean
positions. The origin, direction and phase of the reference helicoid
are unrestricted, and the physical position itself has zero mean
curvature. Its quotient class is that of the certified immersion. -/
theorem placed_manuscript_main_of_published_inputs (mp : PublishedFiniteTopologyGaussianCurvature)
    (poi : SimplyConnectedNoncompactUniformization.{0}) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, HasCertifiedPointedNormalization s.normalized.toOriginalSmoothHelicoid ∧
        HasOriginalPointedGaussDivisor s.normalized.toOriginalSmoothHelicoid) := by
  obtain ⟨⟨c,w,unique⟩,model,embedding,normalized,_⟩ := original_manuscript_main_of_published_inputs mp poi whw
  exact ⟨⟨c,(placed_class_iff_original c).mpr w,fun y hy => unique y ((placed_class_iff_original y).mp hy)⟩,
    (placed_class_iff_original _).mpr model,embedding,fun s => normalized s.normalized⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.placed_class_iff_original
#print axioms TwoAxisHelicoid.placed_manuscript_main_of_published_inputs
