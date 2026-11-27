import TwoAxisHelicoid.OriginalPointedModel
import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.SpatialSimilarityClasses

namespace TwoAxisHelicoid
open Set Topology InnerProductSpace

/-- The pointwise comparison of every original surface with the same marked
model identifies its similarity class. A single original embedded example
then transfers global embeddedness to the model. -/
theorem positional_classification_of_pointed_models
    (normal : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid)
    (existsSurface : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let represented := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image = c
    (∃! c, represented c) ∧ represented (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion := by
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  have similar (s : OriginalPositionallyAsymptoticHelicoid) : Q.r s.image (range certifiedTorusImmersion) := by
    obtain ⟨_,_,_,U,k,E,b,_,_,hk,h,_⟩ := normal s
    exact image_similarity_of_surjective_parameters s.euclideanPosition certifiedTorusImmersion U U.surjective k E b hk h
  obtain ⟨s⟩ := existsSurface
  refine ⟨unique_spatial_image_class_of_common_model (fun t : OriginalPositionallyAsymptoticHelicoid => t.image)
    (range certifiedTorusImmersion) ⟨s⟩ similar,⟨s,Quotient.sound (similar s)⟩,?_⟩
  obtain ⟨_,_,_,U,k,E,b,_,_,hk,h,_⟩ := normal s
  let F := E.toDilationEquiv.trans (DilationEquiv.smulTorsor b hk.ne')
  have he : certifiedTorusImmersion = F ∘ s.euclideanPosition ∘ U.symm := by
    funext q
    change certifiedTorusImmersion q = k • E (s.euclideanPosition (U.symm q))+b
    simpa only [U.apply_symm_apply] using h (U.symm q)
  rw [he]
  exact F.toHomeomorph.isClosedEmbedding.comp (((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding).comp U.symm.isClosedEmbedding)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_classification_of_pointed_models
