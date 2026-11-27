import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.OriginalAnnularEndConsequences
import TwoAxisHelicoid.FiniteTopologyManuscriptConclusion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- A single classification of annuli supplies both the physical end
coordinate and the actual marked compact torus of each graph surface. -/
theorem graph_cap_normalization_and_index_from_annuli (ann : AnnularRiemannSurfaceUniformization.{0})
    (s : OriginalHelicoidRepresentative) :
    HasPointedOriginalSpinBranchCap s.toPositional ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid ∧ HasInfiniteRealSurfaceMorseIndex s.position := by
  obtain ⟨poles,index⟩ := original_annular_end_pole_model_and_index s ann
  have cap := original_pointed_spin_cap_of_torus_uniformization s.toPositional poles.some
    (compact_genus_one_uniformization_of_annular_classification ann _)
  have normal := (pointed_spin_cap_certifies_original s.toPositional cap).2
  exact ⟨cap,normal,original_pointed_gauss_divisor_of_normalization _ normal,index⟩

/-- Any one physically embedded representative with the certified
pointed normalization gives a closed embedding of the certified map
and identifies the whole image up to a positive similarity. -/
theorem pointed_original_embedding_and_similarity (s : OriginalSmoothHelicoid)
    (normal : HasCertifiedPointedNormalization s) :
    IsClosedEmbedding certifiedTorusImmersion ∧
      (spatialSimilaritySetoid _).r s.image (range certifiedTorusImmersion) := by
  obtain ⟨_,_,_,U,k,E,b,_,_,hk,h,_⟩ := normal
  let F := E.toDilationEquiv.trans (DilationEquiv.smulTorsor b hk.ne')
  have eq : certifiedTorusImmersion=F ∘ s.euclideanPosition ∘ U.symm := by
    funext q
    change certifiedTorusImmersion q=k • E (s.euclideanPosition (U.symm q))+b
    simpa only [U.apply_symm_apply] using h (U.symm q)
  refine ⟨?_,image_similarity_of_surjective_parameters s.euclideanPosition certifiedTorusImmersion U U.surjective k E b hk h⟩
  rw [eq]
  exact F.toHomeomorph.isClosedEmbedding.comp (((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding).comp U.symm.isClosedEmbedding)

/-- Uniqueness in the original full graph class from the annular
classification and one unmarked embedded example. -/
theorem graph_unique_class_from_annuli (ann : AnnularRiemannSurfaceUniformization.{0})
    (existsSurface : Nonempty OriginalHelicoidRepresentative) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧ IsClosedEmbedding certifiedTorusImmersion := by
  obtain ⟨s⟩ := existsSurface
  have image (t : OriginalHelicoidRepresentative) := pointed_original_embedding_and_similarity t.toOriginalSmoothHelicoid
    (graph_cap_normalization_and_index_from_annuli ann t).2.1
  exact ⟨unique_spatial_image_class_of_common_model (fun t : OriginalHelicoidRepresentative => t.image)
    (range certifiedTorusImmersion) ⟨s⟩ (fun t => (image t).2),⟨s,Quotient.sound (image s).2⟩,(image s).1⟩

/-- For the weaker original positional asymptotics the curvature
bound first supplies a graph. End and handle uniformization then use
only annuli. The same pointed cap computes the integer branch,
Gauss divisor and genuine compactly supported real index. -/
theorem positional_cap_normalization_and_index_from_annuli (bound : FiniteTopologyGaussianCurvatureBound)
    (ann : AnnularRiemannSurfaceUniformization.{0}) (s : OriginalPositionallyAsymptoticHelicoid) :
    HasPointedOriginalSpinBranchCap s ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid ∧ HasInfiniteRealSurfaceMorseIndex s.position := by
  obtain ⟨C,non,curv⟩ := bound s.toOriginalSmoothHelicoid
  exact graph_cap_normalization_and_index_from_annuli ann
    (s.graphRepresentative (original_physical_shape_bound_of_gaussian _ non curv))

theorem positional_unique_class_from_curvature_and_annuli (bound : FiniteTopologyGaussianCurvatureBound)
    (ann : AnnularRiemannSurfaceUniformization.{0}) (existsSurface : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧ IsClosedEmbedding certifiedTorusImmersion :=
  positional_classification_of_pointed_models (fun s => (positional_cap_normalization_and_index_from_annuli bound ann s).2.1) existsSurface

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_cap_normalization_and_index_from_annuli
#print axioms TwoAxisHelicoid.graph_unique_class_from_annuli
#print axioms TwoAxisHelicoid.positional_unique_class_from_curvature_and_annuli
