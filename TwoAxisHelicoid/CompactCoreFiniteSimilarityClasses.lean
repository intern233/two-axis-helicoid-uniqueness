import TwoAxisHelicoid.SmoothGeneratingCoreTransfer
import TwoAxisHelicoid.SpatialSimilarityClasses

namespace TwoAxisHelicoid
open Set

noncomputable def PitchNormalizedBasicImmersion.image (X : PitchNormalizedBasicImmersion) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  (coordinateToEuclidean ∘ X.position) '' ((rhombicPeriodPair X.t X.ht).lattice : Set ℂ)ᶜ

private theorem pitch_normalized_coefficient_ne_zero (X : PitchNormalizedBasicImmersion) : X.c ≠ 0 := by
  intro he
  have hs := X.scale
  rw [he,abs_zero] at hs
  linarith [(verticalA_spec ⟨X.ht,X.hT⟩).1.2]

/-- Equal marked heights determine the actual complete geometric image up
to positive-ratio similarity; both signs of the real coefficient are allowed. -/
theorem pitch_normalized_images_similar_of_equal_height (X Y : PitchNormalizedBasicImmersion)
    (he : X.t = Y.t) : (spatialSimilaritySetoid _).r X.image Y.image := by
  have hy : HasTwoAxisHelicoidCoordinateDifferential Y.position X.t (verticalA X.t) Y.c X.ht :=
    by simpa only [he] using Y.differential
  obtain ⟨b,hb⟩ := actual_coordinate_primitives_unique_up_to_scale_translation X.ht
    (pitch_normalized_coefficient_ne_zero X) X.differential hy
  let r := Y.c/X.c
  have hr : r ≠ 0 := div_ne_zero (pitch_normalized_coefficient_ne_zero Y) (pitch_normalized_coefficient_ne_zero X)
  refine ⟨DilationEquiv.smulTorsor (coordinateToEuclidean b) hr,?_⟩
  have e (z : ℂ) (hz : z ∉ (rhombicPeriodPair X.t X.ht).lattice) :
      coordinateToEuclidean (Y.position z) = r • coordinateToEuclidean (X.position z)+coordinateToEuclidean b := by
    rw [hb z hz,map_add,map_smul]
  have hdom : ((rhombicPeriodPair Y.t Y.ht).lattice : Set ℂ)ᶜ = ((rhombicPeriodPair X.t X.ht).lattice : Set ℂ)ᶜ := by simp only [he]
  unfold PitchNormalizedBasicImmersion.image
  rw [hdom,image_image]
  apply image_congr
  exact fun z hz => (e z hz).symm

/-- Appendix B.2 in the actual quotient of Euclidean surface images, from
smooth generating-core compactness and the analytic right-end limit. -/
theorem smooth_generating_core_finite_similarity_classes {S : Set PitchNormalizedBasicImmersion}
    (hS : HasSubsequentialSmoothGeneratingCurves S) :
    ((fun X : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) X.image) '' S).Finite := by
  classical
  let c := fun t : ℝ => if h : ∃ X ∈ S, X.t = t then
    Quotient.mk (spatialSimilaritySetoid _) h.choose.image else Quotient.mk (spatialSimilaritySetoid _) ∅
  have hfin := core_compactness_implies_finite_parameters (smooth_generating_curves_give_subsequential_bounded_cores hS)
  apply (hfin.image c).subset
  rintro _ ⟨X,hX,rfl⟩
  have h : ∃ Z ∈ S, Z.t = X.t := ⟨X,hX,rfl⟩
  refine ⟨X.t,⟨X,hX,rfl⟩,?_⟩
  simp only [c,dite_eq_left h]
  exact Quotient.sound (pitch_normalized_images_similar_of_equal_height h.choose X h.choose_spec.2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_generating_core_finite_similarity_classes
