import TwoAxisHelicoid.EmbeddedPitchPhysicalRepresentative
import TwoAxisHelicoid.OriginalPitchNormalization

namespace TwoAxisHelicoid
open Set

/-- With the standard `2(a-1)/c` convention, positive pitch means a
negative height parameter. -/
def positiveUnitPitchFamily : Set PitchNormalizedBasicImmersion := {W | W ∈ embeddedPitchFamily ∧ W.c < 0}

/-- Central reflection exchanges the two signs of the pitch while
preserving height modulus, the marked axes and embeddedness. -/
theorem positive_pitch_representative (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily) :
    ∃ V ∈ positiveUnitPitchFamily, V.t = W.t ∧ (spatialSimilaritySetoid _).r W.image V.image := by
  by_cases hn : W.c < 0
  · exact ⟨W,⟨hW,hn⟩,rfl,(spatialSimilaritySetoid _).refl _⟩
  have ha := (verticalA_spec ⟨W.ht,W.hT⟩).1.2
  have hp : 0 < W.c := by
    have e := W.scale
    rw [abs_of_nonneg (le_of_not_gt hn)] at e
    linarith
  let k := (-1:ℝ)
  have hk : k ≠ 0 := by norm_num [k]
  let V : PitchNormalizedBasicImmersion := {
    t := W.t, ht := W.ht, hT := W.hT, c := k*W.c
    scale := by simp [k,W.scale]
    position := fun z => k • W.position z
    differential := by
      intro z hz
      rw [coordinateData_scale,nullRealDerivative_smul]
      exact (W.differential z hz).const_smul k
    periodic := fun z hz w hw => congrArg (k • ·) (W.periodic z hz w hw) }
  obtain ⟨h,hi⟩ := hW
  refine ⟨V,⟨⟨h.spatial_smul hk,harmonic_quotient_injective_of_smul h hi hk⟩,by
    change (-1:ℝ)*W.c < 0
    linarith⟩,rfl,?_⟩
  apply (spatial_similarity_iff_positive_scale_isometry _ _).mpr
  refine ⟨1,(LinearIsometryEquiv.neg ℝ).toIsometryEquiv,one_pos,?_⟩
  unfold PitchNormalizedBasicImmersion.image
  rw [image_image]
  apply image_congr
  intro z _
  change (1:ℝ) • -coordinateToEuclidean (W.position z) = coordinateToEuclidean ((-1:ℝ) • W.position z)
  simp

theorem original_representative_in_positive_pitch_family (s : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} s.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) :
    ∃ W ∈ positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
  obtain ⟨W,hW,hS⟩ := original_representative_in_pitch_family s bbc uniform hw
  obtain ⟨V,hV,_,hI⟩ := positive_pitch_representative W hW
  exact ⟨V,hV,(spatialSimilaritySetoid _).trans hS hI⟩

theorem positive_pitch_actual_geometric_representative (W : PitchNormalizedBasicImmersion)
    (hW : W ∈ positiveUnitPitchFamily) :
    ∃ s : OriginalHelicoidRepresentative, s.image = W.image ∧ s.axes.pitch = 1 ∧
      s.axes.horizontalPoint = 0 ∧ s.axes.horizontalDirection = 1 ∧
      ∀ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (d : ℝ), d ≠ 0 → (∀ v, R v 2 = v 2+d) →
        R '' range s.position ≠ range s.position := by
  obtain ⟨s,e,pitch,unit,rest⟩ := embedded_pitch_actual_geometric_representative_with_pitch W hW.1
  have ha := (verticalA_spec ⟨W.ht,W.hT⟩).1.2
  have pos : 0 < s.axes.pitch := pitch ▸ div_pos_of_neg_of_neg
    (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr ha)) hW.2
  rw [abs_of_pos pos] at unit
  exact ⟨s,e,unit,rest⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_representative_in_positive_pitch_family
#print axioms TwoAxisHelicoid.positive_pitch_actual_geometric_representative
