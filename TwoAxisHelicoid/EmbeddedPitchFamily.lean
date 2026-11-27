import TwoAxisHelicoid.HarmonicPitchNormalizedRepresentative
import TwoAxisHelicoid.HarmonicSpatialScaling

namespace TwoAxisHelicoid
open Complex Set

/-- The actual pitch-normalized basic immersions which have both
symmetries and are injective on their punctured torus. -/
def embeddedPitchFamily : Set PitchNormalizedBasicImmersion :=
  {W | ∃ hW : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair W.t W.ht) W.position,
    Function.Injective (harmonicTorusImmersion hW)}

theorem original_embedded_harmonic_presents_in_pitch_family
    (hw : RhombicHelicoidIntersectionPrinciple) {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2:ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2:ℤ)) :
    ∃ W ∈ embeddedPitchFamily, W.t = t ∧
      (spatialSimilaritySetoid _).r (range (coordinateToEuclidean ∘ harmonicTorusImmersion hX)) W.image := by
  obtain ⟨W,hWt,himg,R,k,hk,_,hY,hpos⟩ := harmonic_embedded_pitch_normalized_representative hw ht hX hXi hhOrder hgOrder
  have hinj : Function.Injective (harmonicTorusImmersion hY) := by
    rw [harmonicTorusImmersion_space_map hX R hY]
    exact R.injective.comp hXi
  have hW : ∃ h : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) W.position,
      Function.Injective (harmonicTorusImmersion h) := by
    rw [funext hpos]
    exact ⟨hY.spatial_smul hk.ne',harmonic_quotient_injective_of_smul hY hinj hk.ne'⟩
  refine ⟨W,?_,hWt,himg⟩
  change ∃ h : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair W.t W.ht) W.position,
      Function.Injective (harmonicTorusImmersion h)
  subst t
  exact hW

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_embedded_harmonic_presents_in_pitch_family
