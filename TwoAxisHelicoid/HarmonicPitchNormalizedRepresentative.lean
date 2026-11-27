import TwoAxisHelicoid.HoffmanWhiteBasicBranch
import TwoAxisHelicoid.CompactCoreFiniteSimilarityClasses
import TwoAxisHelicoid.CoordinateOrientationIsometry
import TwoAxisHelicoid.PrimitivePeriodNecessity

namespace TwoAxisHelicoid
open Complex Set

/-- Rescale the actual original parametrization to the unit-pitch
convention of Appendix B, preserving its two marked axes and full
compact core. This step uses no estimate on the horizontal period. -/
theorem harmonic_embedded_pitch_normalized_representative
    (hw : RhombicHelicoidIntersectionPrinciple) {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2:ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2:ℤ)) :
    ∃ W : PitchNormalizedBasicImmersion, W.t = t ∧
      (spatialSimilaritySetoid _).r (range (coordinateToEuclidean ∘ harmonicTorusImmersion hX)) W.image ∧
      ∃ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (k : ℝ), 0 < k ∧
        (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
        TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (fun z => R (X z)) ∧
        ∀ z, W.position z = k • R (X z) := by
  obtain ⟨a,c,R,ha,hc,hT,ha',hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_basic_data_of_intersection_principle hw ht hX hXi hhOrder hgOrder
  subst a
  let a := verticalA t
  let L := rhombicPeriodPair t ht
  let Y := fun z => R (X z)
  let p := puncturedImmersionCoefficient L Y
  have hg' (z : ℂ) (hz : z ∉ gaussLogPoleSet L a) :
      nullGauss (p z) = 1*thetaGauss t a 1 z := (hg z hz).trans (one_mul _).symm
  have hA := hY.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  have he := null_coefficients_eq_phased_coordinateData ht ha hc norm_one hA.null
    (fun _ hz j => puncturedImmersionCoefficient_analyticAt hY hz j) hh hg'
  have hD (z : ℂ) (hz : z ∉ L.lattice) : HasFDerivAt Y (nullRealDerivative (coordinateData t a c ht z)) z := by
    have he' : phasedCoordinateData t a c ht 1 z = coordinateData t a c ht z := by
      funext j
      fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]
    rw [← he',← he z hz]
    exact puncturedImmersionCoefficient_hasFDerivAt hY hz
  let k := 2*(1-a)/|c|
  have hk : 0 < k := div_pos (mul_pos (by norm_num) (sub_pos.mpr ha.2)) (abs_pos.mpr hc)
  have hd : HasTwoAxisHelicoidCoordinateDifferential (fun z => k • Y z) t a (k*c) ht := by
    intro z hz
    have heq : coordinateData t a (k*c) ht z = k • coordinateData t a c ht z := by
      rw [coordinateData_real_smul t a (k*c) ht z,coordinateData_real_smul t a c ht z,smul_smul]
    rw [heq,nullRealDerivative_real_smul]
    exact (hD z hz).const_smul k
  let W : PitchNormalizedBasicImmersion := {
    t := t, ht := ht, hT := hT, c := k*c
    scale := by rw [abs_mul,abs_of_pos hk]; exact div_mul_cancel₀ _ (abs_ne_zero.mpr hc)
    position := fun z => k • Y z
    differential := hd
    periodic := fun z hz ω hω => congrArg (k • ·) (hY.periodic z hz ω hω) }
  refine ⟨W,rfl,?_,R,k,hk,hR,hY,fun _ => rfl⟩
  apply (spatial_similarity_iff_positive_scale_isometry _ _).mpr
  refine ⟨k,euclideanOrientationIsometry R hR,hk,?_⟩
  rw [Set.range_comp,harmonicTorusImmersion_range hX,image_image,image_image]
  change (fun z => k • coordinateToEuclidean (R (X z))) '' (L.lattice : Set ℂ)ᶜ =
    (fun z => coordinateToEuclidean (k • Y z)) '' (L.lattice : Set ℂ)ᶜ
  simp only [map_smul,Y]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_embedded_pitch_normalized_representative
