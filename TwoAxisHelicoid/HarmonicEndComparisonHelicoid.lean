import TwoAxisHelicoid.HarmonicIntegerCompleteAxes
import TwoAxisHelicoid.HelicoidEndHorizontalRuling
import TwoAxisHelicoid.AxisHelicoidGauge
import TwoAxisHelicoid.HarmonicTorusC1Normalization

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaGauss

/-- The helicoid occurring in the complete single-sheeted C¹ end
theorem is exactly the calibrated pitch-α surface in the original
spatial coordinates. The actual horizontal axis forces its phase
before any information about intersections in the compact core. -/
theorem harmonic_integer_end_comparison_helicoid {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    let α : ℝ := 2*(a-m)/c
    ∃ b : ℝ, let A := axisSpatialNormalization (integer_helicoidal_pitch_ne_zero ha hc m) ![0,0,b]
      HasHelicoidC1End (coordinateToTube ∘ A ∘ harmonicTorusImmersion hX) ∧
        A ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im) = range (axisRuledHelicoid I α 0) := by
  let L := rhombicPeriodPair t ht
  let α : ℝ := 2*(a-m)/c
  have hα : α ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨b,hb⟩ := harmonic_integer_data_C1_helicoid_end ht ha hc m hX hh hg
  let A := axisSpatialNormalization hα ![0,0,b]
  let Y := coordinateToTube ∘ A ∘ harmonicTorusImmersion hX
  have hEnd : HasHelicoidC1End Y := by
    convert hb using 1
    funext q
    rw [heightCenteredTorusPrimitive_eq_space_map _ hα]
    rfl
  have hcont : Continuous Y := by
    apply coordinateToTube.continuous.comp (A.continuous.comp _)
    apply periodTorusLift_continuous_punctured _ _ _
    intro z hz
    exact (hX.differentiable z hz).continuousAt.congr (punctureFilledMap_eventuallyEq hz).symm
  have hline : ∀ x : ℝ, ((x,0),α*(0-b)) ∈ range Y := by
    intro x
    obtain ⟨z,hz,hzr⟩ := (harmonic_integer_data_contains_complete_axes ht ha hc m hX hh hg).1 (-x/α)
    refine ⟨⟨periodTorusProjection L z,fun h => hz ((periodTorusProjection_eq_zero L z).mp h)⟩,?_⟩
    change coordinateToTube (axisSpatialNormalization hα ![0,0,b] (harmonicTorusImmersion hX _)) = _
    rw [harmonicTorusImmersion_projection hX hz,hzr,axisSpatialNormalization_apply]
    apply Prod.ext
    · apply Prod.ext
      · change (verticalRotation I (α • (verticalRotation I (![-x/α,0,0] : Fin 3 → ℝ)-
          verticalRotation I (![0,0,b] : Fin 3 → ℝ)))) 0 = x
        simp [verticalRotation_apply]
        field_simp
      · change (verticalRotation I (α • (verticalRotation I (![-x/α,0,0] : Fin 3 → ℝ)-
          verticalRotation I (![0,0,b] : Fin 3 → ℝ)))) 1 = 0
        simp [verticalRotation_apply]
    · rfl
  have hsin := hEnd.horizontal_line_is_ruling hcont hline
  have hunit : (![1,0,0] : Fin 3 → ℝ) ∈ range (axisRuledHelicoid I α b) := by
    apply (axisHelicoidSide_eq_zero_iff (by simp : normSq I=1) _ _ _).mp
    let θ := α*(0-b)
    change (I*Complex.exp (I*(θ : ℂ))).re*1 + (I*Complex.exp (I*(θ : ℂ))).im*0 = 0
    rw [mul_one,mul_zero,add_zero,mul_comm I (θ : ℂ),Complex.mul_re,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub,Complex.exp_ofReal_mul_I_im,show Real.sin θ = 0 from hsin,neg_zero]
  exact ⟨b,hEnd,(inverse_image_standardHelicoid_axisNormalization hα b).trans
    (axisRuledHelicoid_range_of_horizontal_unit (by simp : normSq I=1) α b hunit)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_end_comparison_helicoid
