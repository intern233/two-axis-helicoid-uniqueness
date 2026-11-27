import TwoAxisHelicoid.ExactIntersectionWinding
import TwoAxisHelicoid.AxisHelicoidGauge
import TwoAxisHelicoid.IntegerEndHeightCenter

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaGauss

/-- Proposition 4.2 after the precise intersection conclusion of
Hoffman–White. The helicoid in that conclusion can use any height shift
admitted by the end normalization. No pointwise transversality, phase
avoidance, intersection multiplicity or preferred height shift is assumed. -/
theorem harmonic_integer_axis_index_of_axes_intersection {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) (punctureFilledMap (rhombicPeriodPair t ht) X)
        (punctureFilledMap_periodic hX.periodic) q.1))
    (hinter : ∃ b : ℝ,
      X '' ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ ∩
        (axisSpatialNormalization (integer_helicoidal_pitch_ne_zero ha hc m) ![0,0,b]) ⁻¹'
          range (fun w : ℂ => standardHelicoid w.re w.im) =
      {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)}) :
    m = 0 ∨ m = 1 := by
  have hG := harmonic_height_primitive_thetaG_zero ht ha hc hX hh
  let α : ℝ := 2*(a-m)/c
  let g := thetaGauss t a m (I*t)
  obtain ⟨b,hb⟩ := hinter
  rw [inverse_image_standardHelicoid_axisNormalization] at hb
  have hunit := (show (![1,0,0] : Fin 3 → ℝ) ∈ {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)} from
    Or.inl ⟨rfl,rfl⟩)
  rw [← hb] at hunit
  have hcmp := axisRuledHelicoid_range_of_horizontal_unit (by simp : normSq I = 1) α b hunit.2
  have hmid := harmonic_integer_axis_midpoint_data ht ha m hX hg
  have hgunit : normSq g = 1 := thetaGauss_axis_normSq ht ha m ⟨ht,by linarith⟩
  have hunit' : (![1,0,0] : Fin 3 → ℝ) ∈ range (axisRuledHelicoid g α (X (I*t) 2)) := by
    apply (axisHelicoidSide_eq_zero_iff hgunit _ _ _).mp
    change axisHelicoidSide (thetaGauss t a m (I*t)) α (X (I*t) 2) _ = 0
    rw [hmid.1]
    rcases hmid.2 with h | h <;> simp [h,axisHelicoidSide]
  have href := axisRuledHelicoid_range_of_horizontal_unit hgunit α (X (I*t) 2) hunit'
  apply harmonic_integer_axis_parameter_of_exact_intersection ht ha hc hG m hX hh hg hXi
  intro z hz he
  change X z ∈ range (axisRuledHelicoid g α (X (I*t) 2)) at he
  rw [href,← hcmp] at he
  have hmem : X z ∈ X '' ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ ∩
      range (axisRuledHelicoid I α b) := ⟨⟨z,hz,rfl⟩,he⟩
  change X z ∈ {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)}
  rw [← hb]
  exact hmem

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_axis_index_of_axes_intersection
