import TwoAxisHelicoid.HarmonicIntegerC1End
import TwoAxisHelicoid.HelicoidalC1Similarity

namespace TwoAxisHelicoid
open Complex Set

/-- The actual descended map, independent of how values at deleted
lattice points were originally represented. -/
noncomputable def harmonicTorusImmersion {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) : PuncturedPeriodTorus L → Fin 3 → ℝ :=
  fun q => periodTorusLift L (punctureFilledMap L X) (punctureFilledMap_periodic hX.periodic) q.1

theorem harmonicTorusImmersion_projection {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) {z : ℂ} (hz : z ∉ L.lattice) :
    harmonicTorusImmersion hX ⟨periodTorusProjection L z,fun h => hz ((periodTorusProjection_eq_zero L z).mp h)⟩ = X z :=
  punctureFilledMap_eq hz

theorem harmonicTorusImmersion_space_map {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hY : TwoAxisHarmonicConformalImmersion L (fun z => R (X z))) :
    harmonicTorusImmersion hY = R ∘ harmonicTorusImmersion hX := by
  funext q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hproj : periodTorusProjection L z = q.1 := hz
  have hzn : z ∉ L.lattice := fun h => q.2 (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  have hq : q = ⟨periodTorusProjection L z,fun h => hzn ((periodTorusProjection_eq_zero L z).mp h)⟩ :=
    Subtype.ext hproj.symm
  rw [hq,Function.comp_apply,harmonicTorusImmersion_projection hX hzn,harmonicTorusImmersion_projection hY hzn]

theorem harmonic_integer_data_hasHelicoidalC1End
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    HasHelicoidalC1End (harmonicTorusImmersion hX) := by
  let α : ℝ := 2*(a-m)/c
  have hα : α ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨b,hb⟩ := harmonic_integer_data_C1_helicoid_end ht ha hc m hX hh hg
  refine ⟨axisSpatialNormalization hα ![0,0,b],|α|,abs_pos.mpr hα,?_,?_⟩
  · intro v w
    simpa only [sq_abs] using axisSpatialNormalization_squared_displacement hα ![0,0,b] v w
  · have he : (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => coordinateToTube
        (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b
          (punctureFilledMap (rhombicPeriodPair t ht) X) (punctureFilledMap_periodic hX.periodic) q.1)) =
        coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ harmonicTorusImmersion hX := by
      funext q
      rw [heightCenteredTorusPrimitive_eq_space_map _ hα]
      rfl
    rwa [← he]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_data_hasHelicoidalC1End
