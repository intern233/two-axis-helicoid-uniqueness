import TwoAxisHelicoid.HarmonicNullLift
import TwoAxisHelicoid.NullCoordinateRecognition
import TwoAxisHelicoid.GlobalImmersionRigidity

namespace TwoAxisHelicoid
open Complex Set

theorem harmonic_basic_gauss_data_has_coordinate_differential {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {q : ℂ} (hq : ‖q‖ = 1)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = q*thetaGauss t a 1 z) :
    ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt X (nullRealDerivative (phasedCoordinateData t a c ht q z)) z := by
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  have he := null_coefficients_eq_phased_coordinateData ht ha hc hq hp.null
    (fun _ hz j => puncturedImmersionCoefficient_analyticAt hX hz j) hh hg
  intro z hz
  rw [← he z hz]
  exact puncturedImmersionCoefficient_hasFDerivAt hX hz

/-- Once the basic Gauss branch is obtained, the actual map's single-valued
periods force the certified parameter pair. There is no separate period
assumption, numerical-root assumption or omitted finite-zero continuation. -/
theorem harmonic_basic_data_parameters_certified {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {q : ℂ} (hq : ‖q‖ = 1)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = q*thetaGauss t a 1 z) :
    t = certifiedClosedParameters.t ∧ a = certifiedClosedParameters.a := by
  have hd := harmonic_basic_gauss_data_has_coordinate_differential ht ha hc hq hX hh hg
  have h := periodic_phased_coordinate_primitive_period_equations ht ha hc hq hd hX.periodic
  have he : (t,a) = (certifiedClosedParameters.t,certifiedClosedParameters.a) :=
    existsUnique_actual_common_period_full_domain.unique ⟨ht,ha,h⟩
      ⟨certifiedClosedParameters.height_pos,certifiedClosedParameters.abscissa_mem,
        certifiedClosedParameters.vertical_closed,certifiedClosedParameters.horizontal_closed⟩
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_basic_data_parameters_certified
