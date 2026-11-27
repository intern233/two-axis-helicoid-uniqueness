import TwoAxisHelicoid.SpinorRegularity
import TwoAxisHelicoid.HarmonicIntegerCoordinateData
import TwoAxisHelicoid.NullCoordinateRecognition

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

theorem spinorCoordinateData_eq_original {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C z : ℂ}
    (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    spinorCoordinateData t a m C z =
      weierstrassTriple (thetaGauss t a m z)
        (I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)) := by
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h1 := weierstrassSpinor_square_one ht m hC haL hz hp
  have h2 := weierstrassSpinor_square_two ht m hC haL hz hm hp
  have h3 := weierstrassSpinor_product ht m hC haL hz
  ext j
  fin_cases j <;> dsimp [spinorCoordinateData,weierstrassTriple]
  · rw [h1,h2]
    ring
  · rw [h1,h2]
    ring
  · exact h3

/-- Identification at all finite regular points, including the two zeros
of the height differential. The removable continuation is proved from
the actual analytic coefficients. -/
theorem null_coefficients_eq_spinorCoordinateData {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ) {C : ℂ}
    (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2)) {p : ℂ → Fin 3 → ℂ}
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ComplexNull (p z))
    (hA : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (p z) = thetaGauss t a m z) :
    ∀ z ∉ (rhombicPeriodPair t ht).lattice, p z = spinorCoordinateData t a m C z := by
  have hregular (z : ℂ) (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      p z = spinorCoordinateData t a m C z := by
    have h := (not_mem_gaussLogPoleSet (rhombicPeriodPair t ht) a z).mp hz
    have hh0 := null_height_nonzero_away_pair ht ha
      (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hh hz
    rw [null_eq_weierstrassTriple (hp z h.1) hh0,hg z hz,hh z h.1]
    exact (spinorCoordinateData_eq_original ht ha m hC h.1 h.2.1 h.2.2).symm
  intro z hz
  have hpc : ContinuousAt p z := continuousAt_pi.mpr (fun j => (hA z hz j).continuousAt)
  have hsc := (spinorCoordinateData_analyticAt (a := a) ht m C hz).continuousAt
  have he : p =ᶠ[𝓝[≠] z] spinorCoordinateData t a m C := by
    filter_upwards [latticePoleSet_punctured_avoids (rhombicPeriodPair t ht)
      (show ({0,(a : ℂ),-(a : ℂ)} : Set ℂ).Finite by simp) z] with w hw
    exact hregular w hw
  exact tendsto_nhds_unique (hpc.tendsto.mono_left nhdsWithin_le_nhds)
    ((hsc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)

theorem harmonic_integer_data_has_spinor_differential
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt X (nullRealDerivative (spinorCoordinateData t a m C z)) z := by
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  have he := null_coefficients_eq_spinorCoordinateData ht ha hc m hC hp.null
    (fun _ hz j => puncturedImmersionCoefficient_analyticAt hX hz j) hh hg
  intro z hz
  rw [← he z hz]
  exact puncturedImmersionCoefficient_hasFDerivAt hX hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_data_has_spinor_differential
