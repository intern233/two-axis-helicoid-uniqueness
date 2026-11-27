import TwoAxisHelicoid.IntegerHeightEndCoordinate
import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem integer_helicoidal_pitch_ne_zero {a c : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hc : c ≠ 0) (m : ℤ) : 2*(a-m)/c ≠ 0 := by
  apply div_ne_zero (mul_ne_zero (by norm_num) _) hc
  apply sub_ne_zero.mpr
  intro he
  by_cases hm : m ≤ 0
  · have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    linarith [ha.1]
  · have hmZ : 1 ≤ m := by omega
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmZ
    linarith [ha.2]

theorem TwoAxisHarmonicConformalImmersion.vertical_axis_zero
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    {z : ℂ} (hz : z ∉ L.lattice) (hrez : z.re = 0) : X z 0 = 0 ∧ X z 1 = 0 := by
  have he : conj z = -z := by
    apply Complex.ext <;> simp [hrez]
  have hc := hX.conjugation z hz
  rw [he,hX.neg z hz] at hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  constructor <;> linarith

/-- Reconstruct the actual integer-branch coordinate differential from
the harmonic map's own coefficient, height form and Gauss map. -/
theorem harmonic_integer_gauss_data_has_coordinate_differential
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      HasFDerivAt X (nullRealDerivative
        (weierstrassTriple (thetaGauss t a m z) (coordinateData t a c ht z 2))) z := by
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  intro z hz
  have hzn := ((not_mem_gaussLogPoleSet _ _ _).mp hz).1
  have hh0 := null_height_nonzero_away_pair ht ha
    (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hh hz
  have hd := puncturedImmersionCoefficient_hasFDerivAt hX hzn
  rw [null_eq_weierstrassTriple (hp.null z hzn) hh0,hg z hz,hh z hzn] at hd
  exact hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_gauss_data_has_coordinate_differential
