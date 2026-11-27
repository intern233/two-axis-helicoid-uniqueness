import TwoAxisHelicoid.BobenkoEvenSpinFormula

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaEtaExpression thetaZeta

/-- The same second spinor in (38) for the unshifted choice ν=0. -/
noncomputable def bobenkoUnshiftedSecondSpinor (t L : ℝ) (w : ℂ) : ℂ :=
  exp (-(Real.pi:ℂ)*I/4) *
    (bobenkoSigma t L (w+1/2)/(bobenkoSigma t L w*bobenkoSigma t L (1/2))) *
    exp (-bobenkoZeta t L w/2)

private theorem shift_eq {L a : ℝ} (hL : 0 < L) (ha : a = 1-1/(2*L)) :
    (L:ℂ)*(1-(a:ℂ)) = 1/2 := by
  rw [ha]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  ring

private theorem spin_exponent_eq {L a : ℝ} (hL : 0 < L) (ha : a = 1-1/(2*L))
    (Z : ℂ) : ((a:ℂ)-1)*Z = -(Z/L)/2 := by
  rw [ha]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  ring

theorem bobenko_two_spin_coefficients {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1-1/(2*L)) (har : a ∈ Ioo (0:ℝ) 1) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    bobenkoEvenSecondSpinor t L (L*z) =
      -(exp (-(Real.pi:ℂ)*I/4)/(L*thetaSigma t a))*thetaSpinor t a 1 z ∧
    bobenkoUnshiftedSecondSpinor t L (L*z) =
      (exp (-(Real.pi:ℂ)*I/4)/(L*thetaSigma t (1-a)))*thetaSpinor t (a-1) 0 z := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp
    (real_not_mem_rhombic_lattice_of_pos ht har.1 (by linarith [har.2]))
  have hs1 := mt (thetaSigma_zero_iff_lattice_of_pos ht ht 1).mp (by
    simpa using (real_not_mem_rhombic_lattice_of_pos ht (x := 1) (by norm_num) (by norm_num)))
  have hs' : thetaSigma t (1-(a:ℂ)) ≠ 0 := by
    apply mt (thetaSigma_zero_iff_lattice_of_pos ht ht _).mp
    simpa only [Complex.ofReal_sub,Complex.ofReal_one] using
      (real_not_mem_rhombic_lattice_of_pos ht (x := 1-a) (by linarith [har.2]) (by linarith [har.1]))
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hL0 := Complex.ofReal_ne_zero.mpr hL.ne'
  constructor
  · rw [bobenkoEvenSecondSpinor,(bobenko_sigma_two_shifts ht hL ha z).2,bobenko_sigma_scale hL,
        bobenko_sigma_two_normalizer ht hL ha,bobenko_zeta_scale hL]
    simp only [thetaSpinor,spinorExponent,Int.cast_one,one_mul,spin_exponent_eq hL ha,exp_add]
    field_simp [hL0,hsa,hsz,hs1,exp_ne_zero]
  · have hshift := shift_eq hL ha
    rw [bobenkoUnshiftedSecondSpinor,show (L:ℂ)*z+1/2=L*(z+(1-a)) by rw [← hshift]; ring,
      bobenko_sigma_scale hL,bobenko_sigma_scale hL,
      show bobenkoSigma t L (1/2) = L*thetaSigma t (1-a) by rw [← hshift,bobenko_sigma_scale hL],
      bobenko_zeta_scale hL]
    simp only [thetaSpinor,spinorExponent,Int.cast_zero,Complex.ofReal_sub,Complex.ofReal_one,
      sub_zero,zero_mul,add_zero,spin_exponent_eq hL ha]
    rw [show z-((a:ℂ)-1)=z+(1-a) by ring]
    field_simp [hL0,hs',hsz]

/-- Along the same physical period 2ω₃, the characteristic and
unshifted choices in (38) have opposite spin characters. -/
theorem bobenko_different_spin_characters {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1-1/(2*L)) (har : a ∈ Ioo (0:ℝ) 1) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    bobenkoEvenSecondSpinor t L (L*(z+(1+I*t))) = -bobenkoEvenSecondSpinor t L (L*z) ∧
    bobenkoUnshiftedSecondSpinor t L (L*(z+(1+I*t))) = bobenkoUnshiftedSecondSpinor t L (L*z) := by
  have hw : 1+I*t ∈ (rhombicPeriodPair t ht).lattice :=
    PeriodPair.mem_lattice.mpr ⟨0,1,by simp [rhombicPeriodPair]⟩
  have hz' : z+(1+I*t) ∉ (rhombicPeriodPair t ht).lattice :=
    fun h => hz (by simpa using (rhombicPeriodPair t ht).lattice.sub_mem h hw)
  obtain ⟨he,hu⟩ := bobenko_two_spin_coefficients ht hL ha har hz
  obtain ⟨he',hu'⟩ := bobenko_two_spin_coefficients ht hL ha har hz'
  rw [he,hu,he',hu',thetaSpinor_multiplier_half ht 1 hz,thetaSpinor_multiplier_half ht 0 hz]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bobenko_different_spin_characters
