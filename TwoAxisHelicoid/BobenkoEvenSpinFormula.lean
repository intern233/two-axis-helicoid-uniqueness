import TwoAxisHelicoid.BobenkoRhombicScaling
import TwoAxisHelicoid.WeierstrassSpinors

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaEtaExpression thetaZeta

/-- The characteristic sigma in Bobenko (37), ν=2 and ω₂=-L. -/
noncomputable def bobenkoSigmaTwo (t L : ℝ) (w : ℂ) : ℂ :=
  -exp (bobenkoZeta t L (-L)*w)*bobenkoSigma t L (w+L)/bobenkoSigma t L (-L)

private theorem sigma_one_ne {t : ℝ} (ht : 0 < t) : thetaSigma t 1 ≠ 0 :=
  mt (thetaSigma_zero_iff_lattice_of_pos ht ht 1).mp (by
    simpa using (real_not_mem_rhombic_lattice_of_pos ht (x := 1) (by norm_num) (by norm_num)))

theorem bobenko_eta_two {t L : ℝ} (hL : 0 < L) :
    bobenkoZeta t L (-L) = -thetaEtaExpression t / L := by
  have eq := thetaZeta_add_two t (-1)
  rw [show (-1:ℂ)+2=1 by norm_num,thetaZeta_neg] at eq
  rw [show (-(L:ℂ))=L*(-1) by ring,bobenko_zeta_scale hL,thetaZeta_neg]
  congr 1
  linear_combination -(1/2:ℂ)*eq

theorem bobenko_sigma_two_scaled {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (z : ℂ) :
    bobenkoSigmaTwo t L (L*z) =
      exp (-thetaEtaExpression t*z)*thetaSigma t (z+1)/thetaSigma t 1 := by
  have hL0 : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hn : bobenkoSigma t L (-L) = -(L*thetaSigma t 1) := by
    rw [show (-(L:ℂ))=L*(-1) by ring,bobenko_sigma_scale hL,thetaSigma_neg]; ring
  rw [bobenkoSigmaTwo,bobenko_eta_two hL,hn,show (L:ℂ)*z+L=L*(z+1) by ring,
    bobenko_sigma_scale hL,show -thetaEtaExpression t/(L:ℂ)*(L*z) = -thetaEtaExpression t*z by
      field_simp [hL0]]
  field_simp [hL0,sigma_one_ne ht]

theorem bobenko_sigma_two_shifts {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) (z : ℂ) :
    bobenkoSigmaTwo t L (L*z-1/2) =
      (exp (thetaEtaExpression t*z))⁻¹ * exp (thetaEtaExpression t*(1-a)) *
        thetaSigma t (z+a)/thetaSigma t 1 ∧
    bobenkoSigmaTwo t L (L*z+1/2) =
      -(exp (thetaEtaExpression t*z)*exp (thetaEtaExpression t*(1-a))*
        thetaSigma t (z-a)/thetaSigma t 1) := by
  let s : ℂ := 1-(a:ℂ)
  have hLs : (L:ℂ)*s = 1/2 := by
    dsimp [s]; rw [ha]; push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
    ring
  constructor
  · rw [show (L:ℂ)*z-1/2 = L*(z-s) by rw [← hLs]; ring,
        bobenko_sigma_two_scaled ht hL,show z-s+1=z+a by dsimp [s]; ring,
        show -thetaEtaExpression t*(z-s)= -(thetaEtaExpression t*z)+thetaEtaExpression t*s by ring,
        exp_add,exp_neg]
  · rw [show (L:ℂ)*z+1/2 = L*(z+s) by rw [← hLs]; ring,
      bobenko_sigma_two_scaled ht hL,show z+s+1=(z-a)+2 by dsimp [s]; ring,
      thetaSigma_add_two]
    have ep : exp (-thetaEtaExpression t*(z+s))*exp (2*thetaEtaExpression t*(z-a+1)) =
        exp (thetaEtaExpression t*z)*exp (thetaEtaExpression t*s) := by
      simp only [← exp_add]; congr 1; dsimp [s]; ring
    calc
      _ = -((exp (-thetaEtaExpression t*(z+s))*exp (2*thetaEtaExpression t*(z-a+1)))*
            thetaSigma t (z-a)/thetaSigma t 1) := by ring
      _ = _ := by rw [ep]

theorem bobenko_sigma_two_normalizer {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) :
    bobenkoSigmaTwo t L (1/2) =
      exp (thetaEtaExpression t*(1-a))*thetaSigma t a/thetaSigma t 1 := by
  simpa [thetaSigma_neg, neg_div] using (bobenko_sigma_two_shifts ht hL ha 0).2

theorem bobenko_sigma_two_normalizer_ne {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) (har : a ∈ Ioo (0:ℝ) 1) :
    bobenkoSigmaTwo t L (1/2) ≠ 0 := by
  rw [bobenko_sigma_two_normalizer ht hL ha]
  exact div_ne_zero (mul_ne_zero (exp_ne_zero _) (mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp
    (real_not_mem_rhombic_lattice_of_pos ht har.1 (by linarith [har.2])))) (sigma_one_ne ht)

private theorem bobenko_kernel_exponent {t L a : ℝ} (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) (z : ℂ) :
    exp (2*((a:ℂ)-1)*thetaZeta t z + 2*thetaEtaExpression t*z) =
      (exp (thetaZeta t z/L))⁻¹ * exp (thetaEtaExpression t*z)^2 := by
  rw [← exp_neg,← exp_nat_mul,← exp_add]
  congr 1
  rw [ha]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  ring

/-- The ν=2 Gauss quotient below equation (39), in its original coordinate. -/
noncomputable def bobenkoEvenGauss (t L : ℝ) (w : ℂ) : ℂ :=
  bobenkoSigmaTwo t L (w-1/2)/bobenkoSigmaTwo t L (w+1/2)*exp (bobenkoZeta t L w)

theorem bobenko_even_gauss_pullback {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) {z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    bobenkoEvenGauss t L (L*z)*thetaGauss t a 1 z = -I := by
  have hm' := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mp hm
  have hp' := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
  obtain ⟨hminus,hplus⟩ := bobenko_sigma_two_shifts ht hL ha z
  rw [bobenkoEvenGauss,hminus,hplus,bobenko_zeta_scale hL]
  simp only [thetaGauss,Int.cast_one,mul_one,bobenko_kernel_exponent hL ha]
  field_simp [exp_ne_zero,hm',hp',sigma_one_ne ht]

/-- Coefficient of the second spinor in (38), including its common phase. -/
noncomputable def bobenkoEvenSecondSpinor (t L : ℝ) (w : ℂ) : ℂ :=
  exp (-(Real.pi:ℂ)*I/4) *
    (bobenkoSigmaTwo t L (w+1/2)/(bobenkoSigma t L w*bobenkoSigmaTwo t L (1/2))) *
    exp (-bobenkoZeta t L w/2)

private theorem bobenko_phase_sq : exp (-(Real.pi:ℂ)*I/4)^2 = -I := by
  rw [← exp_nat_mul,show ((2:ℕ):ℂ)*(-(Real.pi:ℂ)*I/4) = -((Real.pi:ℂ)/2*I) by push_cast; ring,
    exp_neg,Complex.exp_pi_div_two_mul_I,inv_eq_one_div]
  apply (div_eq_iff I_ne_zero).mpr
  simp

/-- Pullback of b² dw from (38), expressed in the actual TwoAxisHelicoid horizontal
kernel. This uses the unshifted variable denominator σ(w). -/
theorem bobenko_even_second_spinor_square {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) (har : a ∈ Ioo (0:ℝ) 1) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    (L:ℂ)*bobenkoEvenSecondSpinor t L (L*z)^2 = (-I/L)*thetaA t a z := by
  have hal := real_not_mem_rhombic_lattice_of_pos ht har.1 (by linarith [har.2] : a < 2)
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp hal
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hζ : exp (-(thetaZeta t z/(L:ℂ))/2)^2 = (exp (thetaZeta t z/(L:ℂ)))⁻¹ := by
    rw [← exp_nat_mul,← exp_neg]; congr 1; push_cast; ring
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht z hal hz,thetaSigmaKernel,
    bobenko_kernel_exponent hL ha,bobenkoEvenSecondSpinor,
    (bobenko_sigma_two_shifts ht hL ha z).2,bobenko_sigma_scale hL,
    bobenko_sigma_two_normalizer ht hL ha,bobenko_zeta_scale hL]
  simp only [mul_pow,bobenko_phase_sq,hζ]
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne',exp_ne_zero,sigma_one_ne ht,hsa,hsz]

/-- At the midpoint of the path in (44) the two possible variable
denominators have different zero sets. -/
theorem bobenko_midpoint_denominators {t L : ℝ} (ht : 0 < t) (hL : 0 < L) :
    bobenkoSigmaTwo t L (-L) = 0 ∧ bobenkoSigma t L (-L) ≠ 0 := by
  rw [show (-(L:ℂ)) = L*(-1) by ring,bobenko_sigma_two_scaled ht hL,bobenko_sigma_scale hL,
      thetaSigma_neg]
  simp [thetaSigma_zero,Complex.ofReal_ne_zero.mpr hL.ne',sigma_one_ne ht]

/-- For L=1/2, the characteristic (0,0) satisfies the nonlattice
test printed in Theorem 4, p.24, while the denominator of (38) vanishes. -/
theorem bobenko_theorem_four_nu_two_exception {t : ℝ} (ht : 0 < t) :
    (1/2:ℂ) ∉ (bobenkoPeriodPair t (1/2) ht (by norm_num)).lattice ∧
      bobenkoSigmaTwo t (1/2) (1/2) = 0 := by
  have hL : (0:ℝ) < 1/2 := by norm_num
  have pp := bobenko_lattice_scale_iff ht hL 1
  have one : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa using (real_not_mem_rhombic_lattice_of_pos ht (x := 1) (by norm_num) (by norm_num))
  have two : thetaSigma t 2 = 0 := by simpa [thetaSigma_zero] using thetaSigma_add_two t 0
  constructor
  · simpa using mt pp.mp one
  · simpa [one_add_one_eq_two, two] using bobenko_sigma_two_scaled ht hL 1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bobenko_even_gauss_pullback
#print axioms TwoAxisHelicoid.bobenko_even_second_spinor_square
#print axioms TwoAxisHelicoid.bobenko_midpoint_denominators
#print axioms TwoAxisHelicoid.bobenko_theorem_four_nu_two_exception
