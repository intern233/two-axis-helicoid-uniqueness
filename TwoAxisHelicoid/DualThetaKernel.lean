import TwoAxisHelicoid.SigmaReciprocal
import TwoAxisHelicoid.EllipticFReciprocal
import TwoAxisHelicoid.DualKernelAlgebra

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaZeta thetaA thetaJet thetaScaledJet

noncomputable def dualAbscissa (t a : ℝ) : ℂ := a/(I*t)

theorem dualAbscissa_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    dualAbscissa t a = -I*a/t := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold dualAbscissa
  field_simp
  simp only [I_sq]
  ring

noncomputable def dualThetaA (t a : ℝ) (w : ℂ) : ℂ :=
  -(1:ℂ)/(t:ℂ)^2*
    (((Real.pi*thetaJet (1/t) 1 0)/(2*thetaJet (1/t) 0 (Real.pi*dualAbscissa t a/2)))^2*
      (thetaJet (1/t) 0 (Real.pi*(w-dualAbscissa t a)/2)/thetaJet (1/t) 0 (Real.pi*w/2))^2*
      Complex.exp (2*Real.pi*I*w+I*((Real.pi*(1-a)/t:ℝ):ℂ)*thetaQuotient (1/t) 1 (Real.pi*w/2)))

theorem thetaA_reciprocal_sigma {t a : ℝ} (ht : 0 < t)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) {w : ℂ}
    (hw : w ∉ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice) :
    thetaA t a ((I*t)*w) = -(1:ℂ)/(t:ℂ)^2*
      (Complex.exp (2*(a-1)*(thetaZeta (1/t) w/(I*t))+2*thetaEtaExpression t*((I*t)*w))*
        (thetaSigma (1/t) (w-dualAbscissa t a)^2/
          (thetaSigma (1/t) w^2*thetaSigma (1/t) (dualAbscissa t a)^2))) := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  have hz : (I*t)*w ∉ (rhombicPeriodPair t ht).lattice :=
    fun h => hw ((rhombic_reciprocal_mem_iff ht w).mpr h)
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht ((I*t)*w) ha hz]
  unfold thetaSigmaKernel
  rw [thetaZeta_reciprocal ht hz,thetaSigma_reciprocal ht ((I*t)*w-a),
    thetaSigma_reciprocal ht ((I*t)*w),thetaSigma_reciprocal ht (a:ℂ)]
  simp only [mul_div_cancel_left₀ w hi,sub_div,dualAbscissa]
  have hsw := mt (thetaSigma_zero_iff_lattice_of_pos (one_div_pos.mpr ht)
    (one_div_pos.mpr ht) w).mp hw
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos (one_div_pos.mpr ht)
    (one_div_pos.mpr ht) ((a:ℂ)/(I*t))).mp (reciprocal_not_mem_lattice ht ha)
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem thetaA_reciprocal_theta {t a : ℝ} (ht : 0 < t)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) {w : ℂ}
    (hw : w ∉ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice) :
    thetaA t a ((I*t)*w) = dualThetaA t a w := by
  have htinv := one_div_pos.mpr ht
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  have hd := thetaScaledJet_one_ne_zero_of_pos htinv
  have hs := mt (thetaScaledJet_zero_iff_lattice_of_pos htinv htinv w).mp hw
  have hb := mt (thetaScaledJet_zero_iff_lattice_of_pos htinv htinv (dualAbscissa t a)).mp
    (reciprocal_not_mem_lattice ht ha)
  rw [thetaA_reciprocal_sigma ht ha hw]
  unfold thetaSigma
  rw [sigma_ratio_exponential_algebra _ _ _ _ _ _ _ _ hd hs hb]
  have he : 2*(a-1)*(thetaZeta (1/t) w/(I*t))+2*thetaEtaExpression t*((I*t)*w)-
      2*thetaEtaExpression (1/t)*w*dualAbscissa t a =
      2*Real.pi*I*w+I*((Real.pi*(1-a)/t:ℝ):ℂ)*thetaQuotient (1/t) 1 (Real.pi*w/2) := by
    rw [thetaEtaExpression_reciprocal ht]
    unfold thetaZeta dualAbscissa thetaScaledJet thetaQuotient
    simp only [pow_zero,pow_one,one_mul]
    rw [show (Real.pi/2:ℂ)*w = Real.pi*w/2 by ring]
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  unfold dualThetaA thetaScaledJet
  simp only [pow_zero,pow_one,one_mul,mul_zero]
  congr 2
  · congr 1 <;> ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_reciprocal_theta
