import TwoAxisHelicoid.ThetaSigmaZeta
import TwoAxisHelicoid.SigmaKernelAlgebra

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaScaledJet

noncomputable def thetaSigmaKernel (t a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (2*(a-1)*thetaZeta t z+2*thetaEtaExpression t*z)*
    (thetaSigma t (z-a)^2/(thetaSigma t z^2*thetaSigma t (a:ℂ)^2))

theorem thetaA_eq_scaled (t a : ℝ) (z : ℂ) :
    thetaA t a z = (thetaScaledJet t 1 0/thetaScaledJet t 0 (a:ℂ))^2*
      (thetaScaledJet t 0 (z-a)/thetaScaledJet t 0 z)^2*
      Complex.exp (2*(a-1)*(thetaScaledJet t 1 z/thetaScaledJet t 0 z)) := by
  have harg (w : ℂ) : (Real.pi/2:ℂ)*w = Real.pi*w/2 := by ring
  simp only [thetaA,thetaScaledJet,pow_zero,pow_one,one_mul,harg,thetaQuotient,mul_zero,zero_div]
  congr 1
  · simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · congr 1
    ring

theorem thetaSigmaKernel_eq_thetaA {t a : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (z : ℂ)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaSigmaKernel t a z = thetaA t a z := by
  have hd := thetaScaledJet_one_ne_zero ht
  have hs := mt (thetaScaledJet_zero_iff_lattice ht ht0 z).mp hz
  have hb := mt (thetaScaledJet_zero_iff_lattice ht ht0 (a:ℂ)).mp ha
  unfold thetaSigmaKernel thetaSigma thetaZeta
  rw [sigma_kernel_algebra (a:ℂ) z (thetaEtaExpression t)
    (thetaScaledJet t 1 z/thetaScaledJet t 0 z) (thetaScaledJet t 1 0)
    (thetaScaledJet t 0 (z-a)) (thetaScaledJet t 0 z) (thetaScaledJet t 0 (a:ℂ)) hd hs hb]
  exact (thetaA_eq_scaled t a z).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigmaKernel_eq_thetaA
