import TwoAxisHelicoid.RightCoefficientEnclosure
import TwoAxisHelicoid.HorizontalRightDerivative

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaQuotient thetaLogSecond thetaLogFourth rightSlopeTheta

theorem thetaEtaExpression_jet_ratio {t : ℝ} (ht : 0 < t) :
    thetaEtaExpression t = -(Real.pi^2/12:ℂ)*(thetaJet t 3 0/thetaJet t 1 0) := by
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 := thetaJet_one_at_zero_ne_zero_of_pos ht
  unfold thetaEtaExpression thetaScaledJet
  simp only [mul_zero,pow_one]
  field_simp
  ring

theorem rightSlopeTheta_algebra {t : ℝ} (ht : 0 < t) :
    (Real.pi:ℂ)*rightSlopeTheta t =
      3*thetaLogSecond t 1^2-2*thetaEtaExpression t*thetaLogSecond t 1-
        (2/3:ℂ)*thetaLogFourth t 1 := by
  rw [thetaLogSecond_one,thetaLogFourth_one,thetaEtaExpression_jet_ratio ht]
  unfold rightSlopeTheta
  ring

theorem rightSlopeTheta_eq_period_slope {t : ℝ} (ht : 0 < t) :
    (rightSlopeTheta t).re = -deriv ellipticFReal t+ellipticI t ht/Real.pi := by
  let L := rhombicPeriodPair t ht
  have hz : (1:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have heL := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz
  have heC := thetaLogFourth_eq_weierstrassP_second ht hz
  have heODE := rhombic_weierstrass_second_order ht hz
  have hj : (Real.pi:ℂ)*rightSlopeTheta t = thetaLogSecond t 1^2+
      (L.g₂/12+2*L.weierstrassP 1*thetaEtaExpression t+L.weierstrassP 1^2)-
      deriv L.derivWeierstrassP 1/2 := by
    rw [rightSlopeTheta_algebra ht,heL,heC,heODE]
    change 3*(L.weierstrassP 1+thetaEtaExpression t)^2-
      2*thetaEtaExpression t*(L.weierstrassP 1+thetaEtaExpression t)-(2/3:ℂ)*(6*L.weierstrassP 1^2-L.g₂/2) = _
    ring
  rw [thetaLogSecond_one_real] at hj
  have hjr : Real.pi*(rightSlopeTheta t).re = ellipticFReal t^2+ellipticI t ht-ellipticC t ht/2 := by
    have hr := congrArg Complex.re hj
    simpa only [ellipticI,ellipticC,L,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,← Complex.ofReal_pow] using hr
  have hh := ellipticFReal_heat_identity ht
  apply mul_right_cancel₀ Real.pi_ne_zero
  field_simp [Real.pi_ne_zero]
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rightSlopeTheta_eq_period_slope
