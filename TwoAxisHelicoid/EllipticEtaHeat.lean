import TwoAxisHelicoid.LogSecondSixth
import TwoAxisHelicoid.VerticalEllipticHeat

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaScaledJet thetaJet thetaEtaExpression

theorem actual_g2_scaled_theta_identity {t : ℝ} (ht : 0 < t) :
    (rhombicPeriodPair t ht).g₂*(thetaScaledJet t 1 0)^2 =
      (10/3:ℂ)*(thetaScaledJet t 3 0)^2-2*thetaScaledJet t 1 0*thetaScaledJet t 5 0 := by
  let L := rhombicPeriodPair t ht
  have hN : logSecondNumerator (thetaScaledJet t) (L.weierstrassPExcept 0) (thetaEtaExpression t)
      =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(thetaWeierstrassDifference_weighted_of_pos ht ht).symm] with z hz
    rw [hz]
    simp only [Pi.mul_apply,Pi.pow_apply,thetaWeierstrassDifference_eq_zero_of_pos ht ht,zero_mul]
  have hzero : iteratedDeriv 6
      (logSecondNumerator (thetaScaledJet t) (L.weierstrassPExcept 0) (thetaEtaExpression t)) 0 = 0 := by
    rw [hN.iteratedDeriv_eq]
    simp
  have hcalc := logSecondNumerator_sixth (thetaScaledJet t) (L.weierstrassPExcept 0)
    (thetaEtaExpression t) (fun j => thetaScaledJet_analyticAt ht j 0)
    (L.analyticAt_weierstrassPExcept 0)
    (fun j n => congrFun (thetaScaledJet_iteratedDeriv ht j n) 0)
    (thetaScaledJet_zero_at_zero t) (thetaScaledJet_two_at_zero t) (L.weierstrassPExcept_zero 0)
  rw [hcalc,L.iteratedDeriv_weierstrassPExcept_self] at hzero
  norm_num only [Nat.reduceAdd,Nat.factorial,ite_false,show (2:ℕ) ≠ 0 by decide,
    Nat.cast_ofNat,PeriodPair.sumInvPow_zero] at hzero
  have hc : 3*thetaEtaExpression t*thetaScaledJet t 1 0+thetaScaledJet t 3 0 = 0 := by
    unfold thetaEtaExpression
    field_simp [thetaScaledJet_one_ne_zero_of_pos ht]
    ring
  change L.g₂*(thetaScaledJet t 1 0)^2 = _
  unfold PeriodPair.g₂
  linear_combination -(1/36:ℂ)*hzero-(20/9:ℂ)*thetaScaledJet t 3 0*hc

theorem thetaScaledJet_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => thetaScaledJet s j z)
      (thetaScaledJet t (j+2) z/(2*(Real.pi:ℂ))+(Real.pi/8:ℂ)*thetaScaledJet t j z) t := by
  have hd := (thetaJet_parameter_hasDerivAt ht j ((Real.pi/2:ℂ)*z)).const_mul ((Real.pi/2:ℂ)^j)
  convert hd using 1
  · funext s
    unfold thetaScaledJet
    rfl
  · simp only [thetaScaledJet,pow_add]
    field_simp
    ring

theorem thetaEtaExpression_hasDerivAt_heat {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaEtaExpression
      (((rhombicPeriodPair t ht).g₂/12-thetaEtaExpression t^2)/(Real.pi:ℂ)) t := by
  have hn := thetaScaledJet_one_ne_zero_of_pos ht
  have hd := (((thetaScaledJet_parameter_hasDerivAt ht 3 0).div
    (thetaScaledJet_parameter_hasDerivAt ht 1 0) hn).const_mul (-(1/3:ℂ)))
  have he : thetaEtaExpression = fun s : ℝ => -(1/3:ℂ)*(thetaScaledJet s 3 0/thetaScaledJet s 1 0) := by
    funext s
    unfold thetaEtaExpression
    ring
  rw [he]
  convert hd using 1
  have hg := actual_g2_scaled_theta_identity ht
  norm_num only [Nat.reduceAdd]
  field_simp [hn,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  linear_combination 144*hg

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_g2_scaled_theta_identity
#print axioms TwoAxisHelicoid.thetaEtaExpression_hasDerivAt_heat
