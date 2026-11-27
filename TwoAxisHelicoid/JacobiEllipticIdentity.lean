import TwoAxisHelicoid.JacobiThetaSecondLogDerivative
import TwoAxisHelicoid.ThetaAllWeierstrass

namespace TwoAxisHelicoid
open Complex Filter
set_option maxHeartbeats 800000
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond jacobiFactorProduct

theorem jacobiThetaProduct_ne_zero {q z : ℂ} (hq : ‖q‖ < 1)
    (hx : jacobiExp z ≠ 1) (hp : ‖q‖*‖jacobiExp z‖ < 1)
    (hm : ‖q‖*‖(jacobiExp z)⁻¹‖ < 1) : jacobiThetaProduct q z ≠ 0 := by
  change Complex.exp (-I*(Real.pi : ℂ)*z/2)*
    ((1-jacobiExp z)*jacobiFactorProduct q (jacobiExp z)*
      jacobiFactorProduct q ((jacobiExp z)⁻¹)) ≠ 0
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx.symm)
      (jacobiFactorProduct_ne_zero_of_norm hq hp)) (jacobiFactorProduct_ne_zero_of_norm hq hm))

theorem thetaScaledJet_ne_zero_of_product_region {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hx : jacobiExp z ≠ 1) (hp : ‖jacobiNome t‖*‖jacobiExp z‖ < 1)
    (hm : ‖jacobiNome t‖*‖(jacobiExp z)⁻¹‖ < 1) : thetaScaledJet t 0 z ≠ 0 := by
  intro hz
  have he := rhombicProductTheta_eq_scaled_theta ht z
  rw [hz, mul_zero] at he
  exact jacobiThetaProduct_ne_zero (jacobiNome_norm_lt_one ht) hx hp hm he

theorem thetaScaledJet_logDeriv_hasDerivAt {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : thetaScaledJet t 0 z ≠ 0) :
    HasDerivAt (logDeriv (thetaScaledJet t 0)) (-thetaLogSecond t z) z := by
  have he : logDeriv (thetaScaledJet t 0) = fun w => thetaScaledJet t 1 w/thetaScaledJet t 0 w := by
    funext w
    rw [logDeriv_apply, (thetaScaledJet_hasDerivAt ht 0 w).deriv]
  have h := (thetaScaledJet_hasDerivAt ht 1 z).div (thetaScaledJet_hasDerivAt ht 0 z) hz
  have hv : (thetaScaledJet t 2 z*thetaScaledJet t 0 z-
      thetaScaledJet t 1 z*thetaScaledJet t 1 z)/(thetaScaledJet t 0 z)^2 =
      -thetaLogSecond t z := by
    rw [thetaLogSecond_scaled]
    field_simp [hz]
    ring
  change HasDerivAt (fun w => thetaScaledJet t 1 w/thetaScaledJet t 0 w)
    ((thetaScaledJet t 2 z*thetaScaledJet t 0 z-
      thetaScaledJet t 1 z*thetaScaledJet t 1 z)/(thetaScaledJet t 0 z)^2) z at h
  rw [hv] at h
  rw [he]
  exact h

/-- The manuscript's product-series formula for the actual second logarithmic
derivative of its theta series, on its annulus of absolute convergence. -/
theorem thetaLogSecond_eq_jacobiSecondE {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hx : jacobiExp z ≠ 1) (hp : ‖jacobiNome t‖*‖jacobiExp z‖ < 1)
    (hm : ‖jacobiNome t‖*‖(jacobiExp z)⁻¹‖ < 1) :
    thetaLogSecond t z = -(Real.pi : ℂ)^2*jacobiSecondE (jacobiNome t) (jacobiExp z) := by
  have hz := thetaScaledJet_ne_zero_of_product_region ht hx hp hm
  have hd := jacobiThetaProduct_logDeriv_hasDerivAt (jacobiNome_norm_lt_one ht)
    (jacobiNome_ne_zero t) hx hp hm
  have hd' : HasDerivAt (logDeriv (thetaScaledJet t 0))
      ((Real.pi : ℂ)^2*jacobiSecondE (jacobiNome t) (jacobiExp z)) z := by
    apply hd.congr_of_eventuallyEq
    exact Eventually.of_forall (thetaScaledJet_logDeriv_eq_product ht)
  have h := (thetaScaledJet_logDeriv_hasDerivAt ht hz).unique hd'
  linear_combination -h

theorem weierstrassP_add_eta_eq_jacobiSecondE {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hx : jacobiExp z ≠ 1) (hp : ‖jacobiNome t‖*‖jacobiExp z‖ < 1)
    (hm : ‖jacobiNome t‖*‖(jacobiExp z)⁻¹‖ < 1) :
    (rhombicPeriodPair t ht).weierstrassP z+thetaEtaExpression t =
      -(Real.pi : ℂ)^2*jacobiSecondE (jacobiNome t) (jacobiExp z) := by
  rw [← thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz]
  exact thetaLogSecond_eq_jacobiSecondE ht hx hp hm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_eq_jacobiSecondE
#print axioms TwoAxisHelicoid.weierstrassP_add_eta_eq_jacobiSecondE
