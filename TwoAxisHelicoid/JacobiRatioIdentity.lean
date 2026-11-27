import TwoAxisHelicoid.JacobiThetaLogDerivative

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct thetaScaledJet

theorem jacobiExp_neg (z : ℂ) : jacobiExp (-z) = (jacobiExp z)⁻¹ := by
  simp only [jacobiExp, mul_neg, Complex.exp_neg]

theorem jacobiExp_sub (w b : ℂ) : jacobiExp (w-b) = jacobiExp (-b)*jacobiExp w := by
  unfold jacobiExp
  rw [← Complex.exp_add]
  congr 1
  ring

theorem jacobiPairProduct_inv (q x : ℂ) : jacobiPairProduct q x⁻¹ = jacobiPairProduct q x := by
  simp only [jacobiPairProduct, inv_inv, mul_comm]

theorem jacobiThetaProduct_eq_pair (q z : ℂ) :
    jacobiThetaProduct q z = Complex.exp (-I*(Real.pi : ℂ)*z/2)*
      (1-jacobiExp z)*jacobiPairProduct q (jacobiExp z) := by
  simp only [jacobiThetaProduct, jacobiThetaProductCore, jacobiPairProduct, jacobiExp]
  ring

theorem jacobiThetaProduct_neg (q z : ℂ) : jacobiThetaProduct q (-z) = -jacobiThetaProduct q z := by
  rw [jacobiThetaProduct_eq_pair, jacobiThetaProduct_eq_pair, jacobiExp_neg,
    jacobiPairProduct_inv]
  have he : Complex.exp (-I*(Real.pi : ℂ)*(-z)/2) =
      Complex.exp (-I*(Real.pi : ℂ)*z/2)*jacobiExp z := by
    rw [jacobiExp, ← Complex.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [jacobiExp_ne_zero z]
  ring

theorem jacobiThetaProduct_ratio {q b w : ℂ}
    (hr : jacobiExp (-b) ≠ 1) (hx : jacobiExp w ≠ 1)
    (hDr : jacobiPairProduct q (jacobiExp (-b)) ≠ 0)
    (hDx : jacobiPairProduct q (jacobiExp w) ≠ 0) :
    jacobiThetaProduct q (w-b)/(jacobiThetaProduct q w*jacobiThetaProduct q (-b)) =
      ((1-jacobiExp (-b)*jacobiExp w)*jacobiPairProduct q (jacobiExp (-b)*jacobiExp w))/
        ((1-jacobiExp w)*jacobiPairProduct q (jacobiExp w)*
          (1-jacobiExp (-b))*jacobiPairProduct q (jacobiExp (-b))) := by
  rw [jacobiThetaProduct_eq_pair, jacobiThetaProduct_eq_pair, jacobiThetaProduct_eq_pair,
    jacobiExp_sub]
  have he : Complex.exp (-I*(Real.pi : ℂ)*(w-b)/2) =
      Complex.exp (-I*(Real.pi : ℂ)*w/2)*Complex.exp (-I*(Real.pi : ℂ)*(-b)/2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [Complex.exp_ne_zero, sub_ne_zero.mpr hr.symm, sub_ne_zero.mpr hx.symm, hDr, hDx]

noncomputable def jacobiNormalization (q r : ℂ) : ℂ :=
  (jacobiFactorProduct q 1)^4/((1-r)^2*(jacobiPairProduct q r)^2)

theorem jacobiThetaProduct_normalized_ratio {q b w : ℂ} (hq : ‖q‖ < 1)
    (hr : jacobiExp (-b) ≠ 1) (hx : jacobiExp w ≠ 1)
    (hDr : jacobiPairProduct q (jacobiExp (-b)) ≠ 0)
    (hDx : jacobiPairProduct q (jacobiExp w) ≠ 0) :
    (deriv (jacobiThetaProduct q) 0/jacobiThetaProduct q b)^2*
      (jacobiThetaProduct q (w-b)/jacobiThetaProduct q w)^2 =
      -(Real.pi : ℂ)^2*jacobiNormalization q (jacobiExp (-b))*
        (((1-jacobiExp (-b)*jacobiExp w)*jacobiPairProduct q (jacobiExp (-b)*jacobiExp w))/
          ((1-jacobiExp w)*jacobiPairProduct q (jacobiExp w)))^2 := by
  have hratio := jacobiThetaProduct_ratio hr hx hDr hDx
  have hneg := jacobiThetaProduct_neg q b
  rw [hneg] at hratio
  have he : (deriv (jacobiThetaProduct q) 0/jacobiThetaProduct q b)^2*
      (jacobiThetaProduct q (w-b)/jacobiThetaProduct q w)^2 =
      (deriv (jacobiThetaProduct q) 0)^2*
        (jacobiThetaProduct q (w-b)/(jacobiThetaProduct q w*(-jacobiThetaProduct q b)))^2 := by
    ring
  rw [he, hratio, (jacobiThetaProduct_hasDerivAt_zero hq).deriv]
  unfold jacobiNormalization
  simp only [mul_pow, neg_sq, I_sq]
  field_simp [sub_ne_zero.mpr hr.symm, sub_ne_zero.mpr hx.symm, hDr, hDx]

theorem thetaScaledJet_ratio_eq_product {t : ℝ} (ht : 0 < t) (b w : ℂ) :
    (thetaScaledJet t 1 0/thetaScaledJet t 0 b)^2*
      (thetaScaledJet t 0 (w-b)/thetaScaledJet t 0 w)^2 =
      (deriv (rhombicProductTheta t) 0/rhombicProductTheta t b)^2*
        (rhombicProductTheta t (w-b)/rhombicProductTheta t w)^2 := by
  let c : ℂ := deriv (rhombicProductTheta t) 0/thetaScaledJet t 1 0
  have hc : c ≠ 0 := jacobiTheta_normalization_ne_zero ht
  have hd : deriv (rhombicProductTheta t) 0 = c*thetaScaledJet t 1 0 := by
    dsimp [c]
    rw [div_mul_cancel₀ _ (thetaScaledJet_one_ne_zero_of_pos ht)]
  rw [hd, rhombicProductTheta_eq_scaled_theta ht b,
    rhombicProductTheta_eq_scaled_theta ht (w-b), rhombicProductTheta_eq_scaled_theta ht w]
  change _ = ((c*thetaScaledJet t 1 0)/(c*thetaScaledJet t 0 b))^2*
    ((c*thetaScaledJet t 0 (w-b))/(c*thetaScaledJet t 0 w))^2
  simp only [mul_div_mul_left _ _ hc]

theorem thetaQuotient_eq_product_logDeriv {t : ℝ} (ht : 0 < t) (w : ℂ) :
    thetaQuotient t 1 (Real.pi*w/2) =
      (2/(Real.pi : ℂ))*logDeriv (rhombicProductTheta t) w := by
  rw [← thetaScaledJet_logDeriv_eq_product ht, logDeriv_apply,
    (thetaScaledJet_hasDerivAt ht 0 w).deriv]
  unfold thetaScaledJet thetaQuotient
  simp only [Nat.zero_add, pow_zero, pow_one, one_mul]
  rw [show (Real.pi/2 : ℂ)*w = Real.pi*w/2 by ring]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiThetaProduct_normalized_ratio
#print axioms TwoAxisHelicoid.thetaScaledJet_ratio_eq_product
#print axioms TwoAxisHelicoid.thetaQuotient_eq_product_logDeriv
