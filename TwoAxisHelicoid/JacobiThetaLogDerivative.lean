import TwoAxisHelicoid.JacobiProductIdentity
import TwoAxisHelicoid.JacobiSecondLogDerivative

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct thetaScaledJet

noncomputable def jacobiExp (z : ℂ) : ℂ := Complex.exp (I*(Real.pi : ℂ)*z)

theorem jacobiExp_ne_zero (z : ℂ) : jacobiExp z ≠ 0 := Complex.exp_ne_zero _

theorem jacobiExp_hasDerivAt (z : ℂ) :
    HasDerivAt jacobiExp (I*(Real.pi : ℂ)*jacobiExp z) z := by
  unfold jacobiExp
  have h := ((hasDerivAt_id z).const_mul (I*(Real.pi : ℂ))).cexp
  simpa only [id_eq, mul_one, mul_comm] using h

theorem jacobiExp_inv_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w => (jacobiExp w)⁻¹) (-I*(Real.pi : ℂ)*(jacobiExp z)⁻¹) z := by
  convert (jacobiExp_hasDerivAt z).inv (jacobiExp_ne_zero z) using 1
  field_simp

theorem jacobiThetaProduct_logDeriv {q z : ℂ} (hq : ‖q‖ < 1)
    (hx : jacobiExp z ≠ 1) (hp : ‖q‖*‖jacobiExp z‖ < 1)
    (hm : ‖q‖*‖(jacobiExp z)⁻¹‖ < 1) :
    logDeriv (jacobiThetaProduct q) z = I*(Real.pi : ℂ)*
      (-1/2-jacobiExp z/(1-jacobiExp z)+
        jacobiExp z*logDeriv (jacobiFactorProduct q) (jacobiExp z)-
        (jacobiExp z)⁻¹*logDeriv (jacobiFactorProduct q) ((jacobiExp z)⁻¹)) := by
  let u : ℂ → ℂ := fun w => Complex.exp (-I*(Real.pi : ℂ)*w/2)
  let v : ℂ → ℂ := fun w => 1-jacobiExp w
  let p : ℂ → ℂ := fun w => jacobiFactorProduct q (jacobiExp w)
  let m : ℂ → ℂ := fun w => jacobiFactorProduct q ((jacobiExp w)⁻¹)
  have hu : HasDerivAt u ((-I*(Real.pi : ℂ)/2)*u z) z := by
    have h := (((hasDerivAt_id z).const_mul (-I*(Real.pi : ℂ))).div_const 2).cexp
    convert h using 1
    · rfl
    · dsimp [u]
      ring
  have hv : HasDerivAt v (-(I*(Real.pi : ℂ)*jacobiExp z)) z :=
    (jacobiExp_hasDerivAt z).const_sub 1
  have hdp : HasDerivAt p
      (deriv (jacobiFactorProduct q) (jacobiExp z)*(I*(Real.pi : ℂ)*jacobiExp z)) z :=
    ((jacobiFactorProduct_differentiable hq (jacobiExp z)).hasDerivAt).comp z
      (jacobiExp_hasDerivAt z)
  have hdm : HasDerivAt m
      (deriv (jacobiFactorProduct q) ((jacobiExp z)⁻¹)*(-I*(Real.pi : ℂ)*(jacobiExp z)⁻¹)) z :=
    ((jacobiFactorProduct_differentiable hq ((jacobiExp z)⁻¹)).hasDerivAt).comp z
      (jacobiExp_inv_hasDerivAt z)
  have hd := ((hu.mul hv).mul hdp).mul hdm
  have he : jacobiThetaProduct q = (u*v)*(p*m) := by
    funext w
    simp only [u, v, p, m, Pi.mul_apply, jacobiThetaProduct, jacobiThetaProductCore, jacobiExp]
    ring
  have hneU : u z ≠ 0 := Complex.exp_ne_zero _
  have hneV : v z ≠ 0 := sub_ne_zero.mpr hx.symm
  have hneP : p z ≠ 0 := jacobiFactorProduct_ne_zero_of_norm hq hp
  have hneM : m z ≠ 0 := jacobiFactorProduct_ne_zero_of_norm hq hm
  have he' : jacobiThetaProduct q = ((u*v)*p)*m := by rw [he]; exact mul_assoc _ _ _ |>.symm
  rw [he', logDeriv_apply, hd.deriv]
  simp only [Pi.mul_apply, logDeriv_apply]
  dsimp only [u, v, p, m] at hneU hneV hneP hneM ⊢
  field_simp [hneU, hneV, hneP, hneM, jacobiExp_ne_zero z]
  ring

theorem thetaScaledJet_logDeriv_eq_product {t : ℝ} (ht : 0 < t) (z : ℂ) :
    logDeriv (thetaScaledJet t 0) z = logDeriv (rhombicProductTheta t) z := by
  have he : rhombicProductTheta t = fun w =>
      (deriv (rhombicProductTheta t) 0 / thetaScaledJet t 1 0)*thetaScaledJet t 0 w :=
    funext (rhombicProductTheta_eq_scaled_theta ht)
  rw [he, logDeriv_const_mul z _ (jacobiTheta_normalization_ne_zero ht)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiThetaProduct_logDeriv
#print axioms TwoAxisHelicoid.thetaScaledJet_logDeriv_eq_product
