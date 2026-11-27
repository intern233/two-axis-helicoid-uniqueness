import TwoAxisHelicoid.JacobiRatioIdentity
import TwoAxisHelicoid.ProductAnnulusBounds
import TwoAxisHelicoid.JacobiVerticalIdentity
import TwoAxisHelicoid.DualThetaKernel

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct thetaJet thetaScaledJet

theorem jacobiPairProduct_ne_zero {q x : ℂ} (hq : ‖q‖ < 1)
    (hp : ‖q‖*‖x‖ < 1) (hm : ‖q‖*‖x⁻¹‖ < 1) : jacobiPairProduct q x ≠ 0 := by
  unfold jacobiPairProduct
  exact mul_ne_zero (jacobiFactorProduct_ne_zero_of_norm hq hp)
    (jacobiFactorProduct_ne_zero_of_norm hq hm)

theorem jacobiThetaProduct_logDeriv_pair {q z : ℂ} (hq : ‖q‖ < 1)
    (hx : jacobiExp z ≠ 1) (hp : ‖q‖*‖jacobiExp z‖ < 1)
    (hm : ‖q‖*‖(jacobiExp z)⁻¹‖ < 1) :
    logDeriv (jacobiThetaProduct q) z = I*(Real.pi : ℂ)*
      (-1/2-jacobiExp z/(1-jacobiExp z)+
        jacobiExp z*logDeriv (jacobiPairProduct q) (jacobiExp z)) := by
  rw [jacobiThetaProduct_logDeriv hq hx hp hm,
    jacobiPairProduct_euler_logDeriv hq (jacobiExp_ne_zero z) hp hm]
  ring

noncomputable def dualProductR (t a : ℝ) : ℝ := Real.exp (-Real.pi*a/t)
noncomputable def dualProductKappa (t a : ℝ) : ℝ := Real.pi*(1-a)/t

/-- The actual dual period kernel, expressed using convergent Jacobi products.
The rational form in the exponential avoids subtraction of large theta jets. -/
noncomputable def dualProductIntegrand (t a : ℝ) (w : ℂ) : ℂ :=
  ((Real.pi : ℂ)^2/(t : ℂ)^2)*
    jacobiNormalization (jacobiNome (1/t)) (dualProductR t a)*
    (jacobiExp w/(1-jacobiExp w))^2*
    (((1-(dualProductR t a : ℂ)*jacobiExp w)*
      jacobiPairProduct (jacobiNome (1/t)) ((dualProductR t a : ℂ)*jacobiExp w))/
        jacobiPairProduct (jacobiNome (1/t)) (jacobiExp w))^2*
    Complex.exp ((dualProductKappa t a : ℂ)*
      (-1+2/(1-jacobiExp w)-2*jacobiExp w*
        logDeriv (jacobiPairProduct (jacobiNome (1/t))) (jacobiExp w)))

theorem dual_product_abscissa_exp {t : ℝ} (ht : 0 < t) (a : ℝ) :
    jacobiExp (-dualAbscissa t a) = (dualProductR t a : ℂ) := by
  rw [dualAbscissa_eq ht]
  have he : -(-I*(a : ℂ)/t) = I*a/t := by ring
  rw [he, jacobiExp_imaginary_quotient]
  rfl

theorem dualThetaA_eq_product {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    {w : ℂ} (hx : jacobiExp w ≠ 1)
    (hp : ‖jacobiNome (1/t)‖*‖jacobiExp w‖ < 1)
    (hm : ‖jacobiNome (1/t)‖*‖(jacobiExp w)⁻¹‖ < 1) :
    dualThetaA t a w = dualProductIntegrand t a w := by
  let s : ℝ := 1/t
  let b : ℂ := dualAbscissa t a
  let Q : ℂ := jacobiNome s
  have hs : 0 < s := one_div_pos.mpr ht
  have hQ : ‖Q‖ < 1 := jacobiNome_norm_lt_one hs
  have hb : -b = I*a/t := by
    dsimp [b]
    rw [dualAbscissa_eq ht]
    ring
  have hreg := jacobi_vertical_region ht ha0 ha1
  rw [← hb] at hreg
  have hDr : jacobiPairProduct Q (jacobiExp (-b)) ≠ 0 :=
    jacobiPairProduct_ne_zero hQ hreg.2.1 hreg.2.2
  have hDx : jacobiPairProduct Q (jacobiExp w) ≠ 0 :=
    jacobiPairProduct_ne_zero hQ hp hm
  have hratio := thetaScaledJet_ratio_eq_product hs b w
  have hraw : ((Real.pi*thetaJet s 1 0)/(2*thetaJet s 0 (Real.pi*b/2)))^2*
      (thetaJet s 0 (Real.pi*(w-b)/2)/thetaJet s 0 (Real.pi*w/2))^2 =
      (deriv (rhombicProductTheta s) 0/rhombicProductTheta s b)^2*
        (rhombicProductTheta s (w-b)/rhombicProductTheta s w)^2 := by
    convert hratio using 1
    simp only [thetaScaledJet, pow_one, pow_zero, one_mul, mul_zero]
    rw [show (Real.pi/2 : ℂ)*b = Real.pi*b/2 by ring,
      show (Real.pi/2 : ℂ)*(w-b) = Real.pi*(w-b)/2 by ring,
      show (Real.pi/2 : ℂ)*w = Real.pi*w/2 by ring]
    ring
  have hprod := jacobiThetaProduct_normalized_ratio hQ hreg.1 hx hDr hDx
  have hlog := jacobiThetaProduct_logDeriv_pair hQ hx hp hm
  have htwo : Complex.exp (2*(Real.pi : ℂ)*I*w) = (jacobiExp w)^2 := by
    rw [jacobiExp, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hexp : 2*(Real.pi : ℂ)*I*w+
      I*(dualProductKappa t a : ℂ)*((2/(Real.pi : ℂ))*
        (I*(Real.pi : ℂ)*(-1/2-jacobiExp w/(1-jacobiExp w)+
          jacobiExp w*logDeriv (jacobiPairProduct Q) (jacobiExp w)))) =
      2*(Real.pi : ℂ)*I*w+(dualProductKappa t a : ℂ)*
        (-1+2/(1-jacobiExp w)-2*jacobiExp w*logDeriv (jacobiPairProduct Q) (jacobiExp w)) := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, sub_ne_zero.mpr hx.symm]
    ring_nf
    simp only [I_sq]
    ring
  change -(1 : ℂ)/(t : ℂ)^2*
    ((((Real.pi*thetaJet s 1 0)/(2*thetaJet s 0 (Real.pi*b/2)))^2*
      (thetaJet s 0 (Real.pi*(w-b)/2)/thetaJet s 0 (Real.pi*w/2))^2)*
      Complex.exp (2*Real.pi*I*w+I*(dualProductKappa t a : ℂ)*
        thetaQuotient s 1 (Real.pi*w/2))) = _
  rw [hraw, thetaQuotient_eq_product_logDeriv hs]
  change -(1 : ℂ)/(t : ℂ)^2*
    (((deriv (jacobiThetaProduct Q) 0/jacobiThetaProduct Q b)^2*
      (jacobiThetaProduct Q (w-b)/jacobiThetaProduct Q w)^2)*
      Complex.exp (2*Real.pi*I*w+I*(dualProductKappa t a : ℂ)*
        ((2/(Real.pi : ℂ))*logDeriv (jacobiThetaProduct Q) w))) = _
  rw [hprod, hlog, hexp, Complex.exp_add, htwo]
  have hr : jacobiExp (-b) = (dualProductR t a : ℂ) := dual_product_abscissa_exp ht a
  rw [hr]
  unfold dualProductIntegrand
  change _ = _
  dsimp only [Q, s] at hDx ⊢
  field_simp [sub_ne_zero.mpr hx.symm, hDx]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.dualThetaA_eq_product
