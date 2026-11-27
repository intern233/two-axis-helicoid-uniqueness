import TwoAxisHelicoid.JacobiProductBasic

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 0

noncomputable def jacobiThetaProductCore (q x : ℂ) : ℂ :=
  (1-x)*jacobiFactorProduct q x*jacobiFactorProduct q x⁻¹

theorem jacobiThetaProductCore_shift {q x : ℂ} (hq : ‖q‖ < 1)
    (hq0 : q ≠ 0) (hx : x ≠ 0) :
    jacobiThetaProductCore q (q*x) = -x⁻¹*jacobiThetaProductCore q x := by
  have he : q*(q*x)⁻¹ = x⁻¹ := by field_simp
  have hs := jacobiFactorProduct_shift hq ((q*x)⁻¹)
  rw [he] at hs
  unfold jacobiThetaProductCore
  rw [jacobiFactorProduct_shift hq x, ← hs]
  field_simp
  ring

theorem jacobiThetaProductCore_one (q : ℂ) : jacobiThetaProductCore q 1 = 0 := by
  simp [jacobiThetaProductCore]

noncomputable def jacobiThetaProduct (q z : ℂ) : ℂ :=
  Complex.exp (-Complex.I*(Real.pi : ℂ)*z/2) *
    jacobiThetaProductCore q (Complex.exp (Complex.I*(Real.pi : ℂ)*z))

theorem jacobiThetaProduct_zero (q : ℂ) : jacobiThetaProduct q 0 = 0 := by
  simp [jacobiThetaProduct, jacobiThetaProductCore]

theorem jacobiThetaProduct_differentiable {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (jacobiThetaProduct q) := by
  unfold jacobiThetaProduct jacobiThetaProductCore
  apply Differentiable.mul (by fun_prop)
  apply Differentiable.mul
  · exact (show Differentiable ℂ (fun z : ℂ => 1-Complex.exp (I*(Real.pi : ℂ)*z)) by
      fun_prop).mul ((jacobiFactorProduct_differentiable hq).comp (by fun_prop))
  · exact (jacobiFactorProduct_differentiable hq).comp
      ((show Differentiable ℂ (fun z : ℂ => Complex.exp (I*(Real.pi : ℂ)*z)) by
        fun_prop).inv (fun z => Complex.exp_ne_zero _))

theorem jacobiThetaProduct_hasDerivAt_zero {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (jacobiThetaProduct q)
      (-I*(Real.pi : ℂ)*(jacobiFactorProduct q 1)^2) 0 := by
  have he : HasDerivAt (fun z : ℂ => Complex.exp (I*(Real.pi : ℂ)*z))
      (I*(Real.pi : ℂ)) 0 := by
    simpa only [id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℂ)).const_mul (I*(Real.pi : ℂ))).cexp
  have hp : Differentiable ℂ (fun z : ℂ =>
      jacobiFactorProduct q (Complex.exp (I*(Real.pi : ℂ)*z))) :=
    (jacobiFactorProduct_differentiable hq).comp (by fun_prop)
  have hn : Differentiable ℂ (fun z : ℂ =>
      jacobiFactorProduct q ((Complex.exp (I*(Real.pi : ℂ)*z))⁻¹)) :=
    (jacobiFactorProduct_differentiable hq).comp
      ((show Differentiable ℂ (fun z : ℂ => Complex.exp (I*(Real.pi : ℂ)*z)) by
        fun_prop).inv (fun z => Complex.exp_ne_zero _))
  have hs : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-I*(Real.pi : ℂ)*z/2)) 0 := by
    fun_prop
  have hd := ((hs.hasDerivAt.mul ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub he)).mul
    (hp 0).hasDerivAt).mul (hn 0).hasDerivAt
  convert hd using 1
  · funext z
    simp only [jacobiThetaProduct, jacobiThetaProductCore, Pi.mul_apply, Pi.sub_apply]
    ring
  · simp only [Pi.mul_apply, Pi.sub_apply, mul_zero, zero_div, Complex.exp_zero,
      sub_self, zero_mul, zero_add, one_mul, inv_one, add_zero, zero_sub]
    ring

theorem jacobiThetaProduct_deriv_zero_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    deriv (jacobiThetaProduct q) 0 ≠ 0 := by
  rw [(jacobiThetaProduct_hasDerivAt_zero hq).deriv]
  apply mul_ne_zero
  · exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · apply pow_ne_zero
    apply jacobiFactorProduct_ne_zero_of_norm hq
    simpa only [norm_one, mul_one] using hq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiThetaProductCore_shift
#print axioms TwoAxisHelicoid.jacobiThetaProduct_hasDerivAt_zero
