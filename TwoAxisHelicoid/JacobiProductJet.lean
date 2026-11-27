import TwoAxisHelicoid.JacobiSymmetricProduct

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiSymmetricProduct

noncomputable def jacobiSineFactor (z : ℂ) : ℂ :=
  exp ((-I*(Real.pi : ℂ)/2)*z)-exp ((I*(Real.pi : ℂ)/2)*z)

theorem jacobiSineFactor_analyticAt (z : ℂ) : AnalyticAt ℂ jacobiSineFactor z := by
  unfold jacobiSineFactor
  fun_prop

theorem jacobiSineFactor_jet_zero (n : ℕ) :
    iteratedDeriv n jacobiSineFactor 0 =
      (-I*(Real.pi : ℂ)/2)^n-(I*(Real.pi : ℂ)/2)^n := by
  unfold jacobiSineFactor
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_cexp_const_mul,iteratedDeriv_cexp_const_mul]
  simp

theorem jacobiThetaProduct_eq_sine_mul (q : ℂ) :
    jacobiThetaProduct q = jacobiSineFactor*jacobiSymmetricProduct q := by
  funext z
  have he : exp ((-I*(Real.pi : ℂ)/2)*z)*exp (I*(Real.pi : ℂ)*z) =
      exp ((I*(Real.pi : ℂ)/2)*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [jacobiThetaProduct,jacobiThetaProductCore,jacobiSineFactor,
    jacobiSymmetricProduct,jacobiExp,Pi.mul_apply,
    show -I*(Real.pi : ℂ)*z/2 = (-I*(Real.pi : ℂ)/2)*z by ring]
  rw [sub_mul,← he]
  ring

theorem jacobiThetaProduct_third_zero {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    iteratedDeriv 3 (jacobiThetaProduct q) 0 =
      (-(Real.pi : ℂ)^2/4+6*(Real.pi : ℂ)^2*jacobiSecondSum q 1)*
        deriv (jacobiThetaProduct q) 0 := by
  have hR := (jacobiSymmetricProduct_differentiable hq).analyticAt 0
  have h3 := iteratedDeriv_mul
    (n := 3) (jacobiSineFactor_analyticAt 0).contDiffAt hR.contDiffAt
  rw [← jacobiThetaProduct_eq_sine_mul q] at h3
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose,
    Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat,jacobiSineFactor_jet_zero,
    pow_zero,sub_self,zero_mul,zero_add,mul_one,one_mul] at h3
  rw [jacobiSymmetricProduct_second_zero hq hq0] at h3
  have h1 := (jacobiSineFactor_analyticAt 0).differentiableAt.hasDerivAt.mul
    hR.differentiableAt.hasDerivAt
  have h10 : deriv jacobiSineFactor 0 = -I*(Real.pi : ℂ) := by
    simpa only [iteratedDeriv_one,pow_one] using jacobiSineFactor_jet_zero 1 |>.trans (by ring)
  have hS0 : jacobiSineFactor 0 = 0 := by simp [jacobiSineFactor]
  rw [jacobiThetaProduct_eq_sine_mul q,h1.deriv,h10,hS0,zero_mul,add_zero]
  rw [← jacobiThetaProduct_eq_sine_mul q,h3]
  simp only [iteratedDeriv_one,jacobiSymmetricProduct_deriv_zero hq,mul_zero,add_zero,
    iteratedDeriv_zero]
  ring_nf; norm_num [I_sq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiThetaProduct_third_zero
