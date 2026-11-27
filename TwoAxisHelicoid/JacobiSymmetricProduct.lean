import TwoAxisHelicoid.JacobiThetaSecondLogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct

noncomputable def jacobiSymmetricProduct (q z : ℂ) : ℂ :=
  jacobiFactorProduct q (jacobiExp z)*jacobiFactorProduct q (jacobiExp z)⁻¹

theorem jacobiSymmetricProduct_differentiable {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (jacobiSymmetricProduct q) := by
  intro z
  exact (((jacobiFactorProduct_differentiable hq _).hasDerivAt.comp z
    (jacobiExp_hasDerivAt z)).mul
      ((jacobiFactorProduct_differentiable hq _).hasDerivAt.comp z
        (jacobiExp_inv_hasDerivAt z))).differentiableAt

theorem jacobiSymmetricProduct_zero_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    jacobiSymmetricProduct q 0 ≠ 0 := by
  have hn := jacobiFactorProduct_ne_zero_of_norm hq
    (show ‖q‖*‖(1 : ℂ)‖ < 1 by simpa using hq)
  simpa [jacobiSymmetricProduct,jacobiExp] using mul_ne_zero hn hn

theorem jacobiSymmetricProduct_logDeriv {q z : ℂ} (hq : ‖q‖ < 1)
    (hp : ‖q‖*‖jacobiExp z‖ < 1) (hm : ‖q‖*‖(jacobiExp z)⁻¹‖ < 1) :
    logDeriv (jacobiSymmetricProduct q) z = I*(Real.pi : ℂ)*
      (jacobiExp z*logDeriv (jacobiFactorProduct q) (jacobiExp z)-
        (jacobiExp z)⁻¹*logDeriv (jacobiFactorProduct q) (jacobiExp z)⁻¹) := by
  have hd := ((jacobiFactorProduct_differentiable hq _).hasDerivAt.comp z
    (jacobiExp_hasDerivAt z)).mul
      ((jacobiFactorProduct_differentiable hq _).hasDerivAt.comp z
        (jacobiExp_inv_hasDerivAt z))
  have hnp := jacobiFactorProduct_ne_zero_of_norm hq hp
  have hnm := jacobiFactorProduct_ne_zero_of_norm hq hm
  change HasDerivAt (jacobiSymmetricProduct q) _ z at hd
  rw [logDeriv_apply,hd.deriv]
  simp only [jacobiSymmetricProduct,logDeriv_apply,Function.comp_apply]
  field_simp [hnp,hnm]
  ring

theorem jacobiSymmetricProduct_deriv_zero {q : ℂ} (hq : ‖q‖ < 1) :
    deriv (jacobiSymmetricProduct q) 0 = 0 := by
  have h := jacobiSymmetricProduct_logDeriv (z := 0) hq
    (by simpa [jacobiExp] using hq) (by simpa [jacobiExp] using hq)
  simp only [jacobiExp,mul_zero,Complex.exp_zero,inv_one,one_mul,sub_self,mul_zero,
    logDeriv_apply,div_eq_zero_iff] at h
  exact h.resolve_right (jacobiSymmetricProduct_zero_ne_zero hq)

theorem jacobiSymmetricProduct_logDeriv_hasDerivAt_zero {q : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt (logDeriv (jacobiSymmetricProduct q))
      (2*(Real.pi : ℂ)^2*jacobiSecondSum q 1) 0 := by
  have hx : jacobiExp (0 : ℂ) = 1 := by simp [jacobiExp]
  have hE := jacobiEulerLog_hasDerivAt (x := 1) hq hq0 (by simpa using hq)
  have hp := (show HasDerivAt (fun y => y*logDeriv (jacobiFactorProduct q) y)
      (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*1)^2) (jacobiExp 0) by rwa [hx]).comp 0
    (jacobiExp_hasDerivAt 0)
  have hm := (show HasDerivAt (fun y => y*logDeriv (jacobiFactorProduct q) y)
      (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*1)^2) (jacobiExp 0)⁻¹ by rwa [hx,inv_one]).comp 0
    (jacobiExp_inv_hasDerivAt 0)
  have hd := (hp.sub hm).const_mul (I*(Real.pi : ℂ))
  have hs : (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*1)^2) = -jacobiSecondSum q 1 := by
    simpa only [mul_one] using jacobiSecondSum_eq_negEuler q 1
  rw [hs] at hd
  have hval : I*(Real.pi : ℂ)*
      ((-jacobiSecondSum q 1)*(I*(Real.pi : ℂ))-
        (-jacobiSecondSum q 1)*(-I*(Real.pi : ℂ))) =
      2*(Real.pi : ℂ)^2*jacobiSecondSum q 1 := by
    ring_nf
    simp only [I_sq]
    ring
  simp only [hx,inv_one,mul_one] at hd
  rw [hval] at hd
  apply hd.congr_of_eventuallyEq
  have hc := (jacobiExp_hasDerivAt 0).continuousAt
  have hi := (jacobiExp_inv_hasDerivAt 0).continuousAt
  have hpb : ‖q‖*‖jacobiExp (0 : ℂ)‖ < 1 := by simpa [hx] using hq
  have hmb : ‖q‖*‖(jacobiExp (0 : ℂ))⁻¹‖ < 1 := by simpa [hx] using hq
  filter_upwards [(continuousAt_const.mul hc.norm).eventually_lt_const hpb,
    (continuousAt_const.mul hi.norm).eventually_lt_const hmb] with z hz hz'
  exact jacobiSymmetricProduct_logDeriv hq hz hz'

theorem jacobiSymmetricProduct_second_zero {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    iteratedDeriv 2 (jacobiSymmetricProduct q) 0 =
      2*(Real.pi : ℂ)^2*jacobiSecondSum q 1*jacobiSymmetricProduct q 0 := by
  have ha := (jacobiSymmetricProduct_differentiable hq).analyticAt 0
  have hd := ha.deriv.differentiableAt.hasDerivAt.div ha.differentiableAt.hasDerivAt
    (jacobiSymmetricProduct_zero_ne_zero hq)
  change HasDerivAt (logDeriv (jacobiSymmetricProduct q)) _ 0 at hd
  have he := (jacobiSymmetricProduct_logDeriv_hasDerivAt_zero hq hq0).unique hd
  rw [jacobiSymmetricProduct_deriv_zero hq] at he
  simp only [zero_mul,sub_zero] at he
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  field_simp [jacobiSymmetricProduct_zero_ne_zero hq] at he
  exact he.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiSymmetricProduct_second_zero
