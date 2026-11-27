import TwoAxisHelicoid.JacobiThetaLogDerivative

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiExp

noncomputable def jacobiSecondSum (q x : ℂ) : ℂ :=
  ∑' n : ℕ, q^(n+1)*x/(1-q^(n+1)*x)^2

noncomputable def jacobiSecondE (q x : ℂ) : ℂ :=
  x/(1-x)^2+jacobiSecondSum q x+jacobiSecondSum q x⁻¹

theorem jacobiSecondSum_eq_negEuler (q x : ℂ) :
    (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*x)^2)*x = -jacobiSecondSum q x := by
  rw [← tsum_mul_right, jacobiSecondSum, ← tsum_neg]
  apply tsum_congr
  intro n
  ring

theorem jacobiExp_fraction_hasDerivAt {z : ℂ} (hz : jacobiExp z ≠ 1) :
    HasDerivAt (fun w => jacobiExp w/(1-jacobiExp w))
      (I*(Real.pi : ℂ)*jacobiExp z/(1-jacobiExp z)^2) z := by
  have h := (jacobiExp_hasDerivAt z).div
    ((jacobiExp_hasDerivAt z).const_sub 1) (sub_ne_zero.mpr hz.symm)
  convert h using 1
  ring

theorem jacobiThetaProduct_logDeriv_hasDerivAt {q z : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hx : jacobiExp z ≠ 1)
    (hp : ‖q‖*‖jacobiExp z‖ < 1) (hm : ‖q‖*‖(jacobiExp z)⁻¹‖ < 1) :
    HasDerivAt (logDeriv (jacobiThetaProduct q))
      ((Real.pi : ℂ)^2*jacobiSecondE q (jacobiExp z)) z := by
  have hfrac := jacobiExp_fraction_hasDerivAt hx
  have hplus := (jacobiEulerLog_hasDerivAt hq hq0 hp).comp z (jacobiExp_hasDerivAt z)
  have hminus := (jacobiEulerLog_hasDerivAt hq hq0 hm).comp z (jacobiExp_inv_hasDerivAt z)
  have hd := (((hfrac.const_sub (-1/2)).add hplus).sub hminus).const_mul (I*(Real.pi : ℂ))
  have hformula : HasDerivAt (fun w : ℂ => I*(Real.pi : ℂ)*
      (-1/2-jacobiExp w/(1-jacobiExp w)+
        jacobiExp w*logDeriv (jacobiFactorProduct q) (jacobiExp w)-
        (jacobiExp w)⁻¹*logDeriv (jacobiFactorProduct q) ((jacobiExp w)⁻¹)))
      ((Real.pi : ℂ)^2*jacobiSecondE q (jacobiExp z)) z := by
    convert hd using 1
    · funext w
      rfl
    · rw [show (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*jacobiExp z)^2)*
          (I*(Real.pi : ℂ)*jacobiExp z) = I*Real.pi*
          ((∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*jacobiExp z)^2)*jacobiExp z) by ring]
      rw [show (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*(jacobiExp z)⁻¹)^2)*
          (-I*(Real.pi : ℂ)*(jacobiExp z)⁻¹) = -I*Real.pi*
          ((∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*(jacobiExp z)⁻¹)^2)*(jacobiExp z)⁻¹) by ring]
      rw [jacobiSecondSum_eq_negEuler, jacobiSecondSum_eq_negEuler]
      unfold jacobiSecondE
      ring_nf
      simp only [I_sq]
      ring
  apply hformula.congr_of_eventuallyEq
  have hc := (jacobiExp_hasDerivAt z).continuousAt
  have hi := (jacobiExp_inv_hasDerivAt z).continuousAt
  have hep := (continuousAt_const.mul hc.norm).eventually_lt_const hp
  have hem := (continuousAt_const.mul hi.norm).eventually_lt_const hm
  filter_upwards [hc.eventually_ne hx, hep, hem] with w hw hwp hwm
  exact jacobiThetaProduct_logDeriv hq hw hwp hwm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiThetaProduct_logDeriv_hasDerivAt
