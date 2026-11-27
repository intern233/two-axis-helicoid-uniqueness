import TwoAxisHelicoid.LeftProductError
import TwoAxisHelicoid.DualHorizontalPeriod

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct

noncomputable def dualProductMainTerm (t a : ℝ) (w : ℂ) : ℂ :=
  ((Real.pi : ℂ)^2/(t : ℂ)^2)*(jacobiExp w/(1-jacobiExp w))^2*
    Complex.exp ((dualProductKappa t a : ℂ)*(-1+2/(1-jacobiExp w)))

theorem dualProductIntegrand_factor (t a : ℝ) (w : ℂ) :
    dualProductIntegrand t a w = dualProductMainTerm t a w*
      jacobiProductError (jacobiNome (1/t)) (dualProductR t a) (dualProductKappa t a) (jacobiExp w) := by
  unfold dualProductIntegrand dualProductMainTerm jacobiProductError
  have he : (dualProductKappa t a : ℂ)*
      (-1+2/(1-jacobiExp w)-2*jacobiExp w*logDeriv (jacobiPairProduct (jacobiNome (1/t))) (jacobiExp w)) =
      (dualProductKappa t a : ℂ)*(-1+2/(1-jacobiExp w))+
        (-2*(dualProductKappa t a : ℂ)*jacobiExp w*logDeriv (jacobiPairProduct (jacobiNome (1/t))) (jacobiExp w)) := by ring
  rw [he, Complex.exp_add]
  ring

noncomputable def leftComparisonFunction (t : ℝ) (w : ℂ) : ℂ :=
  I*t*dualProductMainTerm t (verticalA t) w

theorem leftComparisonFunction_eq_original {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hx : jacobiExp w ≠ 1) :
    leftComparisonFunction t w =
      (I*(Real.pi : ℂ)^2/((t : ℂ)*(leftBeta t : ℂ)))*
        ((jacobiExp w)^2/(1-jacobiExp w)^2)*
        Complex.exp (2*(leftKappa t : ℂ)*jacobiExp w/(1-jacobiExp w)) := by
  have he : (leftKappa t : ℂ)*(-1+2/(1-jacobiExp w)) =
      (leftKappa t : ℂ)+2*(leftKappa t : ℂ)*jacobiExp w/(1-jacobiExp w) := by
    field_simp [sub_ne_zero.mpr hx.symm]
    ring
  have hExp : Complex.exp (leftKappa t : ℂ) = (leftBeta t : ℂ)⁻¹ := by
    have h := exp_neg_leftKappa t
    rw [Real.exp_neg] at h
    rw [← Complex.ofReal_exp, ← Complex.ofReal_inv, ← h, inv_inv]
  unfold leftComparisonFunction dualProductMainTerm
  rw [← leftKappa_eq_dualProductKappa ht, he, Complex.exp_add, hExp]
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne', Complex.ofReal_ne_zero.mpr (leftBeta_pos t).ne',
    sub_ne_zero.mpr hx.symm]

/-- Exact manuscript factorization F = F₀ E, with the original differential scale. -/
theorem actual_dual_comparison_factorization {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    {w : ℂ} (hx : jacobiExp w ≠ 1)
    (hp : ‖jacobiNome (1/t)‖*‖jacobiExp w‖ < 1)
    (hm : ‖jacobiNome (1/t)‖*‖(jacobiExp w)⁻¹‖ < 1) :
    I*t*dualThetaA t (verticalA t) w = leftComparisonFunction t w*
      jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t) (jacobiExp w) := by
  have ha := (verticalA_spec (small_height_mem_vertical_domain ht (by linarith))).1
  rw [dualThetaA_eq_product ht ha.1 ha.2 hx hp hm, dualProductIntegrand_factor]
  rw [← leftKappa_eq_dualProductKappa ht]
  simp only [leftComparisonFunction, dualProductR, leftRootR, mul_assoc]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparisonFunction_eq_original
#print axioms TwoAxisHelicoid.actual_dual_comparison_factorization
