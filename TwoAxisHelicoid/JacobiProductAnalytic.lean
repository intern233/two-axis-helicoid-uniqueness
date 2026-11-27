import TwoAxisHelicoid.JacobiProductErrorBounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct

theorem jacobiPairProduct_analyticAt {q x : ℂ} (hq : ‖q‖ < 1) (hx : x ≠ 0) :
    AnalyticAt ℂ (jacobiPairProduct q) x := by
  apply (jacobiPairProduct_differentiableOn hq).analyticAt
  exact isOpen_ne.mem_nhds hx

theorem jacobiPairProduct_logDeriv_differentiableAt {q x : ℂ}
    (hq : ‖q‖ < 1) (hx : x ≠ 0) (hp : ‖q‖*‖x‖ < 1) (hm : ‖q‖*‖x⁻¹‖ < 1) :
    DifferentiableAt ℂ (logDeriv (jacobiPairProduct q)) x := by
  have ha := jacobiPairProduct_analyticAt hq hx
  exact ha.deriv.differentiableAt.div ha.differentiableAt (jacobiPairProduct_ne_zero hq hp hm)

theorem jacobiProductError_differentiableAt {q r x : ℂ} (k : ℝ)
    (hq : ‖q‖ < 1) (hr : r ≠ 0) (hx : x ≠ 0)
    (hp : ‖q‖*‖x‖ < 1) (hm : ‖q‖*‖x⁻¹‖ < 1) :
    DifferentiableAt ℂ (jacobiProductError q r k) x := by
  have hD := (jacobiPairProduct_analyticAt hq hx).differentiableAt
  have hDs := (jacobiPairProduct_analyticAt hq (mul_ne_zero hr hx)).differentiableAt.comp x
    (differentiableAt_id.const_mul r)
  have hnum := ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul r)).mul hDs
  have hrat := (hnum.div hD (jacobiPairProduct_ne_zero hq hp hm)).pow 2
  have hJ := jacobiPairProduct_logDeriv_differentiableAt hq hx hp hm
  have harg := (differentiableAt_id.const_mul (-2*(k : ℂ))).mul hJ
  have he := (Complex.differentiable_exp _).comp x harg
  unfold jacobiProductError
  exact (hrat.const_mul _).mul he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiProductError_differentiableAt
