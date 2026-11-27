import TwoAxisHelicoid.SlopingFluxBounds
import TwoAxisHelicoid.SlopingFluxTail
import TwoAxisHelicoid.TraceDataSlopingFluxParameters
import TwoAxisHelicoid.RootVerticalConstants

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem sloping_flux_parameter_data_valid : TraceData.slopingFluxParams.interpret.HorizontalValid
    slopingFluxAnalyticSetup rootTLower rootTUpper rootALower rootAUpper := by decide +kernel

/-- Genuine theta coefficient data, the affine velocity and the scale
of the original sloping cycle on the full certified parameter rectangle. -/
theorem sloping_flux_root_parameter_enclosures {t a : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper)
    (ha : a ∈ Icc (rootALower:ℝ) rootAUpper) :
    let S := slopingFluxAnalyticSetup
    let p := TraceData.slopingFluxParams
    (S.lower:ℝ) ≤ t ∧ (p.q.output.interpret.toBall S.config.prec).Contains (exp (-Real.pi*t)) ∧
    (p.abscissa.interpret.toBall S.config.prec).Contains (a:ℂ) ∧
    (p.coefficient.output.interpret.toBall S.config.prec).Contains (thetaACoefficient t a) ∧
    (TraceData.slopingFluxWeight.output.interpret.toBall S.config.prec).Contains ((1-I*t)/2) := by
  obtain ⟨ht',hq,ha',hc⟩ := TraceData.slopingFluxParams.interpret.horizontal_sound slopingFluxAnalyticSetup
    slopingFluxAnalyticSetup_valid sloping_flux_parameter_data_valid ht.1 ht.2 ha.1 ha.2
  have bt := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains ht.1 ht.2) sloping_flux_parameter_data_valid.2.1
  let zs := DyadicBall.zero_contains slopingFluxAnalyticSetup.config.prec
  have h := TraceData.checked_three_expression_contains TraceData.slopingFluxDataSetup.config
    (a := TraceData.slopingFluxParams.height) (b := .zero) (c := .zero) bt zs zs _ _ TraceData.slopingFluxWeight_checked
  have he : TraceData.slopingFluxWeightExpression.interpret.value (threeValues (t:ℂ) 0 0) = (1-I*t)/2 := by
    change (BallExpression.div (.sub (.rational 1) (.mul .imaginaryUnit (.input 0))) (.rational 2)).value _ = _
    simp [BallExpression.div,BallExpression.sub,BallExpression.value,threeValues,div_eq_mul_inv,sub_eq_add_neg]
  rw [he] at h
  exact ⟨ht',hq,ha',hc,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_flux_root_parameter_enclosures
