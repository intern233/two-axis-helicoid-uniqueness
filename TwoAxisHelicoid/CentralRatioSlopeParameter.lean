import TwoAxisHelicoid.SlopingFluxRootParameters
namespace TwoAxisHelicoid
set_option maxRecDepth 5000
def centralRatioSlopeExpression : BallExpression := .div (.mul (.rational 4) (.sub (.rational 1) (.input 1))) (.input 0)
def centralRatioSlopeTrace : DyadicExpressionTrace := (.binary ⟨528116093550026, 0, 995⟩
  (.binary ⟨457468786083188, 0, 591⟩
  (.atom ⟨1125899906842624, 0, 2⟩)
  (.binary ⟨114367196520797, 0, 147⟩
  (.atom ⟨281474976710656, 0, 2⟩)
  (.unary ⟨(-167107780189859), 0, 143⟩ (.atom ⟨167107780189859, 0, 143⟩))))
  (.unary ⟨324943405221717, 0, 191⟩ (.atom ⟨243821420103002, 0, 143⟩)))
theorem centralRatioSlopeTrace_valid : centralRatioSlopeTrace.Valid slopingFluxAnalyticSetup.config (threeDyadic TraceData.slopingFluxParams.height.interpret TraceData.slopingFluxParams.abscissa.interpret .zero) centralRatioSlopeExpression := by decide +kernel
end TwoAxisHelicoid
