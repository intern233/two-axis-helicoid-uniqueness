import TwoAxisHelicoid.TraceDataHorizontal

namespace TwoAxisHelicoid.TraceData
open BallExpression

def slopingFluxWeightExpression : BallExpression := .div (.sub (rational 1) (.mul imaginaryUnit (.input 0))) (rational 2)
def slopingFluxPointExpression : Bool → BallExpression
  | true => .add (.neg (rational 1)) (.mul (.input 0) (.input 1))
  | false => .sub (.neg (rational 1)) (.mul (.input 0) (.input 1))
def slopingFluxPairExpression : BallExpression := .mul (.input 0) (.add (.input 1) (.input 2))

/-- Dyadic enclosures for the reflected pair of points on the original
sloping cycle, their theta kernels and the complex velocity-weighted sum. -/
structure SlopingFluxCell where
  parameter : DyadicBall
  plusPoint : DyadicExpressionTrace
  minusPoint : DyadicExpressionTrace
  plusTheta : DyadicThetaATrace
  minusTheta : DyadicThetaATrace
  pair : DyadicExpressionTrace

def SlopingFluxCell.check (w : SlopingFluxCell) (S : HorizontalRangeSetup) (p : RangeDyadicParameters)
    (v : DyadicBall) (l r : Rat) : Bool :=
  decide ((w.parameter.toBall S.config.prec).coarsens (ComplexBall.realInterval l r)) &&
  w.plusPoint.check S.config (threeDyadic v w.parameter .zero) (slopingFluxPointExpression true) &&
  w.minusPoint.check S.config (threeDyadic v w.parameter .zero) (slopingFluxPointExpression false) &&
  w.plusTheta.horizontalCheck S p.q.output p.abscissa p.coefficient.output w.plusPoint.output &&
  w.minusTheta.horizontalCheck S p.q.output p.abscissa p.coefficient.output w.minusPoint.output &&
  w.pair.check S.config (threeDyadic v w.plusTheta.output w.minusTheta.output) slopingFluxPairExpression &&
  decide ((w.pair.output.toBall S.config.prec).center.im+(w.pair.output.toBall S.config.prec).radius ≤ -(1/32 : Rat))

/-- Finite concatenation of checked cells with literally shared rational endpoints. -/
inductive CheckedSlopingFluxCover (S : HorizontalRangeSetup) (p : RangeDyadicParameters) (v : DyadicBall) : Rat → Rat → Prop
  | cell (w : SlopingFluxCell) (l r : Rat) (checked : w.check S p v l r = true) : CheckedSlopingFluxCover S p v l r
  | join {l m r : Rat} : CheckedSlopingFluxCover S p v l m → CheckedSlopingFluxCover S p v m r → CheckedSlopingFluxCover S p v l r

end TwoAxisHelicoid.TraceData
