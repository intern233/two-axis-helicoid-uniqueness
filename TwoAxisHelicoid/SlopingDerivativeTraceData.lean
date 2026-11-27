import TwoAxisHelicoid.SlopingFluxRootParameters
import TwoAxisHelicoid.DyadicInputList

namespace TwoAxisHelicoid

def slopingKernelSlopeExpression : BallExpression :=
  let r := BallExpression.div (.input 3) (.input 2)
  let m := BallExpression.div (.input 6) (.input 5)
  let q := BallExpression.div (.input 4) (.input 2)
  .mul (.mul (.neg (.pow (.input 7) 2)) (.input 1))
    (.add (.mul .pi (.sub m r)) (.mul (.mul (.mul (.sub (.input 0) (.rational 1)) (.pow .pi 2))
      (.rational (1/2))) (.sub q (.pow r 2))))

structure SlopingDerivativeTrace where
  parameter : DyadicBall
  point : DyadicExpressionTrace
  base : DyadicThetaATrace
  second : DyadicThetaTrace
  shiftedFirst : DyadicThetaTrace
  result : DyadicExpressionTrace

namespace SlopingDerivativeTrace

def inputs (w : SlopingDerivativeTrace) : List DyadicBall :=
  [TraceData.slopingFluxParams.abscissa.interpret,w.base.output,w.base.theta0.output,
    w.base.theta1.output,w.second.output,w.base.thetaShifted.output,w.shiftedFirst.output,
    TraceData.slopingFluxWeight.output.interpret]

def Valid (w : SlopingDerivativeTrace) (l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let v := TraceData.slopingFluxWeight.output.interpret
  (w.parameter.toBall S.config.prec).coarsens (ComplexBall.realInterval l r) ∧
    w.point.Valid S.config (threeDyadic v w.parameter .zero) (TraceData.slopingFluxPointExpression true).interpret ∧
    w.base.Valid S.config S.terms S.error p.q.output.interpret p.abscissa.interpret p.coefficient.output.interpret w.point.output ∧
    w.second.Valid S.config 2 S.terms S.error p.q.output.interpret w.base.seed ∧
    w.shiftedFirst.Valid S.config 1 S.terms S.error p.q.output.interpret w.base.shiftedSeed ∧
    0<w.base.thetaShifted.output.lower ∧
    w.result.Valid S.config (dyadicInputList w.inputs) slopingKernelSlopeExpression ∧
    (w.result.output.toBall S.config.prec).radius<(w.result.output.toBall S.config.prec).center.im

instance (w : SlopingDerivativeTrace) (l r : ℚ) : Decidable (w.Valid l r) := by
  unfold Valid
  infer_instance

end SlopingDerivativeTrace

inductive CheckedSlopingPositiveAcceleration : ℚ → ℚ → Prop
  | cell (w : SlopingDerivativeTrace) (l r : ℚ) (checked : w.Valid l r) : CheckedSlopingPositiveAcceleration l r
  | join {l m r : ℚ} : CheckedSlopingPositiveAcceleration l m → CheckedSlopingPositiveAcceleration m r →
      CheckedSlopingPositiveAcceleration l r

end TwoAxisHelicoid
