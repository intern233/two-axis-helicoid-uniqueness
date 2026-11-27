import TwoAxisHelicoid.RectangleEdgeShapeData
import TwoAxisHelicoid.CentralArcFourthTail

namespace TwoAxisHelicoid

inductive CentralHeightSweep where
  | leftEarly | leftLate | saddleThird | saddleSlope
  deriving DecidableEq

def CentralHeightSweep.leftSide : CentralHeightSweep → Bool
  | .leftEarly | .leftLate => true
  | _ => false

def centralHeightSweepDisk (kind : CentralHeightSweep) (l r : ℚ) : ComplexBall :=
  let lo := if kind.leftSide then (1/2:ℚ) else rootALower
  let hi := if kind.leftSide then (1/2:ℚ) else rootAUpper
  ⟨⟨(lo+hi)/2,(l+r)/2⟩,(r-l+hi-lo)/2⟩

structure CentralArcSlopeTrace where
  box : DyadicBall
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  j0 : DyadicThetaTrace
  j1 : DyadicThetaTrace
  j2 : DyadicThetaTrace
  value : DyadicExpressionTrace

def CentralArcSlopeTrace.Checks (w : CentralArcSlopeTrace) (kind : CentralHeightSweep) (l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.value.output.toBall S.config.prec
  kind≠.saddleThird ∧
  (w.box.toBall S.config.prec).coarsens (centralHeightSweepDisk kind l r) ∧
  w.argument.Valid S.config (threeDyadic w.box .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
  w.j0.Valid S.config 0 S.terms S.error p.q.output.interpret w.seed ∧
  w.j1.Valid S.config 1 S.terms S.error p.q.output.interpret w.seed ∧
  w.j2.Valid S.config 2 S.terms S.error p.q.output.interpret w.seed ∧
  w.value.Valid S.config (fiveDyadic p.height.interpret w.j0.output w.j1.output w.j2.output .zero)
    (rectangleShapeExpression false) ∧ b.radius < (if kind=.leftEarly then -b.center.re else b.center.re)

instance centralArcSlopeChecksDecidable (w : CentralArcSlopeTrace) (k : CentralHeightSweep) (l r : ℚ) : Decidable (w.Checks k l r) := by
  unfold CentralArcSlopeTrace.Checks
  infer_instance

def centralFourthExpression : BallExpression :=
  let u := BallExpression.div (.input 1) (.input 0)
  let v := BallExpression.div (.input 2) (.input 0)
  let w := BallExpression.div (.input 3) (.input 0)
  let b := BallExpression.div (.input 4) (.input 0)
  .mul (.mul (.pow .pi 4) (.rational (1/16)))
    (.sub (.add (.add (.sub (.mul (.rational 3) (.pow v 2)) (.mul (.mul (.rational 12) (.pow u 2)) v))
      (.mul (.rational 6) (.pow u 4))) (.mul (.mul (.rational 4) u) w)) b)

structure CentralArcFourthTrace where
  box : DyadicBall
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  j0 : DyadicThetaTrace
  j1 : DyadicThetaTrace
  j2 : DyadicThetaTrace
  j3 : DyadicThetaTrace
  j4 : DyadicThetaTrace
  value : DyadicExpressionTrace

def CentralArcFourthTrace.Checks (w : CentralArcFourthTrace) (l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let q := TraceData.slopingFluxParams.q.output.interpret
  let b := w.value.output.toBall S.config.prec
  (w.box.toBall S.config.prec).coarsens (centralHeightSweepDisk .saddleThird l r) ∧
  w.argument.Valid S.config (threeDyadic w.box .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
  w.j0.Valid S.config 0 S.terms S.error q w.seed ∧
  w.j1.Valid S.config 1 S.terms S.error q w.seed ∧
  w.j2.Valid S.config 2 S.terms S.error q w.seed ∧
  w.j3.Valid S.config 3 S.terms S.error q w.seed ∧
  w.j4.Valid S.config 4 S.terms 268435456 q w.seed ∧
  w.value.Valid S.config (fiveDyadic w.j0.output w.j1.output w.j2.output w.j3.output w.j4.output)
    centralFourthExpression ∧ b.radius < b.center.re

instance centralArcFourthChecksDecidable (w : CentralArcFourthTrace) (l r : ℚ) : Decidable (w.Checks l r) := by
  unfold CentralArcFourthTrace.Checks
  infer_instance

inductive CheckedCentralHeightSweep : CentralHeightSweep → ℚ → ℚ → Prop
  | slope (w : CentralArcSlopeTrace) {k l r} (check : w.Checks k l r) : CheckedCentralHeightSweep k l r
  | third (w : CentralArcFourthTrace) {l r} (check : w.Checks l r) : CheckedCentralHeightSweep .saddleThird l r
  | join {k l m r} : CheckedCentralHeightSweep k l m → CheckedCentralHeightSweep k m r → CheckedCentralHeightSweep k l r

end TwoAxisHelicoid
