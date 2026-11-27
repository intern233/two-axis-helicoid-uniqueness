import TwoAxisHelicoid.CentralBandEdgeData
import TwoAxisHelicoid.RectangleEdgeThirdTail

namespace TwoAxisHelicoid

def rectangleShapeExpression (left : Bool) : BallExpression :=
  let u := BallExpression.div (.input 2) (.input 1)
  let v := BallExpression.div (.input 3) (.input 1)
  let w := BallExpression.div (.input 4) (.input 1)
  if left then .mul (.mul (.pow .pi 3) (.rational (1/8)))
    (.sub (.sub (.mul (.mul (.rational 3) u) v) (.mul (.rational 2) (.pow u 3))) w)
  else .sub (.div .pi (.input 0)) (.mul (.mul (.pow .pi 2) (.rational (1/4))) (.sub (.pow u 2) v))

structure RectangleEdgeJetTrace where
  box : DyadicBall
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  j0 : DyadicThetaTrace
  j1 : DyadicThetaTrace
  j2 : DyadicThetaTrace
  j3 : DyadicThetaTrace
  value : DyadicExpressionTrace

def rectangleShapeCheck (left : Bool) (l r : ℚ) (w : RectangleEdgeJetTrace) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let out := w.value.output.toBall S.config.prec
  (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall true (if left then 1/2 else 5/8) l r) ∧
  w.argument.Valid S.config (threeDyadic w.box .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
  w.j0.Valid S.config 0 S.terms S.error p.q.output.interpret w.seed ∧
  w.j1.Valid S.config 1 S.terms S.error p.q.output.interpret w.seed ∧
  w.j2.Valid S.config 2 S.terms S.error p.q.output.interpret w.seed ∧
  w.j3.Valid S.config 3 S.terms S.error p.q.output.interpret w.seed ∧
  w.value.Valid S.config (fiveDyadic p.height.interpret w.j0.output w.j1.output w.j2.output w.j3.output)
    (rectangleShapeExpression left) ∧ out.radius < (if left then out.center.im else out.center.re)

instance (b : Bool) (l r : ℚ) (w : RectangleEdgeJetTrace) : Decidable (rectangleShapeCheck b l r w) := by
  unfold rectangleShapeCheck
  infer_instance

inductive CheckedRectangleShape : Bool → ℚ → ℚ → Prop
  | leaf (w : RectangleEdgeJetTrace) {b l r} (ok : rectangleShapeCheck b l r w) : CheckedRectangleShape b l r
  | join {b l m r} : CheckedRectangleShape b l m → CheckedRectangleShape b m r → CheckedRectangleShape b l r

end TwoAxisHelicoid
