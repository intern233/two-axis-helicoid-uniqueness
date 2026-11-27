import TwoAxisHelicoid.CentralRatioJetData

namespace TwoAxisHelicoid

structure ShiftedThetaValueTrace where
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  value : DyadicThetaTrace

def ShiftedThetaValueTrace.Checks (w : ShiftedThetaValueTrace) (z : DyadicBall) (plus : Bool) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  w.argument.Valid S.config (threeDyadic z p.abscissa.interpret .zero) (centralShiftExpression plus) ∧
    w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
    w.value.Valid S.config 0 S.terms S.error p.q.output.interpret w.seed

instance shiftedThetaValueTraceDecidable (w : ShiftedThetaValueTrace) (z : DyadicBall) (p : Bool) :
    Decidable (w.Checks z p) := by unfold ShiftedThetaValueTrace.Checks; infer_instance

structure HighLevelRatioTrace where
  box : DyadicBall
  exponential : DyadicExpressionTrace
  minus : ShiftedThetaValueTrace
  plus : ShiftedThetaValueTrace
  value : DyadicExpressionTrace

def HighLevelRatioTrace.Checks (w : HighLevelRatioTrace) (v : Bool) (x l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let b := w.value.output.toBall S.config.prec
  (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v x l r) ∧
    w.exponential.Valid S.config (threeDyadic centralRatioSlopeTrace.output w.box .zero) centralRatioExpExpression ∧
    w.minus.Checks w.box false ∧ w.plus.Checks w.box true ∧
    w.value.Valid S.config (threeDyadic w.exponential.output w.minus.value.output w.plus.value.output)
      (.div (.mul (.input 0) (.input 1)) (.input 2)) ∧ b.center.re+b.radius < -(1/1024:ℚ)

instance highLevelRatioTraceDecidable (w : HighLevelRatioTrace) (v : Bool) (x l r : ℚ) :
    Decidable (w.Checks v x l r) := by unfold HighLevelRatioTrace.Checks; infer_instance

def highLevelHeightCheck (w : SpatialHeightValueTrace) (v : Bool) (x l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.height.output.toBall S.config.prec
  w.Valid S p.height.interpret p.q.output.interpret ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v x l r) ∧
    -1<b.center.re-b.radius ∧ b.center.re+b.radius<1

instance highLevelHeightCheckDecidable (w : SpatialHeightValueTrace) (v : Bool) (x l r : ℚ) :
    Decidable (highLevelHeightCheck w v x l r) := by unfold highLevelHeightCheck; infer_instance

inductive CheckedHighLevelEdge : Bool → Bool → ℚ → ℚ → ℚ → Prop
  | ratio {v x l r} (w : HighLevelRatioTrace) (ok : w.Checks v x l r) : CheckedHighLevelEdge false v x l r
  | height {v x l r} (w : SpatialHeightValueTrace) (ok : highLevelHeightCheck w v x l r) : CheckedHighLevelEdge true v x l r
  | join {h v x l m r} : CheckedHighLevelEdge h v x l m → CheckedHighLevelEdge h v x m r → CheckedHighLevelEdge h v x l r

end TwoAxisHelicoid
