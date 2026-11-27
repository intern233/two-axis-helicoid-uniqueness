import TwoAxisHelicoid.CentralBandEdgeData

namespace TwoAxisHelicoid

/-- The two theta kernels give both horizontal spatial coefficients
directly, including at the height saddles. -/
structure QuarterSpatialTrace where
  box : DyadicBall
  positive : DyadicThetaATrace
  negative : DyadicThetaATrace

def QuarterSpatialTrace.center (w : QuarterSpatialTrace) (first vertical : Bool) : ℚ :=
  let prec := slopingFluxAnalyticSetup.config.prec
  let p := (w.positive.output.toBall prec).center
  let m := (w.negative.output.toBall prec).center
  if first then (if vertical then p.im+m.im else -(p.re+m.re))/2
  else (if vertical then m.re-p.re else m.im-p.im)/2

def QuarterSpatialTrace.check (w : QuarterSpatialTrace) (first d v : Bool) (e l r lo hi : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let A := w.positive.Valid S.config S.terms S.error p.q.output.interpret p.abscissa.interpret p.coefficient.output.interpret w.box
  let B := w.negative.Valid S.config S.terms S.error p.q.output.interpret p.abscissa.interpret p.coefficient.output.interpret w.box.neg
  let rad := ((w.positive.output.toBall S.config.prec).radius+(w.negative.output.toBall S.config.prec).radius)/2
  A ∧ B ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v e l r) ∧
    lo≤w.center first d-rad ∧ w.center first d+rad≤hi

instance (w : QuarterSpatialTrace) (f d v : Bool) (e l r a b : ℚ) :
    Decidable (w.check f d v e l r a b) := by unfold QuarterSpatialTrace.check; infer_instance

/-- The first pair bounds the rate throughout the interval. The second
pair bounds its integral, so the same mesh can certify a gradient sign
and an anchored position. -/
inductive CheckedQuarterSpatialLine (first d v : Bool) (e : ℚ) :
    ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Prop
  | cell {l r lo hi} (w : QuarterSpatialTrace) (lr : l<r) (cert : w.check first d v e l r lo hi) :
      CheckedQuarterSpatialLine first d v e l r lo hi (lo*(r-l)) (hi*(r-l))
  | join {l m r a b c f u w x y} : CheckedQuarterSpatialLine first d v e l m a b u w →
      CheckedQuarterSpatialLine first d v e m r c f x y →
      CheckedQuarterSpatialLine first d v e l r (min a c) (max b f) (u+x) (w+y)

end TwoAxisHelicoid
