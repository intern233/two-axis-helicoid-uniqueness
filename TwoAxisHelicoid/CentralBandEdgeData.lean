import TwoAxisHelicoid.SpatialWeierstrassTrace
import TwoAxisHelicoid.SpatialHeightValueTrace
import TwoAxisHelicoid.SlopingFluxRootParameters

namespace TwoAxisHelicoid
open ComplexBall

structure CentralGaussFieldTrace where
  box : DyadicBall
  base : DyadicThetaATrace
  second : DyadicThetaTrace
  height : DyadicExpressionTrace
  result : DyadicExpressionTrace

def CentralGaussFieldTrace.Valid (w : CentralGaussFieldTrace) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  w.base.Valid S.config S.terms S.error p.q.output.interpret p.abscissa.interpret p.coefficient.output.interpret w.box ∧
    w.second.Valid S.config 2 S.terms S.error p.q.output.interpret w.base.seed ∧
    w.height.Valid S.config (fiveDyadic p.height.interpret w.base.theta0.output w.base.theta1.output w.second.output .zero) spatialHeightExpression ∧
    0<w.height.output.lower ∧
    w.result.Valid S.config (threeDyadic w.base.output w.height.output .zero) (.div (.input 0) (.input 1))

instance (w : CentralGaussFieldTrace) : Decidable w.Valid := by unfold CentralGaussFieldTrace.Valid; infer_instance

def centralBandEdgeBall (v : Bool) (c l r : ℚ) : ComplexBall :=
  ⟨if v then ⟨c,(l+r)/2⟩ else ⟨(l+r)/2,c⟩,(r-l)/2⟩

inductive CentralBandQuantity | heightNeg | heightPos | gauss

def centralBandHeightNegCheck (w : SpatialHeightValueTrace) (v : Bool) (c l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.height.output.toBall S.config.prec
  w.Valid S p.height.interpret p.q.output.interpret ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v c l r) ∧
    b.center.re+b.radius<0

def centralBandHeightPosCheck (w : SpatialHeightValueTrace) (v : Bool) (c l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.height.output.toBall S.config.prec
  w.Valid S p.height.interpret p.q.output.interpret ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v c l r) ∧
    0<b.center.re-b.radius

def centralBandGaussCheck (w : CentralGaussFieldTrace) (v : Bool) (c l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let b := w.result.output.toBall S.config.prec
  w.Valid ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v c l r) ∧
    b.center.re+b.radius≤ -(1/512) ∧ b.center.im+b.radius≤ -(1/512)

instance (w : SpatialHeightValueTrace) (v : Bool) (c l r : ℚ) : Decidable (centralBandHeightNegCheck w v c l r) := by
  unfold centralBandHeightNegCheck; infer_instance
instance (w : SpatialHeightValueTrace) (v : Bool) (c l r : ℚ) : Decidable (centralBandHeightPosCheck w v c l r) := by
  unfold centralBandHeightPosCheck; infer_instance
instance (w : CentralGaussFieldTrace) (v : Bool) (c l r : ℚ) : Decidable (centralBandGaussCheck w v c l r) := by
  unfold centralBandGaussCheck; infer_instance

inductive CheckedCentralBandEdge : CentralBandQuantity → Bool → ℚ → ℚ → ℚ → Prop
  | heightNeg (w : SpatialHeightValueTrace) {v c l r} (ok : centralBandHeightNegCheck w v c l r) : CheckedCentralBandEdge .heightNeg v c l r
  | heightPos (w : SpatialHeightValueTrace) {v c l r} (ok : centralBandHeightPosCheck w v c l r) : CheckedCentralBandEdge .heightPos v c l r
  | gauss (w : CentralGaussFieldTrace) {v c l r} (ok : centralBandGaussCheck w v c l r) : CheckedCentralBandEdge .gauss v c l r
  | join {k v c l m r} : CheckedCentralBandEdge k v c l m → CheckedCentralBandEdge k v c m r → CheckedCentralBandEdge k v c l r

end TwoAxisHelicoid
