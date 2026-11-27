import TwoAxisHelicoid.ThetaValueEnclosure

namespace TwoAxisHelicoid

def obliqueRatioCheck (w : HighLevelRatioTrace) (positive vertical : Bool) (fixed l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let b := w.value.output.toBall S.config.prec
  w.Valid ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall vertical fixed l r) ∧
    4*b.center.re+(if positive then -7 else 7)*b.center.im+11*b.radius ≤ -(1/1024:ℚ)

instance (w : HighLevelRatioTrace) (p v : Bool) (e l r : ℚ) : Decidable (obliqueRatioCheck w p v e l r) := by
  unfold obliqueRatioCheck
  infer_instance

def obliqueHeightCheck (w : SpatialHeightValueTrace) (positive vertical : Bool) (fixed l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.height.output.toBall S.config.prec
  w.Valid S p.height.interpret p.q.output.interpret ∧
    (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall vertical fixed l r) ∧
    (if positive then b.center.re else -b.center.re)+b.radius < 1/4

instance (w : SpatialHeightValueTrace) (p v : Bool) (e l r : ℚ) : Decidable (obliqueHeightCheck w p v e l r) := by
  unfold obliqueHeightCheck
  infer_instance

inductive CheckedObliqueEdge : Bool → Bool → Bool → ℚ → ℚ → ℚ → Prop
  | ratio {p v e l r} (w : HighLevelRatioTrace) (ok : obliqueRatioCheck w p v e l r) :
      CheckedObliqueEdge p false v e l r
  | height {p v e l r} (w : SpatialHeightValueTrace) (ok : obliqueHeightCheck w p v e l r) :
      CheckedObliqueEdge p true v e l r
  | join {p h v e l m r} : CheckedObliqueEdge p h v e l m → CheckedObliqueEdge p h v e m r →
      CheckedObliqueEdge p h v e l r

end TwoAxisHelicoid
