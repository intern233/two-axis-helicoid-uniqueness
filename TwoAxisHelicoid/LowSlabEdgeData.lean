import TwoAxisHelicoid.ThetaValueEnclosure

namespace TwoAxisHelicoid

/-- Simultaneous upper bounds for the two extreme projections of a
theta value. Convexity gives every intermediate direction as well. -/
def lowSlabSectorCheck (w : HighLevelRatioTrace) (v : Bool) (e l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let b := w.value.output.toBall S.config.prec
  w.Valid ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v e l r) ∧
    4*b.center.re+|b.center.im|+5*b.radius≤ -(1/1024:ℚ)

instance (w : HighLevelRatioTrace) (v : Bool) (e l r : ℚ) : Decidable (lowSlabSectorCheck w v e l r) := by
  unfold lowSlabSectorCheck
  infer_instance

def lowSlabHeightBound (w : SpatialHeightValueTrace) (above v : Bool) (m e l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let b := w.height.output.toBall S.config.prec
  w.Valid S p.height.interpret p.q.output.interpret ∧
    (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall v e l r) ∧
    if above then m<b.center.re-b.radius else b.center.re+b.radius<m

instance (w : SpatialHeightValueTrace) (a v : Bool) (m e l r : ℚ) :
    Decidable (lowSlabHeightBound w a v m e l r) := by unfold lowSlabHeightBound; infer_instance

inductive LowSlabQuantity | sector | height (above : Bool) (value : ℚ)

inductive CheckedLowSlabEdge : LowSlabQuantity → Bool → ℚ → ℚ → ℚ → Prop
  | sector {v e l r} (w : HighLevelRatioTrace) (ok : lowSlabSectorCheck w v e l r) :
      CheckedLowSlabEdge .sector v e l r
  | height {a v m e l r} (w : SpatialHeightValueTrace) (ok : lowSlabHeightBound w a v m e l r) :
      CheckedLowSlabEdge (.height a m) v e l r
  | join {k v e l m r} : CheckedLowSlabEdge k v e l m → CheckedLowSlabEdge k v e m r →
      CheckedLowSlabEdge k v e l r

end TwoAxisHelicoid
