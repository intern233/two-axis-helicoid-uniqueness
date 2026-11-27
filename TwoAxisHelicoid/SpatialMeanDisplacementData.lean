import TwoAxisHelicoid.SpatialRationalMeanCheck
import TwoAxisHelicoid.RationalQuadrature12
import TwoAxisHelicoid.TraceDataSlopingFluxParameters
import TwoAxisHelicoid.TraceDataHorizontalBridge
import TwoAxisHelicoid.SlopingFluxTail

namespace TwoAxisHelicoid

/-- Two certified theta means on oppositely centered segments, with
outward-rounded rational bounds for the physical displacement. -/
structure SpatialMeanDisplacementCell where
  positive : HorizontalRangeCell 12
  negative : HorizontalRangeCell 12

def spatialMeanCenter (first : Bool) (p n : QComplex) : ℚ :=
  if first then -(p.re+n.re)/2 else (n.im-p.im)/2

def SpatialMeanDisplacementCell.Valid (w : SpatialMeanDisplacementCell) (first : Bool) (y l r R lo hi : ℚ) : Prop :=
  let setup := slopingFluxAnalyticSetup
  let params := TraceData.slopingFluxParams.interpret
  let x := (l+r)/2
  let h := (r-l)/2
  let p := w.positive.output.toBall setup.config.prec
  let n := w.negative.output.toBall setup.config.prec
  let c := spatialMeanCenter first p.center n.center
  let b := (p.radius+n.radius)/2
  l<r ∧ w.positive.validAtRational setup rationalQuadrature12 12 params ⟨x,y⟩ h R ∧
    w.negative.validAtRational setup rationalQuadrature12 12 params ⟨-x,-y⟩ h R ∧
    lo≤(r-l)*(c-b) ∧ (r-l)*(c+b)≤hi

instance SpatialMeanDisplacementCell.instDecidableValid (w : SpatialMeanDisplacementCell) (f : Bool) (e l r R a b : ℚ) : Decidable (w.Valid f e l r R a b) := by
  unfold SpatialMeanDisplacementCell.Valid
  infer_instance

inductive CheckedHorizontalDisplacement (first : Bool) (y : ℚ) : ℚ → ℚ → ℚ → ℚ → Prop
  | cell {l r R a b} (w : SpatialMeanDisplacementCell) (ok : w.Valid first y l r R a b) :
      CheckedHorizontalDisplacement first y l r a b
  | join {l m r a b c d} : CheckedHorizontalDisplacement first y l m a b →
      CheckedHorizontalDisplacement first y m r c d → CheckedHorizontalDisplacement first y l r (a+c) (b+d)

theorem CheckedHorizontalDisplacement.cast_bounds {f y l r a b c d}
    (h : CheckedHorizontalDisplacement f y l r a b) (left : a=c) (right : b=d) :
    CheckedHorizontalDisplacement f y l r c d := left ▸ right ▸ h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedHorizontalDisplacement.cast_bounds
