import TwoAxisHelicoid.TraceDataSlopingFluxParameters
import Init.Data.Vector.Basic

namespace TwoAxisHelicoid.TraceData

/-- The twelve rational nodes and weights used by the physical horizontal
means. The analytic bridge checks each entry against the moment-certified rule. -/
def spatialRuleNodes : Vector Rat 12 := #v[(1015/1024), (473/512), (203/256), (623/1024), (49/128), (67/512), (-67/512), (-49/128), (-623/1024), (-203/256), (-473/512), (-1015/1024)]
def spatialRuleWeights : Vector Rat 12 := #v[(92962589220984152436907085312/6191880578394888073236330105315), (520000515578271171924276092/10152119478967653672120999825), (329525838332573570122825358/4160943629000698922013738645), (34533794933167301912802503168/331768499300868245592320519175), (6816070731776354047229528363/56601838361766312985164205950), (3596522294262080859158590172/27652982499532548251323790175), (3596522294262080859158590172/27652982499532548251323790175), (6816070731776354047229528363/56601838361766312985164205950), (34533794933167301912802503168/331768499300868245592320519175), (329525838332573570122825358/4160943629000698922013738645), (520000515578271171924276092/10152119478967653672120999825), (92962589220984152436907085312/6191880578394888073236330105315)]

def spatialAllNodes : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n+1, f => f 0 && spatialAllNodes n (fun i => f i.succ)

def spatialRatSum : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n+1, f => f 0 + spatialRatSum n (fun i => f i.succ)

def spatialTraceInflate (b : ComplexBall) (r : Rat) : ComplexBall := ⟨b.center,b.radius+r⟩

def spatialMeanSum (w : HorizontalRangeCell 12) : ComplexBall :=
  let b := fun i => ((w.nodes i).output.toBall slopingFluxDataSetup.config.prec)
  ⟨⟨spatialRatSum 12 (fun i => (b i).center.re),spatialRatSum 12 (fun i => (b i).center.im)⟩,
    spatialRatSum 12 (fun i => (b i).radius)⟩

/-- A closed rational check of the surrounding disk, all quadrature nodes
and the final error-inflated enclosure for one segment. -/
def HorizontalRangeCell.spatialMeanValid (w : HorizontalRangeCell 12) (c : QComplex) (h R : Rat) : Prop :=
  let s := slopingFluxDataSetup
  let p := slopingFluxParams
  let prec := s.config.prec
  let disk := w.diskFunction.output.toBall prec
  let err := 2*((disk.center.absUpper+disk.radius)*(h/R)^12/(1-h/R))
  0≤h ∧ h<R ∧ (w.center.toBall prec).coarsens ⟨c,0⟩ ∧
    (w.disk.toBall prec).coarsens (spatialTraceInflate (w.center.toBall prec) R) ∧
    w.diskFunction.horizontalCheck s p.q.output p.abscissa p.coefficient.output w.disk=true ∧
    spatialAllNodes 12 (fun i => (w.nodes i).check s p w.center h (spatialRuleNodes.get i) (spatialRuleWeights.get i))=true ∧
    (w.output.toBall prec).coarsens (spatialTraceInflate (spatialMeanSum w) err)

instance HorizontalRangeCell.instDecidableSpatialMeanValid (w : HorizontalRangeCell 12) (c : QComplex) (h R : Rat) : Decidable (w.spatialMeanValid c h R) := by
  unfold HorizontalRangeCell.spatialMeanValid
  infer_instance

structure SpatialMeanCell where
  positive : HorizontalRangeCell 12
  negative : HorizontalRangeCell 12

def SpatialMeanCell.Valid (w : SpatialMeanCell) (first : Bool) (y l r R lo hi : Rat) : Prop :=
  let prec := slopingFluxDataSetup.config.prec
  let x := (l+r)/2
  let h := (r-l)/2
  let p := w.positive.output.toBall prec
  let n := w.negative.output.toBall prec
  let c := if first then -(p.center.re+n.center.re)/2 else (n.center.im-p.center.im)/2
  let b := (p.radius+n.radius)/2
  l<r ∧ w.positive.spatialMeanValid ⟨x,y⟩ h R ∧ w.negative.spatialMeanValid ⟨-x,-y⟩ h R ∧
    lo≤(r-l)*(c-b) ∧ (r-l)*(c+b)≤hi

instance SpatialMeanCell.instDecidableValid (w : SpatialMeanCell) (first : Bool) (y l r R lo hi : Rat) : Decidable (w.Valid first y l r R lo hi) := by
  unfold SpatialMeanCell.Valid
  infer_instance

inductive CheckedSpatialMean (first : Bool) (y : Rat) : Rat → Rat → Rat → Rat → Prop
  | cell {l r R a b} (w : SpatialMeanCell) (valid : w.Valid first y l r R a b) : CheckedSpatialMean first y l r a b
  | join {l m r a b c d} : CheckedSpatialMean first y l m a b → CheckedSpatialMean first y m r c d →
      CheckedSpatialMean first y l r (a+c) (b+d)

theorem CheckedSpatialMean.cast_bounds {f e l r a b c d} (h : CheckedSpatialMean f e l r a b)
    (left : a=c) (right : b=d) : CheckedSpatialMean f e l r c d := left ▸ right ▸ h

end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.CheckedSpatialMean.cast_bounds
