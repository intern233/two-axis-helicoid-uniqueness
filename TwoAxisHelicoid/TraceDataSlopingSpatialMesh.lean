import TwoAxisHelicoid.TraceDataSlopingDisplacement

namespace TwoAxisHelicoid.TraceData

/-- Enclosure of the derivative, the full increment, and every ordered
subinterval increment of a scalar function on one mesh interval. -/
structure SlopingScalarBounds where
  rateLo : Rat
  rateHi : Rat
  totalLo : Rat
  totalHi : Rat
  partLo : Rat
  partHi : Rat
  deriving DecidableEq

def SlopingScalarBounds.cell (l r lo hi : Rat) : SlopingScalarBounds :=
  ⟨lo,hi,lo*(r-l),hi*(r-l),min lo 0*(r-l),max hi 0*(r-l)⟩

def SlopingScalarBounds.join (a b : SlopingScalarBounds) : SlopingScalarBounds :=
  ⟨min a.rateLo b.rateLo,max a.rateHi b.rateHi,a.totalLo+b.totalLo,a.totalHi+b.totalHi,
    a.partLo+b.partLo,a.partHi+b.partHi⟩

def SlopingFluxCell.sumProduct (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) : ComplexBall :=
  let a := v.toBall prec
  let b := (w.plusTheta.output.toBall prec).add (w.minusTheta.output.toBall prec)
  ⟨a.center.mul b.center,a.center.absUpper*b.radius+b.center.absUpper*a.radius+a.radius*b.radius⟩

def SlopingFluxCell.longitudinalBounds (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) (lo hi : Rat) : Prop :=
  let B := w.sumProduct prec v
  2*lo ≤ -(B.center.re+B.radius) ∧ -(B.center.re-B.radius) ≤ 2*hi

instance (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) (lo hi : Rat) :
    Decidable (w.longitudinalBounds prec v lo hi) := by unfold SlopingFluxCell.longitudinalBounds; infer_instance

def SlopingFluxCell.scalarBounds (w : SlopingFluxCell) (first : Bool) (prec : Nat)
    (v : DyadicBall) (lo hi : Rat) : Prop :=
  if first then w.longitudinalBounds prec v lo hi else w.transverseBounds prec v lo hi

instance (w : SlopingFluxCell) (first : Bool) (prec : Nat) (v : DyadicBall) (lo hi : Rat) :
    Decidable (w.scalarBounds first prec v lo hi) := by unfold SlopingFluxCell.scalarBounds; split <;> infer_instance

inductive CheckedSlopingScalar (first : Bool) (S : HorizontalRangeSetup) (p : RangeDyadicParameters)
    (v : DyadicBall) : Rat → Rat → SlopingScalarBounds → Prop
  | cell (w : SlopingFluxCell) (l r lo hi : Rat) (domain : 0≤l ∧ l<r ∧ r≤1)
      (data : w.check S p v l r=true) (rate : w.scalarBounds first S.config.prec v lo hi) :
      CheckedSlopingScalar first S p v l r (.cell l r lo hi)
  | join {l m r : Rat} {a b : SlopingScalarBounds} : CheckedSlopingScalar first S p v l m a →
      CheckedSlopingScalar first S p v m r b → CheckedSlopingScalar first S p v l r (a.join b)
  | relabel {l r : Rat} {a b : SlopingScalarBounds} : CheckedSlopingScalar first S p v l r a → a=b →
      CheckedSlopingScalar first S p v l r b

end TwoAxisHelicoid.TraceData
