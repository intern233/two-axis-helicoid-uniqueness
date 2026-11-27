import TwoAxisHelicoid.TraceDataSlopingFlux

namespace TwoAxisHelicoid.TraceData

/-- Product of the velocity disk with the difference of the two theta
kernel disks already checked on an original sloping-generator cell. -/
def SlopingFluxCell.differenceProduct (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) : ComplexBall :=
  let a := v.toBall prec
  let b := (w.plusTheta.output.toBall prec).sub (w.minusTheta.output.toBall prec)
  ⟨a.center.mul b.center, a.center.absUpper*b.radius+b.center.absUpper*a.radius+a.radius*b.radius⟩

def SlopingFluxCell.transverseBounds (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall)
    (lo hi : Rat) : Prop :=
  let B := w.differenceProduct prec v
  2*lo ≤ -(B.center.im+B.radius) ∧ -(B.center.im-B.radius) ≤ 2*hi

instance (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) (lo hi : Rat) :
    Decidable (w.transverseBounds prec v lo hi) := by unfold SlopingFluxCell.transverseBounds; infer_instance

/-- The last two indices enclose the total change of the transverse
spatial coordinate on the interval between the first two indices. -/
inductive CheckedSlopingDisplacement (S : HorizontalRangeSetup) (p : RangeDyadicParameters) (v : DyadicBall) :
    Rat → Rat → Rat → Rat → Prop
  | cell (w : SlopingFluxCell) (l r lo hi : Rat)
      (domain : 0 ≤ l ∧ l < r ∧ r ≤ 1) (data : w.check S p v l r = true)
      (bounds : w.transverseBounds S.config.prec v lo hi) :
      CheckedSlopingDisplacement S p v l r (lo*(r-l)) (hi*(r-l))
  | join {l m r a b c d : Rat} :
      CheckedSlopingDisplacement S p v l m a b → CheckedSlopingDisplacement S p v m r c d →
      CheckedSlopingDisplacement S p v l r (a+c) (b+d)
  | weaken {l r a b c d : Rat} :
      CheckedSlopingDisplacement S p v l r a b → c ≤ a → b ≤ d →
      CheckedSlopingDisplacement S p v l r c d

end TwoAxisHelicoid.TraceData
