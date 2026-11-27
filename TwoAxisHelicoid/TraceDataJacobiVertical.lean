import TwoAxisHelicoid.TraceDataJacobiKernel
namespace TwoAxisHelicoid.TraceData
def jacobiSmallNomeExpression (u : Rat) : BallExpression :=
  .exp (.neg (.div .pi (.mul (.rational 2) (.rational u))))

structure DyadicJacobiVerticalTrace where
  first : DyadicJacobiSecondTrace
  second : DyadicJacobiSecondTrace
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiVerticalTrace

def Valid (cfg : BallConfig) (err : Nat) (p : DyadicJacobiBaseParameters)
    (w : DyadicJacobiVerticalTrace) : Prop :=
  w.first.Valid cfg err p.q.output p.r.output ∧
  w.second.Valid cfg err p.q.output p.beta.output.neg ∧
  DyadicBall.ChecksAdd w.output w.first.output w.second.output

instance (cfg : BallConfig) (err : Nat) (p : DyadicJacobiBaseParameters)
    (w : DyadicJacobiVerticalTrace) : Decidable (w.Valid cfg err p) := by
  unfold Valid
  infer_instance

end DyadicJacobiVerticalTrace
end TwoAxisHelicoid.TraceData
