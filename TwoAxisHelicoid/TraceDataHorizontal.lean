import TwoAxisHelicoid.TraceData

/- Finite horizontal-period witnesses, with no analytic imports. -/
namespace TwoAxisHelicoid.TraceData

structure HorizontalRangeSetup where
  config : BallConfig
  imaginary : Rat
  terms : Nat
  error : Nat

namespace DyadicBall

def ChecksImaginaryBound (prec : Nat) (bound : Rat) (b : DyadicBall) : Prop :=
  Rat.abs (b.toBall prec).center.im + (b.toBall prec).radius ≤ bound

instance (prec : Nat) (bound : Rat) (b : DyadicBall) :
    Decidable (b.ChecksImaginaryBound prec bound) := by
  unfold ChecksImaginaryBound
  infer_instance

end DyadicBall

namespace DyadicThetaATrace

def horizontalCheck (s : HorizontalRangeSetup) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Bool :=
  w.argument.check s.config (threeDyadic bz ba .zero) thetaArgumentExpression &&
  w.shiftedArgument.check s.config (threeDyadic bz ba .zero) thetaShiftedArgumentExpression &&
  decide (w.argument.output.ChecksImaginaryBound s.config.prec s.imaginary) &&
  decide (w.shiftedArgument.output.ChecksImaginaryBound s.config.prec s.imaginary) &&
  w.seed.check s.config w.argument.output && w.shiftedSeed.check s.config w.shiftedArgument.output &&
  w.theta0.check s.config 0 s.terms s.error bq w.seed &&
  w.theta1.check s.config 1 s.terms s.error bq w.seed &&
  w.thetaShifted.check s.config 0 s.terms s.error bq w.shiftedSeed &&
  decide (0 < w.theta0.output.lower) &&
  w.result.check s.config (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

end DyadicThetaATrace

structure HorizontalRangeNode where
  point : DyadicBall
  function : DyadicThetaATrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace HorizontalRangeNode

def output (w : HorizontalRangeNode) : DyadicBall := w.weighted.output

def check (s : HorizontalRangeSetup) (p : RangeDyadicParameters) (center : DyadicBall)
    (h node weight : Rat) (w : HorizontalRangeNode) : Bool :=
  decide ((w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node)))) &&
  w.function.horizontalCheck s p.q.output p.abscissa p.coefficient.output w.point &&
  w.weighted.check s.config (threeDyadic w.function.output .zero .zero)
    (.mul (.rational weight) (.input 0))

end HorizontalRangeNode

structure HorizontalRangeCell (K : Nat) where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicThetaATrace
  nodes : Fin K → HorizontalRangeNode
  output : DyadicBall

end TwoAxisHelicoid.TraceData
