import TwoAxisHelicoid.TraceDataJacobiChord
import TwoAxisHelicoid.TraceDataJacobiCell

namespace TwoAxisHelicoid.TraceData

structure JacobiChordRangeNode where
  point : DyadicBall
  function : DyadicJacobiChordTrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace JacobiChordRangeNode

def output (w : JacobiChordRangeNode) : DyadicBall := w.weighted.output

def Valid (cfg : BallConfig) (productError eulerError : Nat)
    (p : DyadicJacobiChordParameters) (center : DyadicBall) (h node weight : Rat)
    (w : JacobiChordRangeNode) : Prop :=
  (w.point.toBall cfg.prec).coarsens
    (ComplexBall.add (center.toBall cfg.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid cfg productError eulerError p w.point ∧
  w.weighted.check cfg (dyadicInputList [w.function.output])
    (.mul (.rational weight) (.input 0)) = true

instance (cfg : BallConfig) (productError eulerError : Nat)
    (p : DyadicJacobiChordParameters) (center : DyadicBall) (h node weight : Rat)
    (w : JacobiChordRangeNode) : Decidable (w.Valid cfg productError eulerError p center h node weight) := by
  unfold Valid
  infer_instance

end JacobiChordRangeNode

structure JacobiChordRangeCell (K : Nat) where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicJacobiChordTrace
  nodes : Fin K → JacobiChordRangeNode
  output : DyadicBall


end TwoAxisHelicoid.TraceData
