import TwoAxisHelicoid.TraceDataJacobiCell
namespace TwoAxisHelicoid.TraceData
def jacobiFastX (right : Bool) : BallExpression :=
  if right then .inv (.input 3) else .input 3

def jacobiFastInvX (right : Bool) : BallExpression :=
  if right then .input 3 else .inv (.input 3)

def jacobiFastQXExpression (right : Bool) : BallExpression :=
  .mul (.input 0) (jacobiFastX right)

def jacobiFastQInvXExpression (right : Bool) : BallExpression :=
  .mul (.input 0) (jacobiFastInvX right)

def jacobiFastQRXExpression (right : Bool) : BallExpression :=
  .mul (.mul (.input 0) (.input 1)) (jacobiFastX right)

def jacobiFastQInvRXExpression (right : Bool) : BallExpression :=
  .mul (.neg (.input 2)) (jacobiFastInvX right)

def jacobiFastRXExpression (right : Bool) : BallExpression :=
  .mul (.input 1) (jacobiFastX right)

namespace DyadicJacobiKernelTrace
def FastValid (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) : Prop :=
  let env := dyadicInputList [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
  w.qx.check cfg env (jacobiFastQXExpression right) = true ∧ w.qinvx.check cfg env (jacobiFastQInvXExpression right) = true ∧
  w.qrx.check cfg env (jacobiFastQRXExpression right) = true ∧ w.qinvrx.check cfg env (jacobiFastQInvRXExpression right) = true ∧
  w.x.check cfg (dyadicInputList [p.base.height,p.base.abscissa,z]) (jacobiPhysicalXExpression right) = true ∧
  w.rx.check cfg env (jacobiFastRXExpression right) = true ∧
  w.pA.Valid cfg.prec productError p.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.q.output w.qinvx.output ∧
  w.result.check cfg (dyadicInputList (w.inputs p)) (jacobiKernelResultExpression right) = true

instance (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) :
    Decidable (w.FastValid cfg productError eulerError right p z) := by
  unfold FastValid
  infer_instance

end DyadicJacobiKernelTrace
namespace JacobiRangeNode
def FastValid (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : Rat)
    (w : JacobiRangeNode) : Prop :=
  (w.point.toBall cfg.prec).coarsens
    (ComplexBall.add (center.toBall cfg.prec) (ComplexBall.rational (h*node))) ∧
  w.function.FastValid cfg productError eulerError right p w.point ∧
  w.weighted.check cfg (dyadicInputList [w.function.output])
    (.mul (.rational weight) (.input 0)) = true

instance (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : Rat)
    (w : JacobiRangeNode) : Decidable (w.FastValid cfg productError eulerError right p center h node weight) := by
  unfold FastValid
  infer_instance

end JacobiRangeNode
end TwoAxisHelicoid.TraceData
