import TwoAxisHelicoid.TraceDataJacobi

namespace TwoAxisHelicoid.TraceData
def jacobiDualNomeExpression : BallExpression := .neg (.exp (.neg (.div .pi (.input 0))))
def jacobiDualRExpression : BallExpression := .exp (.neg (.div (.mul .pi (.input 1)) (.input 0)))
def jacobiDualKappaExpression : BallExpression :=
  .div (.mul .pi (.sub (.rational 1) (.input 1))) (.input 0)
def jacobiDualBetaExpression : BallExpression := .exp (.neg jacobiDualKappaExpression)
def jacobiQXExpression : BallExpression :=
  .mul (.const ⟨0,-1⟩) (.exp (.div (.mul .pi (.sub (.input 2) (.rational 1))) (.input 0)))
def jacobiQInvXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.neg (.div (.mul .pi (.add (.input 2) (.rational 1))) (.input 0))))
def jacobiQRXExpression : BallExpression :=
  .mul (.const ⟨0,-1⟩) (.exp (.div (.mul .pi (.sub (.sub (.input 2) (.input 1)) (.rational 1))) (.input 0)))
def jacobiQInvRXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.sub (.sub (.input 1) (.input 2)) (.rational 1))) (.input 0)))
def jacobiPhysicalXExpression (right : Bool) : BallExpression :=
  if right then .mul (.const ⟨0,-1⟩) (.exp (.neg (.div (.mul .pi (.input 2)) (.input 0))))
  else .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.input 2)) (.input 0)))
def jacobiPhysicalRXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.sub (.input 2) (.input 1))) (.input 0)))

def jacobiNormalizationExpression : BallExpression :=
  .div (.pow (.input 1) 4)
    (.mul (.pow (.sub (.rational 1) (.input 0)) 2) (.pow (.mul (.input 2) (.input 3)) 2))

/-- Inputs: t, kappa, normalization, x (or 1/x), rx, four products, two Euler sums. -/
def jacobiKernelResultExpression (right : Bool) : BallExpression :=
  let u := BallExpression.inv (.sub (.rational 1) (.input 3))
  let v := if right then BallExpression.neg u else .mul (.input 3) u
  let b := if right then BallExpression.sub (.rational 1) (.mul (.rational 2) u)
    else .add (.rational (-1)) (.mul (.rational 2) u)
  let d := BallExpression.mul (.input 5) (.input 6)
  let ds := BallExpression.mul (.input 7) (.input 8)
  let j := BallExpression.sub (.input 9) (.input 10)
  .mul (.mul (.mul (.div (.pow .pi 2) (.pow (.input 0) 2)) (.input 2)) (.pow v 2))
    (.mul (.pow (.div (.mul (.sub (.rational 1) (.input 4)) ds) d) 2)
      (.exp (.mul (.input 1) (.sub b (.mul (.rational 2) j)))))

structure DyadicJacobiBaseParameters where
  height : DyadicBall
  abscissa : DyadicBall
  q : DyadicExpressionTrace
  r : DyadicExpressionTrace
  kappa : DyadicExpressionTrace
  beta : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiBaseParameters

def inputs (p : DyadicJacobiBaseParameters) : List DyadicBall := [p.height,p.abscissa,.zero]

def Valid (cfg : BallConfig) (p : DyadicJacobiBaseParameters) : Prop :=
  p.q.check cfg (dyadicInputList p.inputs) jacobiDualNomeExpression = true ∧
  p.r.check cfg (dyadicInputList p.inputs) jacobiDualRExpression = true ∧
  p.kappa.check cfg (dyadicInputList p.inputs) jacobiDualKappaExpression = true ∧
  p.beta.check cfg (dyadicInputList p.inputs) jacobiDualBetaExpression = true

instance (cfg : BallConfig) (p : DyadicJacobiBaseParameters) : Decidable (p.Valid cfg) := by
  unfold Valid
  infer_instance

end DyadicJacobiBaseParameters

structure DyadicJacobiParameters where
  base : DyadicJacobiBaseParameters
  qr : DyadicBall
  p0 : DyadicJacobiProductTrace
  pr : DyadicJacobiProductTrace
  pinvr : DyadicJacobiProductTrace
  normalization : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiParameters

def inputs (p : DyadicJacobiParameters) : List DyadicBall :=
  [p.base.r.output,p.p0.output,p.pr.output,p.pinvr.output]

def Valid (cfg : BallConfig) (err : Nat) (p : DyadicJacobiParameters) : Prop :=
  p.base.Valid cfg ∧ DyadicBall.ChecksMul cfg.prec p.qr p.base.q.output p.base.r.output ∧
  p.p0.Valid cfg.prec err p.base.q.output p.base.q.output ∧
  p.pr.Valid cfg.prec err p.base.q.output p.qr ∧
  p.pinvr.Valid cfg.prec err p.base.q.output p.base.beta.output.neg ∧
  p.normalization.check cfg (dyadicInputList p.inputs) jacobiNormalizationExpression = true

instance (cfg : BallConfig) (err : Nat) (p : DyadicJacobiParameters) : Decidable (p.Valid cfg err) := by
  unfold Valid
  infer_instance

end DyadicJacobiParameters

structure DyadicJacobiKernelTrace where
  qx : DyadicExpressionTrace
  qinvx : DyadicExpressionTrace
  qrx : DyadicExpressionTrace
  qinvrx : DyadicExpressionTrace
  x : DyadicExpressionTrace
  rx : DyadicExpressionTrace
  pA : DyadicJacobiProductTrace
  pB : DyadicJacobiProductTrace
  pC : DyadicJacobiProductTrace
  pD : DyadicJacobiProductTrace
  eA : DyadicJacobiEulerTrace
  eB : DyadicJacobiEulerTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiKernelTrace

def output (w : DyadicJacobiKernelTrace) : DyadicBall := w.result.output

def inputs (p : DyadicJacobiParameters) (w : DyadicJacobiKernelTrace) : List DyadicBall :=
  [p.base.height,p.base.kappa.output,p.normalization.output,w.x.output,w.rx.output,
    w.pA.output,w.pB.output,w.pC.output,w.pD.output,w.eA.output,w.eB.output]

def Valid (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) : Prop :=
  let env := dyadicInputList [p.base.height,p.base.abscissa,z]
  w.qx.check cfg env jacobiQXExpression = true ∧ w.qinvx.check cfg env jacobiQInvXExpression = true ∧
  w.qrx.check cfg env jacobiQRXExpression = true ∧ w.qinvrx.check cfg env jacobiQInvRXExpression = true ∧
  w.x.check cfg env (jacobiPhysicalXExpression right) = true ∧
  w.rx.check cfg env jacobiPhysicalRXExpression = true ∧
  w.pA.Valid cfg.prec productError p.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.q.output w.qinvx.output ∧
  w.result.check cfg (dyadicInputList (w.inputs p)) (jacobiKernelResultExpression right) = true

instance (cfg : BallConfig) (productError eulerError : Nat) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) :
    Decidable (w.Valid cfg productError eulerError right p z) := by
  unfold Valid
  infer_instance

end DyadicJacobiKernelTrace
end TwoAxisHelicoid.TraceData
