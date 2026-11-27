import TwoAxisHelicoid.TraceDataJacobiKernel

namespace TwoAxisHelicoid.TraceData

def jacobiChordNomeExpression : BallExpression :=
  .exp (.neg (.div .pi (.mul (.rational 2) (.input 0))))
def jacobiChordHExpression : BallExpression :=
  .div (.mul (.rational 2) (.input 0)) (.add (.rational 1) (.pow (.input 0) 2))
def jacobiChordKExpression : BallExpression :=
  .div (.sub (.rational 1) (.pow (.input 0) 2)) (.add (.rational 1) (.pow (.input 0) 2))
def jacobiChordUExpression : BallExpression :=
  .add (.input 0) (.mul (.mul (.const ⟨0,1⟩) (.input 1)) (.input 2))
def jacobiChordXExpression : BallExpression :=
  .div (.add (.input 0) (.const ⟨0,1⟩)) (.sub (.input 0) (.const ⟨0,1⟩))
def jacobiChordInvXExpression : BallExpression :=
  .div (.sub (.input 0) (.const ⟨0,1⟩)) (.add (.input 0) (.const ⟨0,1⟩))
def jacobiChordQXExpression : BallExpression := .mul (.input 0) (.input 3)
def jacobiChordQInvXExpression : BallExpression := .mul (.input 0) (.input 4)
def jacobiChordQRXExpression : BallExpression := .mul (.mul (.input 0) (.input 1)) (.input 3)
def jacobiChordQInvRXExpression : BallExpression := .mul (.neg (.input 2)) (.input 4)
def jacobiChordRXExpression : BallExpression := .mul (.input 1) (.input 3)

/-- Inputs: t, kappa, normalization, u, x, rx, four products, two Euler sums, chord k. -/
def jacobiChordResultExpression : BallExpression :=
  let d := BallExpression.mul (.input 6) (.input 7)
  let ds := BallExpression.mul (.input 8) (.input 9)
  let j := BallExpression.sub (.input 10) (.input 11)
  .mul (.mul (.mul (.mul (.div (.neg .pi) (.mul (.rational 2) (.input 0))) (.input 2)) (.input 4))
    (.pow (.div (.mul (.sub (.rational 1) (.input 5)) ds) d) 2))
    (.mul (.exp (.mul (.input 1) (.sub (.mul (.const ⟨0,1⟩) (.input 3)) (.mul (.rational 2) j))))
      (.input 12))


def jacobiChordMinusIExpression : BallExpression := .sub (.input 0) (.const ⟨0,1⟩)
def jacobiChordPlusIExpression : BallExpression := .add (.input 0) (.const ⟨0,1⟩)

structure DyadicJacobiChordParameters where
  base : DyadicJacobiParameters
  nomeHalf : DyadicExpressionTrace
  chordH : DyadicExpressionTrace
  chordK : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiChordParameters

def Valid (cfg : BallConfig) (err : Nat) (p : DyadicJacobiChordParameters) : Prop :=
  p.base.Valid cfg err ∧
  p.nomeHalf.check cfg (dyadicInputList [p.base.base.height]) jacobiChordNomeExpression = true ∧
  p.chordH.check cfg (dyadicInputList [p.nomeHalf.output]) jacobiChordHExpression = true ∧
  p.chordK.check cfg (dyadicInputList [p.nomeHalf.output]) jacobiChordKExpression = true

instance (cfg : BallConfig) (err : Nat) (p : DyadicJacobiChordParameters) : Decidable (p.Valid cfg err) := by
  unfold Valid
  infer_instance

end DyadicJacobiChordParameters

structure DyadicJacobiChordTrace where
  u : DyadicExpressionTrace
  uMinusI : DyadicExpressionTrace
  uPlusI : DyadicExpressionTrace
  x : DyadicExpressionTrace
  invx : DyadicExpressionTrace
  qx : DyadicExpressionTrace
  qinvx : DyadicExpressionTrace
  qrx : DyadicExpressionTrace
  qinvrx : DyadicExpressionTrace
  rx : DyadicExpressionTrace
  pA : DyadicJacobiProductTrace
  pB : DyadicJacobiProductTrace
  pC : DyadicJacobiProductTrace
  pD : DyadicJacobiProductTrace
  eA : DyadicJacobiEulerTrace
  eB : DyadicJacobiEulerTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiChordTrace

def output (w : DyadicJacobiChordTrace) : DyadicBall := w.result.output

def seedInputs (p : DyadicJacobiChordParameters) (w : DyadicJacobiChordTrace) : List DyadicBall :=
  [p.base.base.q.output,p.base.base.r.output,p.base.base.beta.output,w.x.output,w.invx.output]

def inputs (p : DyadicJacobiChordParameters) (w : DyadicJacobiChordTrace) : List DyadicBall :=
  [p.base.base.height,p.base.base.kappa.output,p.base.normalization.output,w.u.output,w.x.output,w.rx.output,
    w.pA.output,w.pB.output,w.pC.output,w.pD.output,w.eA.output,w.eB.output,p.chordK.output]

def Valid (cfg : BallConfig) (productError eulerError : Nat)
    (p : DyadicJacobiChordParameters) (z : DyadicBall) (w : DyadicJacobiChordTrace) : Prop :=
  let uenv := dyadicInputList [w.u.output]
  let env := dyadicInputList (w.seedInputs p)
  w.u.check cfg (dyadicInputList [p.chordH.output,p.chordK.output,z]) jacobiChordUExpression = true ∧
  w.uMinusI.check cfg uenv jacobiChordMinusIExpression = true ∧ 0 < w.uMinusI.output.lower ∧
  w.uPlusI.check cfg uenv jacobiChordPlusIExpression = true ∧ 0 < w.uPlusI.output.lower ∧
  w.x.check cfg uenv jacobiChordXExpression = true ∧
  w.invx.check cfg uenv jacobiChordInvXExpression = true ∧
  w.qx.check cfg env jacobiChordQXExpression = true ∧
  w.qinvx.check cfg env jacobiChordQInvXExpression = true ∧
  w.qrx.check cfg env jacobiChordQRXExpression = true ∧
  w.qinvrx.check cfg env jacobiChordQInvRXExpression = true ∧
  w.rx.check cfg env jacobiChordRXExpression = true ∧
  w.pA.Valid cfg.prec productError p.base.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.base.q.output w.qinvx.output ∧
  w.result.check cfg (dyadicInputList (w.inputs p)) jacobiChordResultExpression = true

instance (cfg : BallConfig) (productError eulerError : Nat)
    (p : DyadicJacobiChordParameters) (z : DyadicBall) (w : DyadicJacobiChordTrace) :
    Decidable (w.Valid cfg productError eulerError p z) := by
  unfold Valid
  infer_instance

end DyadicJacobiChordTrace

end TwoAxisHelicoid.TraceData
