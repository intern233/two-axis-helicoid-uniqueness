import TwoAxisHelicoid.TraceData

namespace TwoAxisHelicoid.TraceData
namespace DyadicBall

def normUpper (prec : Nat) (b : DyadicBall) : Rat :=
  (b.toBall prec).center.absUpper+(b.toBall prec).radius

end DyadicBall

structure DyadicJacobiProductState where
  product : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiProductLoop where
  | zero
  | step (previous : DyadicJacobiProductLoop) (factor : DyadicBall)
      (next : DyadicJacobiProductState)
  deriving Repr

namespace DyadicJacobiProductLoop

def length : DyadicJacobiProductLoop → Nat
  | .zero => 0
  | .step p _ _ => p.length+1

def state (prec : Nat) (bz : DyadicBall) : DyadicJacobiProductLoop → DyadicJacobiProductState
  | .zero => ⟨.one prec, bz⟩
  | .step _ _ s => s

def Valid (prec : Nat) (bq bz : DyadicBall) : DyadicJacobiProductLoop → Prop
  | .zero => True
  | .step p factor next =>
    let s := p.state prec bz
    p.Valid prec bq bz ∧
    DyadicBall.ChecksAdd factor (.one prec) s.term.neg ∧
    DyadicBall.ChecksMul prec next.product s.product factor ∧
    DyadicBall.ChecksMul prec next.term s.term bq

instance instDecidableValid (prec : Nat) (bq bz : DyadicBall)
    (w : DyadicJacobiProductLoop) : Decidable (w.Valid prec bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p factor next => by
    haveI := instDecidableValid prec bq bz p
    unfold Valid
    infer_instance

end DyadicJacobiProductLoop

structure DyadicJacobiProductTrace where
  loop : DyadicJacobiProductLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiProductTrace

def Valid (prec err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiProductTrace) : Prop :=
  let s := w.loop.state prec bz
  let σ := bq.normUpper prec
  let τ := s.term.normUpper prec
  let M := s.product.normUpper prec
  w.loop.Valid prec bq bz ∧ σ < 1 ∧ τ/(1-σ) ≤ 1 ∧
    2*M*τ/(1-σ) ≤ (err : Rat)/DyadicBall.denominator prec ∧
    w.output.Coarsens (s.product.inflate err)

instance (prec err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiProductTrace) :
    Decidable (w.Valid prec err bq bz) := by unfold Valid; infer_instance

end DyadicJacobiProductTrace

def jacobiEulerTermExpression : BallExpression :=
  .div (.neg (.input 0)) (.sub (.rational 1) (.input 0))

structure DyadicJacobiEulerState where
  sum : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiEulerLoop where
  | zero
  | step (previous : DyadicJacobiEulerLoop) (summand : DyadicExpressionTrace)
      (next : DyadicJacobiEulerState)
  deriving Repr

namespace DyadicJacobiEulerLoop

def length : DyadicJacobiEulerLoop → Nat
  | .zero => 0
  | .step p _ _ => p.length+1

def state (bz : DyadicBall) : DyadicJacobiEulerLoop → DyadicJacobiEulerState
  | .zero => ⟨.zero, bz⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (bq bz : DyadicBall) : DyadicJacobiEulerLoop → Prop
  | .zero => True
  | .step p summand next =>
    let s := p.state bz
    p.Valid cfg bq bz ∧
    summand.check cfg (threeDyadic s.term .zero .zero) jacobiEulerTermExpression = true ∧
    DyadicBall.ChecksAdd next.sum s.sum summand.output ∧
    DyadicBall.ChecksMul cfg.prec next.term s.term bq

instance instDecidableValid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiEulerLoop) : Decidable (w.Valid cfg bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p summand next => by
    haveI := instDecidableValid cfg bq bz p
    unfold Valid
    infer_instance

end DyadicJacobiEulerLoop

structure DyadicJacobiEulerTrace where
  loop : DyadicJacobiEulerLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiEulerTrace

def Valid (cfg : BallConfig) (err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiEulerTrace) : Prop :=
  let s := w.loop.state bz
  let σ := bq.normUpper cfg.prec
  let τ := s.term.normUpper cfg.prec
  w.loop.Valid cfg bq bz ∧ σ < 1 ∧ bz.normUpper cfg.prec < 1 ∧ τ < 1 ∧
    τ/((1-σ)*(1-τ)) ≤ (err : Rat)/DyadicBall.denominator cfg.prec ∧
    w.output.Coarsens (s.sum.inflate err)

instance (cfg : BallConfig) (err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiEulerTrace) :
    Decidable (w.Valid cfg err bq bz) := by unfold Valid; infer_instance

end DyadicJacobiEulerTrace

def jacobiSecondTermExpression : BallExpression :=
  .div (.input 0) (.pow (.sub (.rational 1) (.input 0)) 2)

structure DyadicJacobiSecondState where
  sum : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiSecondLoop where
  | zero
  | step (previous : DyadicJacobiSecondLoop) (summand : DyadicExpressionTrace)
      (next : DyadicJacobiSecondState)
  deriving Repr

namespace DyadicJacobiSecondLoop

def length : DyadicJacobiSecondLoop → Nat
  | .zero => 0
  | .step p _ _ => p.length+1

def state (bz : DyadicBall) : DyadicJacobiSecondLoop → DyadicJacobiSecondState
  | .zero => ⟨.zero, bz⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (bq bz : DyadicBall) : DyadicJacobiSecondLoop → Prop
  | .zero => True
  | .step p summand next =>
    let s := p.state bz
    p.Valid cfg bq bz ∧
    summand.check cfg (threeDyadic s.term .zero .zero) jacobiSecondTermExpression = true ∧
    DyadicBall.ChecksAdd next.sum s.sum summand.output ∧
    DyadicBall.ChecksMul cfg.prec next.term s.term bq

instance instDecidableValid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiSecondLoop) : Decidable (w.Valid cfg bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p summand next => by
    haveI := instDecidableValid cfg bq bz p
    unfold Valid
    infer_instance

end DyadicJacobiSecondLoop

structure DyadicJacobiSecondTrace where
  loop : DyadicJacobiSecondLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiSecondTrace

def Valid (cfg : BallConfig) (err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiSecondTrace) : Prop :=
  let s := w.loop.state bz
  let σ := bq.normUpper cfg.prec
  let τ := s.term.normUpper cfg.prec
  w.loop.Valid cfg bq bz ∧ σ < 1 ∧ bz.normUpper cfg.prec < 1 ∧ τ < 1 ∧
    τ/((1-σ)*(1-τ)^2) ≤ (err : Rat)/DyadicBall.denominator cfg.prec ∧
    w.output.Coarsens (s.sum.inflate err)

instance (cfg : BallConfig) (err : Nat) (bq bz : DyadicBall) (w : DyadicJacobiSecondTrace) :
    Decidable (w.Valid cfg err bq bz) := by unfold Valid; infer_instance

end DyadicJacobiSecondTrace

end TwoAxisHelicoid.TraceData
