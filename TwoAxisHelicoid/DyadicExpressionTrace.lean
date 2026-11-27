import TwoAxisHelicoid.DyadicBallBasic
import TwoAxisHelicoid.BallExpression

namespace TwoAxisHelicoid

inductive DyadicExpressionTrace where
  | atom (out : DyadicBall)
  | unary (out : DyadicBall) (child : DyadicExpressionTrace)
  | binary (out : DyadicBall) (left right : DyadicExpressionTrace)
  | exponential (child : DyadicExpressionTrace) (witness : DyadicExpTrace)
  deriving Repr

namespace DyadicExpressionTrace

def output : DyadicExpressionTrace → DyadicBall
  | .atom out => out
  | .unary out _ => out
  | .binary out _ _ => out
  | .exponential _ w => w.output

def Valid (cfg : BallConfig) (env : ℕ → DyadicBall) : BallExpression → DyadicExpressionTrace → Prop
  | .const c, .atom out => (out.toBall cfg.prec).coarsens (ComplexBall.point c)
  | .input n, .atom out => out.Coarsens (env n)
  | .pi, .atom out => (out.toBall cfg.prec).coarsens ComplexBall.piBall
  | .add a b, .binary out wa wb =>
      Valid cfg env a wa ∧ Valid cfg env b wb ∧ DyadicBall.ChecksAdd out wa.output wb.output
  | .neg a, .unary out wa => Valid cfg env a wa ∧ out.Coarsens wa.output.neg
  | .mul a b, .binary out wa wb =>
      Valid cfg env a wa ∧ Valid cfg env b wb ∧ DyadicBall.ChecksMul cfg.prec out wa.output wb.output
  | .inv a, .unary out wa => Valid cfg env a wa ∧ DyadicBall.ChecksInv cfg.prec out wa.output
  | .exp a, .exponential wa w => Valid cfg env a wa ∧ w.Valid cfg wa.output
  | _, _ => False

instance instDecidableValid (cfg : BallConfig) (env : ℕ → DyadicBall)
    (e : BallExpression) (w : DyadicExpressionTrace) : Decidable (Valid cfg env e w) :=
  match e, w with
  | .const _, .atom _ => by unfold Valid; infer_instance
  | .input _, .atom _ => by unfold Valid; infer_instance
  | .pi, .atom _ => by unfold Valid; infer_instance
  | .add a b, .binary _ wa wb => by
    haveI := instDecidableValid cfg env a wa
    haveI := instDecidableValid cfg env b wb
    unfold Valid
    infer_instance
  | .neg a, .unary _ wa => by
    haveI := instDecidableValid cfg env a wa
    unfold Valid
    infer_instance
  | .mul a b, .binary _ wa wb => by
    haveI := instDecidableValid cfg env a wa
    haveI := instDecidableValid cfg env b wb
    unfold Valid
    infer_instance
  | .inv a, .unary _ wa => by
    haveI := instDecidableValid cfg env a wa
    unfold Valid
    infer_instance
  | .exp a, .exponential wa _ => by
    haveI := instDecidableValid cfg env a wa
    unfold Valid
    infer_instance
  | .const _, .unary _ _ => isFalse id
  | .const _, .binary _ _ _ => isFalse id
  | .const _, .exponential _ _ => isFalse id
  | .input _, .unary _ _ => isFalse id
  | .input _, .binary _ _ _ => isFalse id
  | .input _, .exponential _ _ => isFalse id
  | .pi, .unary _ _ => isFalse id
  | .pi, .binary _ _ _ => isFalse id
  | .pi, .exponential _ _ => isFalse id
  | .add _ _, .atom _ => isFalse id
  | .add _ _, .unary _ _ => isFalse id
  | .add _ _, .exponential _ _ => isFalse id
  | .neg _, .atom _ => isFalse id
  | .neg _, .binary _ _ _ => isFalse id
  | .neg _, .exponential _ _ => isFalse id
  | .mul _ _, .atom _ => isFalse id
  | .mul _ _, .unary _ _ => isFalse id
  | .mul _ _, .exponential _ _ => isFalse id
  | .inv _, .atom _ => isFalse id
  | .inv _, .binary _ _ _ => isFalse id
  | .inv _, .exponential _ _ => isFalse id
  | .exp _, .atom _ => isFalse id
  | .exp _, .unary _ _ => isFalse id
  | .exp _, .binary _ _ _ => isFalse id

theorem sound (cfg : BallConfig) (env : ℕ → DyadicBall) (values : ℕ → ℂ)
    (hvalues : ∀ n, ((env n).toBall cfg.prec).Contains (values n))
    (e : BallExpression) (w : DyadicExpressionTrace) (hw : Valid cfg env e w) :
    (w.output.toBall cfg.prec).Contains (e.value values) := by
  induction e generalizing w with
  | const c =>
    cases w <;> simp only [Valid] at hw
    exact ComplexBall.coarsen_contains (ComplexBall.point_contains c) hw
  | input n =>
    cases w <;> simp only [Valid] at hw
    exact DyadicBall.coarsen_contains (hvalues n) hw
  | pi =>
    cases w <;> simp only [Valid] at hw
    exact ComplexBall.coarsen_contains ComplexBall.piBall_contains hw
  | add a b iha ihb =>
    cases w <;> simp only [Valid] at hw
    exact DyadicBall.add_contains (iha _ hw.1) (ihb _ hw.2.1) hw.2.2
  | neg a ih =>
    cases w <;> simp only [Valid] at hw
    exact DyadicBall.coarsen_contains (DyadicBall.neg_contains (ih _ hw.1)) hw.2
  | mul a b iha ihb =>
    cases w <;> simp only [Valid] at hw
    exact DyadicBall.mul_contains (iha _ hw.1) (ihb _ hw.2.1) hw.2.2
  | inv a ih =>
    cases w <;> simp only [Valid] at hw
    exact DyadicBall.inv_contains (ih _ hw.1) hw.2
  | exp a ih =>
    cases w <;> simp only [Valid] at hw
    exact DyadicExpTrace.sound cfg (ih _ hw.1) _ hw.2

end DyadicExpressionTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicExpressionTrace.sound
