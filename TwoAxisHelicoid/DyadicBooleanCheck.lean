import TwoAxisHelicoid.RangeDerivativeCell
import TwoAxisHelicoid.DyadicPointCheck

namespace TwoAxisHelicoid

/- Boolean reflection changes only how a finite trace is checked.  Its conclusion
is exactly the existing mathematical validity predicate. -/
namespace DyadicTaylorTrace

def check (prec : ℕ) (b : DyadicBall) : DyadicTaylorTrace → Bool
  | .zero => true
  | .step p s m t => p.check prec b &&
      decide (DyadicBall.ChecksAdd s p.sum (p.term prec)) &&
      decide (DyadicBall.ChecksMul prec m (p.term prec) b) &&
      decide (DyadicBall.ChecksDivNat t m (p.length+1))

theorem check_eq_true (prec : ℕ) (b : DyadicBall) (w : DyadicTaylorTrace) :
    w.check prec b = true ↔ w.Valid prec b := by
  induction w with
  | zero => simp [check, Valid]
  | step p s m t ih => simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq, ih, and_assoc]

end DyadicTaylorTrace

namespace DyadicSquareTrace

def check (prec : ℕ) (b : DyadicBall) : DyadicSquareTrace → Bool
  | .zero => true
  | .step p out => p.check prec b &&
      decide (DyadicBall.ChecksMul prec out (p.output b) (p.output b))

theorem check_eq_true (prec : ℕ) (b : DyadicBall) (w : DyadicSquareTrace) :
    w.check prec b = true ↔ w.Valid prec b := by
  induction w with
  | zero => simp [check, Valid]
  | step p out ih => simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq, ih]

end DyadicSquareTrace

namespace DyadicExpTrace

def check (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) : Bool :=
  decide (DyadicBall.ChecksDivNat w.scaled b (2^cfg.squarings)) &&
  decide (w.taylor.length = cfg.terms) && w.taylor.check cfg.prec w.scaled &&
  decide (DyadicBall.ChecksExpGuard cfg.prec cfg.terms w.scaled) &&
  decide (DyadicBall.ChecksExpError cfg.prec cfg.terms w.enclosure w.taylor.sum w.scaled) &&
  decide (w.squares.length = cfg.squarings) && w.squares.check cfg.prec w.enclosure

theorem check_eq_true (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) :
    w.check cfg b = true ↔ w.Valid cfg b := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicTaylorTrace.check_eq_true, DyadicSquareTrace.check_eq_true, and_assoc]

end DyadicExpTrace

namespace DyadicExpressionTrace

def check (cfg : BallConfig) (env : ℕ → DyadicBall) : BallExpression → DyadicExpressionTrace → Bool
  | .const c, .atom out => decide (DyadicBall.ChecksPoint cfg.prec out c)
  | .input n, .atom out => decide (out.Coarsens (env n))
  | .pi, .atom out => decide ((out.toBall cfg.prec).coarsens ComplexBall.piBall)
  | .add a b, .binary out wa wb => check cfg env a wa && check cfg env b wb &&
      decide (DyadicBall.ChecksAdd out wa.output wb.output)
  | .neg a, .unary out wa => check cfg env a wa && decide (out.Coarsens wa.output.neg)
  | .mul a b, .binary out wa wb => check cfg env a wa && check cfg env b wb &&
      decide (DyadicBall.ChecksMul cfg.prec out wa.output wb.output)
  | .inv a, .unary out wa => check cfg env a wa && decide (DyadicBall.ChecksInv cfg.prec out wa.output)
  | .exp a, .exponential wa w => check cfg env a wa && w.check cfg wa.output
  | _, _ => false

theorem check_eq_true (cfg : BallConfig) (env : ℕ → DyadicBall)
    (e : BallExpression) (w : DyadicExpressionTrace) :
    check cfg env e w = true ↔ Valid cfg env e w := by
  induction e generalizing w <;> cases w <;>
    simp_all only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
      DyadicExpTrace.check_eq_true, DyadicBall.checksPoint_iff, Bool.false_eq_true, and_assoc]

end DyadicExpressionTrace

namespace DyadicThetaLoop

def check (cfg : BallConfig) (j : ℕ) (bq bp bm bp2 bm2 : DyadicBall) : DyadicThetaLoop → Bool
  | .zero => true
  | .step p term next =>
    let s := p.state cfg.prec bq bp bm
    p.check cfg j bq bp bm bp2 bm2 &&
    term.check cfg (threeDyadic s.coefficient s.positive s.negative)
      (thetaSeedTermExpression j p.length) &&
    decide (DyadicBall.ChecksAdd next.sum s.sum term.output) &&
    decide (DyadicBall.ChecksMul cfg.prec next.coefficient s.coefficient s.step) &&
    decide (DyadicBall.ChecksMul cfg.prec next.step s.step bq) &&
    decide (DyadicBall.ChecksMul cfg.prec next.positive s.positive bp2) &&
    decide (DyadicBall.ChecksMul cfg.prec next.negative s.negative bm2)

theorem check_eq_true (cfg : BallConfig) (j : ℕ) (bq bp bm bp2 bm2 : DyadicBall)
    (w : DyadicThetaLoop) :
    w.check cfg j bq bp bm bp2 bm2 = true ↔ w.Valid cfg j bq bp bm bp2 bm2 := by
  induction w with
  | zero => simp [check, Valid]
  | step p term next ih =>
    simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
      DyadicExpressionTrace.check_eq_true, ih, and_assoc]

end DyadicThetaLoop

namespace DyadicThetaSeed

def check (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) : Bool :=
  w.positive.check cfg (threeDyadic bv .zero .zero) thetaPositiveSeedExpression &&
  w.negative.check cfg (threeDyadic bv .zero .zero) thetaNegativeSeedExpression &&
  decide (DyadicBall.ChecksMul cfg.prec w.positiveSquare w.positive.output w.positive.output) &&
  decide (DyadicBall.ChecksMul cfg.prec w.negativeSquare w.negative.output w.negative.output)

theorem check_eq_true (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) :
    w.check cfg bv = true ↔ w.Valid cfg bv := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicExpressionTrace.check_eq_true, and_assoc]

end DyadicThetaSeed

namespace DyadicThetaTrace

def check (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall) (seed : DyadicThetaSeed)
    (w : DyadicThetaTrace) : Bool :=
  decide (w.loop.length = N) &&
  w.loop.check cfg j bq seed.positive.output seed.negative.output
    seed.positiveSquare seed.negativeSquare &&
  decide (w.output.Coarsens ((w.loop.state cfg.prec bq seed.positive.output seed.negative.output).sum.inflate err))

theorem check_eq_true (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall)
    (seed : DyadicThetaSeed) (w : DyadicThetaTrace) :
    w.check cfg j N err bq seed = true ↔ w.Valid cfg j N err bq seed := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicThetaLoop.check_eq_true, and_assoc]

end DyadicThetaTrace

namespace DyadicThetaATrace

def check (cfg : BallConfig) (N err : ℕ) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Bool :=
  w.argument.check cfg (threeDyadic bz ba .zero) thetaArgumentExpression &&
  w.shiftedArgument.check cfg (threeDyadic bz ba .zero) thetaShiftedArgumentExpression &&
  decide (w.argument.output.ChecksImOne cfg.prec) &&
  decide (w.shiftedArgument.output.ChecksImOne cfg.prec) &&
  w.seed.check cfg w.argument.output && w.shiftedSeed.check cfg w.shiftedArgument.output &&
  w.theta0.check cfg 0 N err bq w.seed && w.theta1.check cfg 1 N err bq w.seed &&
  w.thetaShifted.check cfg 0 N err bq w.shiftedSeed && decide (0 < w.theta0.output.lower) &&
  w.result.check cfg (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

theorem check_eq_true (cfg : BallConfig) (N err : ℕ) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) :
    w.check cfg N err bq ba bc bz = true ↔ w.Valid cfg N err bq ba bc bz := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicExpressionTrace.check_eq_true, DyadicThetaSeed.check_eq_true,
    DyadicThetaTrace.check_eq_true, and_assoc]

end DyadicThetaATrace

namespace RangeDerivativeTrace

def check (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (z : DyadicBall)
    (w : RangeDerivativeTrace) : Bool :=
  w.base.check s.config s.terms s.error p.base.q.output p.base.abscissa p.base.coefficient.output z &&
  w.thetaZ2.check s.config 2 s.terms s.error p.base.q.output w.base.seed &&
  w.thetaZ3.check s.config 3 s.terms s.error p.base.q.output w.base.seed &&
  w.thetaM1.check s.config 1 s.terms s.error p.base.q.output w.base.shiftedSeed &&
  w.thetaM2.check s.config 2 s.terms s.error p.base.q.output w.base.shiftedSeed &&
  decide (0 < w.base.thetaShifted.output.lower) &&
  w.resultA.check s.config (dyadicInputList (w.inputs p)) derivativeAaExpression &&
  w.resultT.check s.config (dyadicInputList (w.inputs p)) derivativeAtExpression

theorem check_eq_true (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (z : DyadicBall)
    (w : RangeDerivativeTrace) : w.check s p z = true ↔ w.Valid s p z := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicThetaATrace.check_eq_true, DyadicThetaTrace.check_eq_true,
    DyadicExpressionTrace.check_eq_true, and_assoc]

end RangeDerivativeTrace

namespace RangeDerivativeNode

def check (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : RangeDerivativeNode) : Bool :=
  decide ((w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node)))) &&
  w.function.check s p w.point &&
  w.weightedA.check s.config (threeDyadic w.function.resultA.output .zero .zero)
    (.mul (.rational weight) (.input 0)) &&
  w.weightedT.check s.config (threeDyadic w.function.resultT.output .zero .zero)
    (.mul (.rational weight) (.input 0))

theorem check_eq_true (s : RangeCertificateSetup) (p : RangeDerivativeParameters)
    (center : DyadicBall) (h node weight : ℚ) (w : RangeDerivativeNode) :
    w.check s p center h node weight = true ↔ w.Valid s p center h node weight := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    RangeDerivativeTrace.check_eq_true, DyadicExpressionTrace.check_eq_true, and_assoc]

end RangeDerivativeNode
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeNode.check_eq_true
