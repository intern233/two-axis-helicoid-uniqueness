import TwoAxisHelicoid.TraceData
import TwoAxisHelicoid.DyadicBooleanCheck

namespace TwoAxisHelicoid.TraceData
namespace QComplex
def interpret (w : QComplex) : TwoAxisHelicoid.QComplex := ⟨w.re, w.im⟩
end QComplex

namespace BallConfig
def interpret (w : BallConfig) : TwoAxisHelicoid.BallConfig := ⟨w.prec, w.terms, w.squarings⟩
end BallConfig

namespace ComplexBall
def interpret (w : ComplexBall) : TwoAxisHelicoid.ComplexBall := ⟨w.center.interpret, w.radius⟩
end ComplexBall

namespace DyadicBall
def interpret (w : DyadicBall) : TwoAxisHelicoid.DyadicBall := ⟨w.re, w.im, w.radius⟩
end DyadicBall

namespace BallExpression
def interpret : BallExpression → TwoAxisHelicoid.BallExpression
  | .const c => .const c.interpret
  | .input i => .input i
  | .pi => .pi
  | .add a b => .add a.interpret b.interpret
  | .neg a => .neg a.interpret
  | .mul a b => .mul a.interpret b.interpret
  | .inv a => .inv a.interpret
  | .exp a => .exp a.interpret
@[simp] theorem interpret_rational (q : ℚ) : (rational q).interpret = TwoAxisHelicoid.BallExpression.rational q := rfl
@[simp] theorem interpret_sub (a b : BallExpression) : (sub a b).interpret = TwoAxisHelicoid.BallExpression.sub a.interpret b.interpret := rfl
@[simp] theorem interpret_div (a b : BallExpression) : (div a b).interpret = TwoAxisHelicoid.BallExpression.div a.interpret b.interpret := rfl
@[simp] theorem interpret_pow (a : BallExpression) (n : ℕ) : (pow a n).interpret = TwoAxisHelicoid.BallExpression.pow a.interpret n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow, interpret, TwoAxisHelicoid.BallExpression.pow, ih]
end BallExpression

namespace DyadicTaylorTrace
def interpret : DyadicTaylorTrace → TwoAxisHelicoid.DyadicTaylorTrace
  | .zero => .zero
  | .step p s m t => .step p.interpret s.interpret m.interpret t.interpret
@[simp] theorem interpret_length (w : DyadicTaylorTrace) : w.interpret.length = w.length := by
  induction w <;> simp_all only [interpret, length, TwoAxisHelicoid.DyadicTaylorTrace.length]
@[simp] theorem interpret_sum (w : DyadicTaylorTrace) : w.interpret.sum = w.sum.interpret := by cases w <;> rfl
@[simp] theorem interpret_term (prec : ℕ) (w : DyadicTaylorTrace) : w.interpret.term prec = (w.term prec).interpret := by cases w <;> rfl
end DyadicTaylorTrace

namespace DyadicSquareTrace
def interpret : DyadicSquareTrace → TwoAxisHelicoid.DyadicSquareTrace
  | .zero => .zero
  | .step p b => .step p.interpret b.interpret
@[simp] theorem interpret_length (w : DyadicSquareTrace) : w.interpret.length = w.length := by
  induction w <;> simp_all only [interpret, length, TwoAxisHelicoid.DyadicSquareTrace.length]
@[simp] theorem interpret_output (b : DyadicBall) (w : DyadicSquareTrace) : w.interpret.output b.interpret = (w.output b).interpret := by cases w <;> rfl
end DyadicSquareTrace

namespace DyadicExpTrace
def interpret (w : DyadicExpTrace) : TwoAxisHelicoid.DyadicExpTrace :=
  ⟨w.scaled.interpret,w.taylor.interpret,w.enclosure.interpret,w.squares.interpret⟩
@[simp] theorem interpret_output (w : DyadicExpTrace) : w.interpret.output = w.output.interpret := by
  exact DyadicSquareTrace.interpret_output _ _
end DyadicExpTrace

namespace DyadicExpressionTrace
def interpret : DyadicExpressionTrace → TwoAxisHelicoid.DyadicExpressionTrace
  | .atom b => .atom b.interpret
  | .unary b p => .unary b.interpret p.interpret
  | .binary b p q => .binary b.interpret p.interpret q.interpret
  | .exponential p w => .exponential p.interpret w.interpret
@[simp] theorem interpret_output (w : DyadicExpressionTrace) : w.interpret.output = w.output.interpret := by
  cases w <;> simp only [interpret, output, TwoAxisHelicoid.DyadicExpressionTrace.output, DyadicExpTrace.interpret_output]
end DyadicExpressionTrace

namespace DyadicThetaState
def interpret (w : DyadicThetaState) : TwoAxisHelicoid.DyadicThetaState :=
  ⟨w.sum.interpret,w.coefficient.interpret,w.step.interpret,w.positive.interpret,w.negative.interpret⟩
end DyadicThetaState

namespace DyadicThetaLoop
def interpret : DyadicThetaLoop → TwoAxisHelicoid.DyadicThetaLoop
  | .zero => .zero
  | .step p t s => .step p.interpret t.interpret s.interpret
@[simp] theorem interpret_length (w : DyadicThetaLoop) : w.interpret.length = w.length := by
  induction w <;> simp_all only [interpret, length, TwoAxisHelicoid.DyadicThetaLoop.length]
@[simp] theorem interpret_state (prec : ℕ) (q p m : DyadicBall) (w : DyadicThetaLoop) :
    w.interpret.state prec q.interpret p.interpret m.interpret = (w.state prec q p m).interpret := by
  cases w <;> rfl
end DyadicThetaLoop

namespace DyadicThetaSeed
def interpret (w : DyadicThetaSeed) : TwoAxisHelicoid.DyadicThetaSeed := ⟨w.positive.interpret, w.negative.interpret, w.positiveSquare.interpret, w.negativeSquare.interpret⟩
end DyadicThetaSeed

namespace DyadicThetaTrace
def interpret (w : DyadicThetaTrace) : TwoAxisHelicoid.DyadicThetaTrace := ⟨w.loop.interpret, w.output.interpret⟩
end DyadicThetaTrace

namespace DyadicThetaATrace
def interpret (w : DyadicThetaATrace) : TwoAxisHelicoid.DyadicThetaATrace := ⟨w.argument.interpret, w.shiftedArgument.interpret, w.seed.interpret, w.shiftedSeed.interpret, w.theta0.interpret, w.theta1.interpret, w.thetaShifted.interpret, w.result.interpret⟩
@[simp] theorem interpret_output (w : DyadicThetaATrace) : w.interpret.output = w.output.interpret := DyadicExpressionTrace.interpret_output _
end DyadicThetaATrace

namespace DyadicCoefficientTrace
def interpret (w : DyadicCoefficientTrace) : TwoAxisHelicoid.DyadicCoefficientTrace := ⟨w.argument.interpret, w.seedZero.interpret, w.seedA.interpret, w.thetaZero.interpret, w.thetaA.interpret, w.result.interpret⟩
@[simp] theorem interpret_output (w : DyadicCoefficientTrace) : w.interpret.output = w.output.interpret := DyadicExpressionTrace.interpret_output _
end DyadicCoefficientTrace

namespace RangeDyadicParameters
def interpret (w : RangeDyadicParameters) : TwoAxisHelicoid.RangeDyadicParameters := ⟨w.height.interpret, w.abscissa.interpret, w.q.interpret, w.coefficient.interpret⟩
end RangeDyadicParameters

namespace RangeDerivativeParameters
def interpret (w : RangeDerivativeParameters) : TwoAxisHelicoid.RangeDerivativeParameters := ⟨w.base.interpret, w.thetaA1.interpret, w.thetaA2.interpret, w.thetaA3.interpret, w.thetaA4.interpret, w.thetaZero3.interpret, w.ratioA.interpret, w.ratioA2.interpret, w.ratioZero.interpret, w.gt.interpret⟩
end RangeDerivativeParameters

namespace RangeDerivativeTrace
def interpret (w : RangeDerivativeTrace) : TwoAxisHelicoid.RangeDerivativeTrace := ⟨w.base.interpret, w.thetaZ2.interpret, w.thetaZ3.interpret, w.thetaM1.interpret, w.thetaM2.interpret, w.resultA.interpret, w.resultT.interpret⟩
end RangeDerivativeTrace

namespace RangeDerivativeNode
def interpret (w : RangeDerivativeNode) : TwoAxisHelicoid.RangeDerivativeNode := ⟨w.point.interpret, w.function.interpret, w.weightedA.interpret, w.weightedT.interpret⟩
end RangeDerivativeNode

namespace RangeDerivativeCell
def interpret (w : RangeDerivativeCell) : TwoAxisHelicoid.RangeDerivativeCell :=
  ⟨w.center.interpret,w.disk.interpret,w.diskFunction.interpret,
    fun i => (w.nodes i).interpret,w.outputA.interpret,w.outputT.interpret⟩
end RangeDerivativeCell

def setupOf (s : TwoAxisHelicoid.RangeCertificateSetup) : RangeCertificateSetup :=
  ⟨⟨s.config.prec,s.config.terms,s.config.squarings⟩,s.terms,s.error⟩

end TwoAxisHelicoid.TraceData
