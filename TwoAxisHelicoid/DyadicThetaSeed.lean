import TwoAxisHelicoid.DyadicThetaLoop
import TwoAxisHelicoid.ThetaExpression

namespace TwoAxisHelicoid

def thetaPositiveSeedExpression : BallExpression :=
  .exp (.mul (.input 0) .imaginaryUnit)
def thetaNegativeSeedExpression : BallExpression :=
  .exp (.mul (.neg (.input 0)) .imaginaryUnit)

structure DyadicThetaSeed where
  positive : DyadicExpressionTrace
  negative : DyadicExpressionTrace
  positiveSquare : DyadicBall
  negativeSquare : DyadicBall
  deriving Repr

namespace DyadicThetaSeed

def Valid (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) : Prop :=
  w.positive.Valid cfg (threeDyadic bv .zero .zero) thetaPositiveSeedExpression ∧
  w.negative.Valid cfg (threeDyadic bv .zero .zero) thetaNegativeSeedExpression ∧
  DyadicBall.ChecksMul cfg.prec w.positiveSquare w.positive.output w.positive.output ∧
  DyadicBall.ChecksMul cfg.prec w.negativeSquare w.negative.output w.negative.output

instance (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) :
    Decidable (w.Valid cfg bv) := by unfold Valid; infer_instance

def Contains (prec : ℕ) (v : ℂ) (w : DyadicThetaSeed) : Prop :=
  (w.positive.output.toBall prec).Contains (Complex.exp (v*Complex.I)) ∧
  (w.negative.output.toBall prec).Contains (Complex.exp (-v*Complex.I)) ∧
  (w.positiveSquare.toBall prec).Contains (Complex.exp (2*v*Complex.I)) ∧
  (w.negativeSquare.toBall prec).Contains (Complex.exp (-2*v*Complex.I))

theorem sound {bv : DyadicBall} {v : ℂ} (cfg : BallConfig)
    (hv : (bv.toBall cfg.prec).Contains v) (w : DyadicThetaSeed) (hw : w.Valid cfg bv) :
    w.Contains cfg.prec v := by
  have he := threeDyadic_contains hv (DyadicBall.zero_contains cfg.prec)
    (DyadicBall.zero_contains cfg.prec)
  have hp := w.positive.sound cfg _ _ he _ hw.1
  have hm := w.negative.sound cfg _ _ he _ hw.2.1
  simp only [thetaPositiveSeedExpression, thetaNegativeSeedExpression,
    BallExpression.value, BallExpression.value_imaginaryUnit, threeValues] at hp hm
  refine ⟨hp, hm, ?_, ?_⟩
  · convert DyadicBall.mul_contains hp hp hw.2.2.1 using 1
    rw [← Complex.exp_add]
    congr 1
    ring
  · convert DyadicBall.mul_contains hm hm hw.2.2.2 using 1
    rw [← Complex.exp_add]
    congr 1
    ring

end DyadicThetaSeed
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaSeed.sound
