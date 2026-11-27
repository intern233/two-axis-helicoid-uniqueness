import TwoAxisHelicoid.TraceDataJacobi
import TwoAxisHelicoid.TraceDataCheckBridge
import TwoAxisHelicoid.DyadicJacobiEuler
import TwoAxisHelicoid.DyadicJacobiSecond

namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 800000

namespace DyadicBall
@[simp] theorem interpret_normUpper (prec : ℕ) (b : DyadicBall) :
    b.interpret.normUpper prec = b.normUpper prec := by
  simp only [TwoAxisHelicoid.DyadicBall.normUpper, normUpper, TwoAxisHelicoid.DyadicBall.toBall, toBall,
    TwoAxisHelicoid.QComplex.absUpper, QComplex.absUpper, interpret, rat_abs_eq]
  rfl
end DyadicBall

namespace DyadicJacobiProductState
def interpret (s : DyadicJacobiProductState) : TwoAxisHelicoid.DyadicJacobiProductState :=
  ⟨s.product.interpret, s.term.interpret⟩
end DyadicJacobiProductState

namespace DyadicJacobiProductLoop
def interpret : DyadicJacobiProductLoop → TwoAxisHelicoid.DyadicJacobiProductLoop
  | .zero => .zero
  | .step p f s => .step p.interpret f.interpret s.interpret

@[simp] theorem interpret_state (prec : ℕ) (bz : DyadicBall) (w : DyadicJacobiProductLoop) :
    w.interpret.state prec bz.interpret = (w.state prec bz).interpret := by
  cases w <;> rfl

theorem interpret_valid (prec : ℕ) (bq bz : DyadicBall)
    (w : DyadicJacobiProductLoop) :
    w.interpret.Valid prec bq.interpret bz.interpret ↔ w.Valid prec bq bz := by
  induction w with
  | zero => rfl
  | step p f s ih =>
    have hone : TwoAxisHelicoid.DyadicBall.one prec = (DyadicBall.one prec).interpret := rfl
    simp only [interpret, TwoAxisHelicoid.DyadicJacobiProductLoop.Valid, Valid, interpret_state, DyadicJacobiProductState.interpret,
      ih, DyadicBall.interpret_neg, hone,
      DyadicBall.interpret_ChecksAdd, DyadicBall.interpret_ChecksMul]

end DyadicJacobiProductLoop

namespace DyadicJacobiProductTrace
def interpret (w : DyadicJacobiProductTrace) : TwoAxisHelicoid.DyadicJacobiProductTrace :=
  ⟨w.loop.interpret, w.output.interpret⟩

theorem interpret_valid (prec err : ℕ) (bq bz : DyadicBall)
    (w : DyadicJacobiProductTrace) :
    w.interpret.Valid prec err bq.interpret bz.interpret ↔
      w.Valid prec err bq bz := by
  simp only [interpret, TwoAxisHelicoid.DyadicJacobiProductTrace.Valid, Valid,
    DyadicJacobiProductLoop.interpret_state, DyadicJacobiProductLoop.interpret_valid, DyadicJacobiProductState.interpret,
    DyadicBall.interpret_normUpper,
    DyadicBall.interpret_inflate, DyadicBall.interpret_Coarsens]
  rfl

end DyadicJacobiProductTrace

namespace DyadicJacobiEulerState
def interpret (s : DyadicJacobiEulerState) : TwoAxisHelicoid.DyadicJacobiEulerState :=
  ⟨s.sum.interpret, s.term.interpret⟩
end DyadicJacobiEulerState

namespace DyadicJacobiEulerLoop
def interpret : DyadicJacobiEulerLoop → TwoAxisHelicoid.DyadicJacobiEulerLoop
  | .zero => .zero
  | .step p f s => .step p.interpret f.interpret s.interpret

@[simp] theorem interpret_state (bz : DyadicBall) (w : DyadicJacobiEulerLoop) :
    w.interpret.state bz.interpret = (w.state bz).interpret := by
  cases w <;> rfl

theorem interpret_valid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiEulerLoop) :
    w.interpret.Valid cfg.interpret bq.interpret bz.interpret ↔ w.Valid cfg bq bz := by
  induction w with
  | zero => rfl
  | step p f s ih =>
    simp only [interpret, TwoAxisHelicoid.DyadicJacobiEulerLoop.Valid, Valid, interpret_state, DyadicJacobiEulerState.interpret,
      BallConfig.interpret_prec, ih,
      DyadicBall.interpret_ChecksAdd, DyadicBall.interpret_ChecksMul, DyadicExpressionTrace.interpret_output]
    have henv : TwoAxisHelicoid.threeDyadic (p.state bz).term.interpret .zero .zero =
        (fun i => (threeDyadic (p.state bz).term .zero .zero i).interpret) :=
      (interpret_threeDyadic _ .zero .zero).symm
    have he : jacobiEulerTermExpression.interpret = TwoAxisHelicoid.jacobiEulerTermExpression := rfl
    rw [henv, ← he, ← TwoAxisHelicoid.DyadicExpressionTrace.check_eq_true,
      DyadicExpressionTrace.interpret_check]

end DyadicJacobiEulerLoop

namespace DyadicJacobiEulerTrace
def interpret (w : DyadicJacobiEulerTrace) : TwoAxisHelicoid.DyadicJacobiEulerTrace :=
  ⟨w.loop.interpret, w.output.interpret⟩

theorem interpret_valid (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall)
    (w : DyadicJacobiEulerTrace) :
    w.interpret.Valid cfg.interpret err bq.interpret bz.interpret ↔
      w.Valid cfg err bq bz := by
  simp only [interpret, TwoAxisHelicoid.DyadicJacobiEulerTrace.Valid, Valid,
    DyadicJacobiEulerLoop.interpret_state, DyadicJacobiEulerLoop.interpret_valid, DyadicJacobiEulerState.interpret,
    BallConfig.interpret_prec, DyadicBall.interpret_normUpper,
    DyadicBall.interpret_inflate, DyadicBall.interpret_Coarsens]
  rfl

end DyadicJacobiEulerTrace

namespace DyadicJacobiSecondState
def interpret (s : DyadicJacobiSecondState) : TwoAxisHelicoid.DyadicJacobiSecondState :=
  ⟨s.sum.interpret, s.term.interpret⟩
end DyadicJacobiSecondState

namespace DyadicJacobiSecondLoop
def interpret : DyadicJacobiSecondLoop → TwoAxisHelicoid.DyadicJacobiSecondLoop
  | .zero => .zero
  | .step p f s => .step p.interpret f.interpret s.interpret

@[simp] theorem interpret_state (bz : DyadicBall) (w : DyadicJacobiSecondLoop) :
    w.interpret.state bz.interpret = (w.state bz).interpret := by
  cases w <;> rfl

theorem interpret_valid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiSecondLoop) :
    w.interpret.Valid cfg.interpret bq.interpret bz.interpret ↔ w.Valid cfg bq bz := by
  induction w with
  | zero => rfl
  | step p f s ih =>
    simp only [interpret, TwoAxisHelicoid.DyadicJacobiSecondLoop.Valid, Valid, interpret_state, DyadicJacobiSecondState.interpret,
      BallConfig.interpret_prec, ih,
      DyadicBall.interpret_ChecksAdd, DyadicBall.interpret_ChecksMul, DyadicExpressionTrace.interpret_output]
    have henv : TwoAxisHelicoid.threeDyadic (p.state bz).term.interpret .zero .zero =
        (fun i => (threeDyadic (p.state bz).term .zero .zero i).interpret) :=
      (interpret_threeDyadic _ .zero .zero).symm
    have he : jacobiSecondTermExpression.interpret = TwoAxisHelicoid.jacobiSecondTermExpression := rfl
    rw [henv, ← he, ← TwoAxisHelicoid.DyadicExpressionTrace.check_eq_true,
      DyadicExpressionTrace.interpret_check]

end DyadicJacobiSecondLoop

namespace DyadicJacobiSecondTrace
def interpret (w : DyadicJacobiSecondTrace) : TwoAxisHelicoid.DyadicJacobiSecondTrace :=
  ⟨w.loop.interpret, w.output.interpret⟩

theorem interpret_valid (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall)
    (w : DyadicJacobiSecondTrace) :
    w.interpret.Valid cfg.interpret err bq.interpret bz.interpret ↔
      w.Valid cfg err bq bz := by
  simp only [interpret, TwoAxisHelicoid.DyadicJacobiSecondTrace.Valid, Valid,
    DyadicJacobiSecondLoop.interpret_state, DyadicJacobiSecondLoop.interpret_valid, DyadicJacobiSecondState.interpret,
    BallConfig.interpret_prec, DyadicBall.interpret_normUpper,
    DyadicBall.interpret_inflate, DyadicBall.interpret_Coarsens]
  rfl

end DyadicJacobiSecondTrace

end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.DyadicJacobiProductTrace.interpret_valid
#print axioms TwoAxisHelicoid.TraceData.DyadicJacobiEulerTrace.interpret_valid
#print axioms TwoAxisHelicoid.TraceData.DyadicJacobiSecondTrace.interpret_valid

