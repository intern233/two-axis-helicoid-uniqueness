import TwoAxisHelicoid.TraceDataCheckBridge
import TwoAxisHelicoid.TraceDataProjections

namespace TwoAxisHelicoid.TraceData

namespace DyadicThetaATrace

theorem interpret_check (cfg : BallConfig) (N err : ℕ) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) :
    w.interpret.check cfg.interpret N err bq.interpret ba.interpret bc.interpret bz.interpret =
      w.check cfg N err bq ba bc bz := by
  simp only [interpret, check, TwoAxisHelicoid.DyadicThetaATrace.check]
  have he : TwoAxisHelicoid.threeDyadic bz.interpret ba.interpret .zero =
      (fun i => (threeDyadic bz ba .zero i).interpret) := (interpret_threeDyadic bz ba .zero).symm
  have harg : thetaArgumentExpression.interpret = TwoAxisHelicoid.thetaArgumentExpression := rfl
  have hshift : thetaShiftedArgumentExpression.interpret = TwoAxisHelicoid.thetaShiftedArgumentExpression := rfl
  have hresult : thetaAFromJetsExpression.interpret = TwoAxisHelicoid.thetaAFromJetsExpression := rfl
  rw [he, ← harg, ← hshift]
  simp only [DyadicExpressionTrace.interpret_check, DyadicExpressionTrace.interpret_output,
    DyadicThetaSeed.interpret_check, DyadicThetaTrace.interpret_check,
    DyadicThetaTrace.interpret_output, BallConfig.interpret_prec,
    DyadicBall.interpret_ChecksImOne, DyadicBall.interpret_lower]
  rw [← interpret_fiveDyadic, ← hresult, DyadicExpressionTrace.interpret_check]

end DyadicThetaATrace

theorem interpret_dyadicInputList_apply (xs : List DyadicBall) (i : ℕ) :
    (dyadicInputList xs i).interpret = TwoAxisHelicoid.dyadicInputList (xs.map DyadicBall.interpret) i := by
  induction xs generalizing i with
  | nil => rfl
  | cons b xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem interpret_dyadicInputList (xs : List DyadicBall) :
    (fun i => (dyadicInputList xs i).interpret) = TwoAxisHelicoid.dyadicInputList (xs.map DyadicBall.interpret) :=
  funext (interpret_dyadicInputList_apply xs)

namespace RangeDerivativeTrace

theorem interpret_inputs (p : RangeDerivativeParameters) (w : RangeDerivativeTrace) :
    (w.inputs p).map DyadicBall.interpret = w.interpret.inputs p.interpret := by
  simp only [inputs, TwoAxisHelicoid.RangeDerivativeTrace.inputs, interpret,
    RangeDerivativeParameters.interpret, RangeDyadicParameters.interpret,
    DyadicThetaATrace.interpret, DyadicThetaTrace.interpret,
    List.map_cons, List.map_nil, TwoAxisHelicoid.DyadicThetaATrace.output, DyadicThetaATrace.output,
    DyadicExpressionTrace.interpret_output]

theorem interpret_check (s : TwoAxisHelicoid.RangeCertificateSetup) (p : RangeDerivativeParameters)
    (z : DyadicBall) (w : RangeDerivativeTrace) :
    w.interpret.check s p.interpret z.interpret = w.check (setupOf s) p z := by
  have hcfg : s.config = (setupOf s).config.interpret := rfl
  have he : TwoAxisHelicoid.dyadicInputList (w.interpret.inputs p.interpret) =
      (fun i => (dyadicInputList (w.inputs p) i).interpret) := by
    rw [← interpret_inputs]
    exact (interpret_dyadicInputList _).symm
  have hA : derivativeAaExpression.interpret = TwoAxisHelicoid.derivativeAaExpression := rfl
  have hT : derivativeAtExpression.interpret = TwoAxisHelicoid.derivativeAtExpression := rfl
  unfold check TwoAxisHelicoid.RangeDerivativeTrace.check
  rw [he, hcfg, ← hA, ← hT]
  simp only [interpret, RangeDerivativeParameters.interpret, RangeDyadicParameters.interpret,
    DyadicCoefficientTrace.interpret_output, DyadicExpressionTrace.interpret_output,
    DyadicThetaATrace.interpret_check, DyadicThetaTrace.interpret_check,
    DyadicThetaATrace.interpret_seed, DyadicThetaATrace.interpret_shiftedSeed,
    DyadicThetaATrace.interpret_thetaShifted, DyadicThetaTrace.interpret_output,
    DyadicBall.interpret_lower, DyadicExpressionTrace.interpret_check, setupOf]

theorem valid_of_check (s : TwoAxisHelicoid.RangeCertificateSetup) (p : RangeDerivativeParameters)
    (z : DyadicBall) (w : RangeDerivativeTrace) (hw : w.check (setupOf s) p z = true) :
    w.interpret.Valid s p.interpret z.interpret := by
  apply (TwoAxisHelicoid.RangeDerivativeTrace.check_eq_true _ _ _ _).mp
  rw [interpret_check]
  exact hw

theorem valid_of_check_as (s : TwoAxisHelicoid.RangeCertificateSetup) (sd : RangeCertificateSetup)
    (hs : setupOf s = sd) (p : RangeDerivativeParameters) (z : DyadicBall)
    (w : RangeDerivativeTrace) (hw : w.check sd p z = true) :
    w.interpret.Valid s p.interpret z.interpret := by
  apply valid_of_check s p z w
  rw [hs]
  exact hw

end RangeDerivativeTrace

namespace RangeDerivativeNode

theorem interpret_check (s : TwoAxisHelicoid.RangeCertificateSetup) (p : RangeDerivativeParameters)
    (center : DyadicBall) (h node weight : ℚ) (w : RangeDerivativeNode) :
    w.interpret.check s p.interpret center.interpret h node weight =
      w.check (setupOf s) p center h node weight := by
  have hcfg : s.config = (setupOf s).config.interpret := rfl
  have hA : TwoAxisHelicoid.threeDyadic w.function.resultA.output.interpret .zero .zero =
      (fun i => (threeDyadic w.function.resultA.output .zero .zero i).interpret) :=
    (interpret_threeDyadic w.function.resultA.output .zero .zero).symm
  have hT : TwoAxisHelicoid.threeDyadic w.function.resultT.output.interpret .zero .zero =
      (fun i => (threeDyadic w.function.resultT.output .zero .zero i).interpret) :=
    (interpret_threeDyadic w.function.resultT.output .zero .zero).symm
  have hexpr : (BallExpression.mul (.rational weight) (.input 0)).interpret =
      TwoAxisHelicoid.BallExpression.mul (.rational weight) (.input 0) := rfl
  unfold check TwoAxisHelicoid.RangeDerivativeNode.check
  simp only [interpret, RangeDerivativeTrace.interpret_check,
    RangeDerivativeTrace.interpret_resultA, RangeDerivativeTrace.interpret_resultT,
    DyadicExpressionTrace.interpret_output]
  rw [hA, hT, hcfg, ← hexpr]
  simp only [DyadicExpressionTrace.interpret_check]
  congr 3
  simp only [TwoAxisHelicoid.ComplexBall.coarsens, TwoAxisHelicoid.QComplex.absUpper, TwoAxisHelicoid.QComplex.sub,
    TwoAxisHelicoid.QComplex.add, TwoAxisHelicoid.QComplex.neg, TwoAxisHelicoid.DyadicBall.toBall, DyadicBall.interpret,
    TwoAxisHelicoid.ComplexBall.add, TwoAxisHelicoid.ComplexBall.rational, TwoAxisHelicoid.ComplexBall.point, TwoAxisHelicoid.QComplex.ofRat,
    ComplexBall.coarsens, QComplex.absUpper, QComplex.sub, QComplex.add, QComplex.neg,
    DyadicBall.toBall, ComplexBall.add, ComplexBall.rational, ComplexBall.point,
    QComplex.ofRat, rat_abs_eq, BallConfig.interpret_prec, setupOf]
  rfl

theorem valid_of_check (s : TwoAxisHelicoid.RangeCertificateSetup) (p : RangeDerivativeParameters)
    (center : DyadicBall) (h node weight : ℚ) (w : RangeDerivativeNode)
    (hw : w.check (setupOf s) p center h node weight = true) :
    w.interpret.Valid s p.interpret center.interpret h node weight := by
  apply (TwoAxisHelicoid.RangeDerivativeNode.check_eq_true _ _ _ _ _ _ _).mp
  rw [interpret_check]
  exact hw

theorem valid_of_check_as (s : TwoAxisHelicoid.RangeCertificateSetup) (sd : RangeCertificateSetup)
    (hs : setupOf s = sd) (p : RangeDerivativeParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : RangeDerivativeNode)
    (hw : w.check sd p center h node weight = true) :
    w.interpret.Valid s p.interpret center.interpret h node weight := by
  apply valid_of_check s p center h node weight w
  rw [hs]
  exact hw

end RangeDerivativeNode
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.RangeDerivativeTrace.valid_of_check
#print axioms TwoAxisHelicoid.TraceData.RangeDerivativeNode.valid_of_check
