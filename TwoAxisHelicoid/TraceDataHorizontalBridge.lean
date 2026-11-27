import TwoAxisHelicoid.TraceDataHorizontal
import TwoAxisHelicoid.TraceDataCheckBridge
import TwoAxisHelicoid.TraceDataProjections
import TwoAxisHelicoid.HorizontalRangeCell

namespace TwoAxisHelicoid.TraceData

def horizontalSetupOf (s : TwoAxisHelicoid.HorizontalRangeSetup) : HorizontalRangeSetup :=
  ⟨⟨s.config.prec, s.config.terms, s.config.squarings⟩, s.imaginary, s.terms, s.error⟩

namespace DyadicBall

theorem interpret_ChecksImaginaryBound (prec : ℕ) (bound : ℚ) (b : DyadicBall) :
    b.interpret.ChecksImaginaryBound prec bound ↔ b.ChecksImaginaryBound prec bound := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksImaginaryBound, ChecksImaginaryBound,
    TwoAxisHelicoid.DyadicBall.toBall, toBall, interpret, rat_abs_eq]
  rfl

end DyadicBall

namespace DyadicThetaATrace

theorem interpret_horizontalCheck (s : TwoAxisHelicoid.HorizontalRangeSetup)
    (bq ba bc bz : DyadicBall) (w : DyadicThetaATrace) :
    w.interpret.horizontalCheck s bq.interpret ba.interpret bc.interpret bz.interpret =
      w.horizontalCheck (horizontalSetupOf s) bq ba bc bz := by
  have he : TwoAxisHelicoid.threeDyadic bz.interpret ba.interpret .zero =
      (fun i => (threeDyadic bz ba .zero i).interpret) :=
    (interpret_threeDyadic bz ba .zero).symm
  have harg : thetaArgumentExpression.interpret = TwoAxisHelicoid.thetaArgumentExpression := rfl
  have hshift : thetaShiftedArgumentExpression.interpret = TwoAxisHelicoid.thetaShiftedArgumentExpression := rfl
  have hresult : thetaAFromJetsExpression.interpret = TwoAxisHelicoid.thetaAFromJetsExpression := rfl
  have hcfg : s.config = (horizontalSetupOf s).config.interpret := rfl
  simp only [interpret, horizontalCheck, TwoAxisHelicoid.DyadicThetaATrace.horizontalCheck]
  rw [he, ← harg, ← hshift, hcfg]
  simp only [DyadicExpressionTrace.interpret_check, DyadicExpressionTrace.interpret_output,
    DyadicThetaSeed.interpret_check, DyadicThetaTrace.interpret_check,
    DyadicThetaTrace.interpret_output, BallConfig.interpret_prec,
    DyadicBall.interpret_ChecksImaginaryBound, DyadicBall.interpret_lower]
  rw [← interpret_fiveDyadic, ← hresult, DyadicExpressionTrace.interpret_check]
  rfl

theorem horizontal_valid_of_check_as (s : TwoAxisHelicoid.HorizontalRangeSetup)
    (sd : HorizontalRangeSetup) (hs : horizontalSetupOf s = sd)
    (bq ba bc bz : DyadicBall) (w : DyadicThetaATrace)
    (hw : w.horizontalCheck sd bq ba bc bz = true) :
    w.interpret.HorizontalValid s bq.interpret ba.interpret bc.interpret bz.interpret := by
  apply (TwoAxisHelicoid.DyadicThetaATrace.horizontalCheck_eq_true _ _ _ _ _ _).mp
  rw [interpret_horizontalCheck, hs]
  exact hw

end DyadicThetaATrace

namespace HorizontalRangeNode

def interpret (w : HorizontalRangeNode) : TwoAxisHelicoid.HorizontalRangeNode :=
  ⟨w.point.interpret, w.function.interpret, w.weighted.interpret⟩

theorem interpret_check (s : TwoAxisHelicoid.HorizontalRangeSetup) (p : RangeDyadicParameters)
    (center : DyadicBall) (h node weight : ℚ) (w : HorizontalRangeNode) :
    w.interpret.check s p.interpret center.interpret h node weight =
      w.check (horizontalSetupOf s) p center h node weight := by
  have hcfg : s.config = (horizontalSetupOf s).config.interpret := rfl
  have he : TwoAxisHelicoid.threeDyadic w.function.output.interpret .zero .zero =
      (fun i => (threeDyadic w.function.output .zero .zero i).interpret) :=
    (interpret_threeDyadic w.function.output .zero .zero).symm
  have hexpr : (BallExpression.mul (.rational weight) (.input 0)).interpret =
      TwoAxisHelicoid.BallExpression.mul (.rational weight) (.input 0) := rfl
  unfold check TwoAxisHelicoid.HorizontalRangeNode.check
  simp only [interpret, RangeDyadicParameters.interpret,
    DyadicExpressionTrace.interpret_output, DyadicCoefficientTrace.interpret_output,
    DyadicThetaATrace.interpret_horizontalCheck, DyadicThetaATrace.interpret_output]
  rw [he, hcfg, ← hexpr]
  simp only [DyadicExpressionTrace.interpret_check]
  congr 2
  simp only [TwoAxisHelicoid.ComplexBall.coarsens, TwoAxisHelicoid.QComplex.absUpper, TwoAxisHelicoid.QComplex.sub,
    TwoAxisHelicoid.QComplex.add, TwoAxisHelicoid.QComplex.neg, TwoAxisHelicoid.DyadicBall.toBall, DyadicBall.interpret,
    TwoAxisHelicoid.ComplexBall.add, TwoAxisHelicoid.ComplexBall.rational, TwoAxisHelicoid.ComplexBall.point, TwoAxisHelicoid.QComplex.ofRat,
    ComplexBall.coarsens, QComplex.absUpper, QComplex.sub, QComplex.add, QComplex.neg,
    DyadicBall.toBall, ComplexBall.add, ComplexBall.rational, ComplexBall.point,
    QComplex.ofRat, rat_abs_eq, BallConfig.interpret_prec, horizontalSetupOf]
  rfl

theorem valid_of_check_as (s : TwoAxisHelicoid.HorizontalRangeSetup) (sd : HorizontalRangeSetup)
    (hs : horizontalSetupOf s = sd) (p : RangeDyadicParameters)
    (center : DyadicBall) (h node weight : ℚ) (w : HorizontalRangeNode)
    (hw : w.check sd p center h node weight = true) :
    w.interpret.Valid s p.interpret center.interpret h node weight := by
  apply (TwoAxisHelicoid.HorizontalRangeNode.check_eq_true _ _ _ _ _ _ _).mp
  rw [interpret_check, hs]
  exact hw

end HorizontalRangeNode

namespace HorizontalRangeCell

def interpret {K : ℕ} (w : HorizontalRangeCell K) : TwoAxisHelicoid.HorizontalRangeCell K :=
  ⟨w.center.interpret, w.disk.interpret, w.diskFunction.interpret,
    fun i => (w.nodes i).interpret, w.output.interpret⟩

end HorizontalRangeCell
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.DyadicThetaATrace.horizontal_valid_of_check_as
#print axioms TwoAxisHelicoid.TraceData.HorizontalRangeNode.valid_of_check_as
