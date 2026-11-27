import TwoAxisHelicoid.HorizontalRangeSetup
import TwoAxisHelicoid.DyadicBooleanCheck

namespace TwoAxisHelicoid

namespace DyadicBall

def ChecksImaginaryBound (prec : ℕ) (bound : ℚ) (b : DyadicBall) : Prop :=
  |(b.toBall prec).center.im|+(b.toBall prec).radius ≤ bound

instance (prec : ℕ) (bound : ℚ) (b : DyadicBall) : Decidable (b.ChecksImaginaryBound prec bound) := by
  unfold ChecksImaginaryBound
  infer_instance

theorem imaginary_bound {prec : ℕ} {bound : ℚ} {b : DyadicBall} {v : ℂ}
    (hv : (b.toBall prec).Contains v) (h : b.ChecksImaginaryBound prec bound) :
    |v.im| ≤ (bound : ℝ) := by
  apply (ComplexBall.abs_im_le hv).trans
  exact_mod_cast h

end DyadicBall

namespace DyadicThetaATrace

def HorizontalValid (s : HorizontalRangeSetup) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Prop :=
  w.argument.Valid s.config (threeDyadic bz ba .zero) thetaArgumentExpression ∧
  w.shiftedArgument.Valid s.config (threeDyadic bz ba .zero) thetaShiftedArgumentExpression ∧
  w.argument.output.ChecksImaginaryBound s.config.prec s.imaginary ∧
  w.shiftedArgument.output.ChecksImaginaryBound s.config.prec s.imaginary ∧
  w.seed.Valid s.config w.argument.output ∧ w.shiftedSeed.Valid s.config w.shiftedArgument.output ∧
  w.theta0.Valid s.config 0 s.terms s.error bq w.seed ∧
  w.theta1.Valid s.config 1 s.terms s.error bq w.seed ∧
  w.thetaShifted.Valid s.config 0 s.terms s.error bq w.shiftedSeed ∧ 0 < w.theta0.output.lower ∧
  w.result.Valid s.config (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

instance (s : HorizontalRangeSetup) (bq ba bc bz : DyadicBall) (w : DyadicThetaATrace) :
    Decidable (w.HorizontalValid s bq ba bc bz) := by unfold HorizontalValid; infer_instance

def horizontalCheck (s : HorizontalRangeSetup) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Bool :=
  w.argument.check s.config (threeDyadic bz ba .zero) thetaArgumentExpression &&
  w.shiftedArgument.check s.config (threeDyadic bz ba .zero) thetaShiftedArgumentExpression &&
  decide (w.argument.output.ChecksImaginaryBound s.config.prec s.imaginary) &&
  decide (w.shiftedArgument.output.ChecksImaginaryBound s.config.prec s.imaginary) &&
  w.seed.check s.config w.argument.output && w.shiftedSeed.check s.config w.shiftedArgument.output &&
  w.theta0.check s.config 0 s.terms s.error bq w.seed &&
  w.theta1.check s.config 1 s.terms s.error bq w.seed &&
  w.thetaShifted.check s.config 0 s.terms s.error bq w.shiftedSeed && decide (0 < w.theta0.output.lower) &&
  w.result.check s.config (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

theorem horizontalCheck_eq_true (s : HorizontalRangeSetup) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) :
    w.horizontalCheck s bq ba bc bz = true ↔ w.HorizontalValid s bq ba bc bz := by
  simp only [horizontalCheck, HorizontalValid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicExpressionTrace.check_eq_true, DyadicThetaSeed.check_eq_true,
    DyadicThetaTrace.check_eq_true, and_assoc]

theorem horizontal_sound {bq ba bc bz : DyadicBall} {t a : ℝ} {z : ℂ}
    (s : HorizontalRangeSetup) (hs : s.Valid) (ht : (s.lower : ℝ) ≤ t)
    (hq : (bq.toBall s.config.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (ba.toBall s.config.prec).Contains (a : ℂ))
    (hc : (bc.toBall s.config.prec).Contains (thetaACoefficient t a))
    (hz : (bz.toBall s.config.prec).Contains z)
    (w : DyadicThetaATrace) (hw : w.HorizontalValid s bq ba bc bz) :
    (w.output.toBall s.config.prec).Contains (thetaA t a z) ∧ z ∈ thetaRegular t := by
  rcases hw with ⟨hav, ham, hyv, hym, hsv, hsm, ht0, ht1, htm, hlower, hresult⟩
  have he := threeDyadic_contains hz ha (DyadicBall.zero_contains s.config.prec)
  have hv := w.argument.sound s.config _ _ he _ hav
  have hm := w.shiftedArgument.sound s.config _ _ he _ ham
  rw [value_thetaArgumentExpression] at hv
  rw [value_thetaShiftedArgumentExpression] at hm
  have hvs := w.seed.sound s.config hv hsv
  have hms := w.shiftedSeed.sound s.config hm hsm
  have h0 := w.theta0.sound s.config 0 s.terms s.error hq w.seed hvs
    (s.tail_bound hs ht 0 _ (DyadicBall.imaginary_bound hv hyv)) ht0
  have h1 := w.theta1.sound s.config 1 s.terms s.error hq w.seed hvs
    (s.tail_bound hs ht 1 _ (DyadicBall.imaginary_bound hv hyv)) ht1
  have hshift := w.thetaShifted.sound s.config 0 s.terms s.error hq w.shiftedSeed hms
    (s.tail_bound hs ht 0 _ (DyadicBall.imaginary_bound hm hym)) htm
  have hout := w.result.sound s.config _ _ (fiveDyadic_contains ha hc hshift h0 h1) _ hresult
  rw [value_thetaAFromJetsExpression] at hout
  exact ⟨hout, ComplexBall.ne_zero_of_lower_pos h0 (DyadicBall.lower_pos_toBall hlower)⟩

end DyadicThetaATrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaATrace.horizontal_sound
