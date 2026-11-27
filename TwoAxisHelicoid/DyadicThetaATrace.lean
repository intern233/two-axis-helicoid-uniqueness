import TwoAxisHelicoid.DyadicThetaAExpression

namespace TwoAxisHelicoid

namespace DyadicBall

def ChecksImOne (prec : ℕ) (b : DyadicBall) : Prop :=
  |b.im|+(b.radius : ℤ) ≤ denominator prec

instance (prec : ℕ) (b : DyadicBall) : Decidable (b.ChecksImOne prec) := by
  unfold ChecksImOne
  infer_instance

theorem im_le_one {prec : ℕ} {b : DyadicBall} {v : ℂ}
    (hv : (b.toBall prec).Contains v) (h : b.ChecksImOne prec) : |v.im| ≤ 1 := by
  apply (ComplexBall.abs_im_le hv).trans
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  have hh : |(b.im : ℚ)|+(b.radius : ℚ) ≤ (denominator prec : ℚ) := by exact_mod_cast h
  suffices hb : |(b.toBall prec).center.im|+(b.toBall prec).radius ≤ (1 : ℚ) by
    exact_mod_cast hb
  change |(b.im : ℚ)/(denominator prec : ℚ)|+(b.radius : ℚ)/(denominator prec : ℚ) ≤ 1
  rw [abs_div, abs_of_pos hd, ← add_div]
  exact (div_le_one hd).mpr hh

theorem lower_pos_toBall {prec : ℕ} {b : DyadicBall} (h : 0 < b.lower) :
    0 < (b.toBall prec).lower := by
  rw [lower_toBall]
  exact div_pos (Int.cast_pos.mpr h) (Int.cast_pos.mpr (denominator_pos prec))

end DyadicBall

structure DyadicThetaATrace where
  argument : DyadicExpressionTrace
  shiftedArgument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  shiftedSeed : DyadicThetaSeed
  theta0 : DyadicThetaTrace
  theta1 : DyadicThetaTrace
  thetaShifted : DyadicThetaTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicThetaATrace

def output (w : DyadicThetaATrace) : DyadicBall := w.result.output

def Valid (cfg : BallConfig) (N err : ℕ) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Prop :=
  w.argument.Valid cfg (threeDyadic bz ba .zero) thetaArgumentExpression ∧
  w.shiftedArgument.Valid cfg (threeDyadic bz ba .zero) thetaShiftedArgumentExpression ∧
  w.argument.output.ChecksImOne cfg.prec ∧
  w.shiftedArgument.output.ChecksImOne cfg.prec ∧
  w.seed.Valid cfg w.argument.output ∧ w.shiftedSeed.Valid cfg w.shiftedArgument.output ∧
  w.theta0.Valid cfg 0 N err bq w.seed ∧ w.theta1.Valid cfg 1 N err bq w.seed ∧
  w.thetaShifted.Valid cfg 0 N err bq w.shiftedSeed ∧ 0 < w.theta0.output.lower ∧
  w.result.Valid cfg (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

instance (cfg : BallConfig) (N err : ℕ) (bq ba bc bz : DyadicBall) (w : DyadicThetaATrace) :
    Decidable (w.Valid cfg N err bq ba bc bz) := by unfold Valid; infer_instance

theorem sound {bq ba bc bz : DyadicBall} {t a : ℝ} {z : ℂ}
    (cfg : BallConfig) (N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (ba.toBall cfg.prec).Contains (a : ℂ))
    (hc : (bc.toBall cfg.prec).Contains (thetaACoefficient t a))
    (hz : (bz.toBall cfg.prec).Contains z)
    (htail0 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 0 v-thetaPartial t 0 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (htail1 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 1 v-thetaPartial t 1 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicThetaATrace) (hw : w.Valid cfg N err bq ba bc bz) :
    (w.output.toBall cfg.prec).Contains (thetaA t a z) ∧ z ∈ thetaRegular t := by
  rcases hw with ⟨hav, ham, hyv, hym, hsv, hsm, ht0, ht1, htm, hlower, hresult⟩
  have he := threeDyadic_contains hz ha (DyadicBall.zero_contains cfg.prec)
  have hv := w.argument.sound cfg _ _ he _ hav
  have hm := w.shiftedArgument.sound cfg _ _ he _ ham
  rw [value_thetaArgumentExpression] at hv
  rw [value_thetaShiftedArgumentExpression] at hm
  have hvs := w.seed.sound cfg hv hsv
  have hms := w.shiftedSeed.sound cfg hm hsm
  have h0 := w.theta0.sound cfg 0 N err hq w.seed hvs
    (htail0 _ (DyadicBall.im_le_one hv hyv)) ht0
  have h1 := w.theta1.sound cfg 1 N err hq w.seed hvs
    (htail1 _ (DyadicBall.im_le_one hv hyv)) ht1
  have hshift := w.thetaShifted.sound cfg 0 N err hq w.shiftedSeed hms
    (htail0 _ (DyadicBall.im_le_one hm hym)) htm
  have hout := w.result.sound cfg _ _ (fiveDyadic_contains ha hc hshift h0 h1) _ hresult
  rw [value_thetaAFromJetsExpression] at hout
  exact ⟨hout, ComplexBall.ne_zero_of_lower_pos h0 (DyadicBall.lower_pos_toBall hlower)⟩

end DyadicThetaATrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaATrace.sound
