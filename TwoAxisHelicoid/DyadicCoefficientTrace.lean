import TwoAxisHelicoid.DyadicThetaATrace

namespace TwoAxisHelicoid

def thetaCoefficientExpression : BallExpression :=
  .pow (.div (.mul .pi (.input 0)) (.mul (.rational 2) (.input 1))) 2

theorem value_thetaCoefficientExpression (t a : ℝ) :
    thetaCoefficientExpression.value (threeValues (thetaJet t 1 0)
      (thetaJet t 0 (Real.pi*a/2)) 0) = thetaACoefficient t a := by
  simp only [thetaCoefficientExpression, BallExpression.value_pow, BallExpression.value_div,
    BallExpression.value, BallExpression.value_rational, threeValues, Rat.cast_ofNat]
  rfl

structure DyadicCoefficientTrace where
  argument : DyadicExpressionTrace
  seedZero : DyadicThetaSeed
  seedA : DyadicThetaSeed
  thetaZero : DyadicThetaTrace
  thetaA : DyadicThetaTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicCoefficientTrace

def output (w : DyadicCoefficientTrace) : DyadicBall := w.result.output

def Valid (cfg : BallConfig) (N err : ℕ) (bq ba : DyadicBall)
    (w : DyadicCoefficientTrace) : Prop :=
  w.argument.Valid cfg (threeDyadic ba .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne cfg.prec ∧
  w.seedZero.Valid cfg .zero ∧ w.seedA.Valid cfg w.argument.output ∧
  w.thetaZero.Valid cfg 1 N err bq w.seedZero ∧ w.thetaA.Valid cfg 0 N err bq w.seedA ∧
  w.result.Valid cfg (threeDyadic w.thetaZero.output w.thetaA.output .zero)
    thetaCoefficientExpression

instance (cfg : BallConfig) (N err : ℕ) (bq ba : DyadicBall) (w : DyadicCoefficientTrace) :
    Decidable (w.Valid cfg N err bq ba) := by unfold Valid; infer_instance

theorem sound {bq ba : DyadicBall} {t a : ℝ} (cfg : BallConfig) (N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (ba.toBall cfg.prec).Contains (a : ℂ))
    (htail0 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 0 v-thetaPartial t 0 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (htail1 : ∀ v : ℂ, |v.im| ≤ 1 → ‖thetaJet t 1 v-thetaPartial t 1 N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicCoefficientTrace) (hw : w.Valid cfg N err bq ba) :
    (w.output.toBall cfg.prec).Contains (thetaACoefficient t a) := by
  rcases hw with ⟨harg, hy, hs0, hsa, ht0, hta, hresult⟩
  have hz := DyadicBall.zero_contains cfg.prec
  have hv := w.argument.sound cfg _ _ (threeDyadic_contains ha hz hz) _ harg
  rw [value_thetaArgumentExpression] at hv
  have hsz := w.seedZero.sound cfg hz hs0
  have hsv := w.seedA.sound cfg hv hsa
  have h0 := w.thetaZero.sound cfg 1 N err hq w.seedZero hsz (htail1 0 (by norm_num)) ht0
  have h1 := w.thetaA.sound cfg 0 N err hq w.seedA hsv
    (htail0 _ (DyadicBall.im_le_one hv hy)) hta
  have hout := w.result.sound cfg _ _ (threeDyadic_contains h0 h1 hz) _ hresult
  rw [value_thetaCoefficientExpression] at hout
  exact hout

end DyadicCoefficientTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicCoefficientTrace.sound
