import TwoAxisHelicoid.DyadicThetaTrace
import TwoAxisHelicoid.HorizontalEnclosure

namespace TwoAxisHelicoid

def fiveDyadic (a b c d e : DyadicBall) : ℕ → DyadicBall
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _+5 => .zero

noncomputable def fiveValues (a b c d e : ℂ) : ℕ → ℂ
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _+5 => 0

theorem fiveDyadic_contains {prec : ℕ} {ba bb bc bd be : DyadicBall} {a b c d e : ℂ}
    (ha : (ba.toBall prec).Contains a) (hb : (bb.toBall prec).Contains b)
    (hc : (bc.toBall prec).Contains c) (hd : (bd.toBall prec).Contains d)
    (he : (be.toBall prec).Contains e) :
    ∀ n, ((fiveDyadic ba bb bc bd be n).toBall prec).Contains (fiveValues a b c d e n) := by
  intro n
  rcases n with _ | (_ | (_ | (_ | (_ | n))))
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact DyadicBall.zero_contains prec

def thetaArgumentExpression : BallExpression :=
  .mul (.mul .pi (.input 0)) (.rational (1/2))

def thetaShiftedArgumentExpression : BallExpression :=
  .mul (.mul .pi (.sub (.input 0) (.input 1))) (.rational (1/2))

def thetaAFromJetsExpression : BallExpression :=
  .mul (.mul (.input 1) (.pow (.div (.input 2) (.input 3)) 2))
    (.exp (.mul (.mul (.sub (.input 0) (.rational 1)) .pi)
      (.div (.input 4) (.input 3))))

theorem value_thetaArgumentExpression (z a : ℂ) :
    thetaArgumentExpression.value (threeValues z a 0) = Real.pi*z/2 := by
  simp [thetaArgumentExpression, BallExpression.value, threeValues]
  ring

theorem value_thetaShiftedArgumentExpression (z a : ℂ) :
    thetaShiftedArgumentExpression.value (threeValues z a 0) = Real.pi*(z-a)/2 := by
  simp [thetaShiftedArgumentExpression, BallExpression.value, threeValues]
  ring

theorem value_thetaAFromJetsExpression (t a : ℝ) (z : ℂ) :
    thetaAFromJetsExpression.value (fiveValues a (thetaACoefficient t a)
      (thetaJet t 0 (Real.pi*(z-a)/2)) (thetaJet t 0 (Real.pi*z/2))
      (thetaJet t 1 (Real.pi*z/2))) = thetaA t a z := by
  simp only [thetaAFromJetsExpression, BallExpression.value, BallExpression.value_pow,
    BallExpression.value_div, BallExpression.value_sub, BallExpression.value_rational,
    fiveValues, Rat.cast_one]
  rfl

end TwoAxisHelicoid
