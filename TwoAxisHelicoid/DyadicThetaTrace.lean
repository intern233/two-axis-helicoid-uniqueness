import TwoAxisHelicoid.DyadicThetaSeed
import TwoAxisHelicoid.DyadicInflate

namespace TwoAxisHelicoid

structure DyadicThetaTrace where
  loop : DyadicThetaLoop
  output : DyadicBall
  deriving Repr

namespace DyadicThetaTrace

def Valid (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall) (seed : DyadicThetaSeed)
    (w : DyadicThetaTrace) : Prop :=
  w.loop.length = N ∧
  w.loop.Valid cfg j bq seed.positive.output seed.negative.output
    seed.positiveSquare seed.negativeSquare ∧
  w.output.Coarsens ((w.loop.state cfg.prec bq seed.positive.output seed.negative.output).sum.inflate err)

instance (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall) (seed : DyadicThetaSeed)
    (w : DyadicThetaTrace) : Decidable (w.Valid cfg j N err bq seed) := by
  unfold Valid
  infer_instance

theorem sound {bq : DyadicBall} {t : ℝ} {v : ℂ} (cfg : BallConfig) (j N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (seed : DyadicThetaSeed) (hs : seed.Contains cfg.prec v)
    (htail : ‖thetaJet t j v-thetaPartial t j N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicThetaTrace) (hw : w.Valid cfg j N err bq seed) :
    (w.output.toBall cfg.prec).Contains (thetaJet t j v) := by
  have hp := (w.loop.sound cfg j hq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hw.2.1).1
  rw [hw.1] at hp
  exact DyadicBall.coarsen_contains (DyadicBall.inflate_contains hp htail) hw.2.2

end DyadicThetaTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaTrace.sound
