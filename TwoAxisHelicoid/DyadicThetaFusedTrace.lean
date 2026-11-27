import TwoAxisHelicoid.DyadicThetaFused

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 400000

def thetaFusedSeedPositiveExpression : BallExpression :=
  .exp (.mul (.input 1) (.const ⟨0,1⟩))
def thetaFusedSeedNegativeExpression : BallExpression :=
  .exp (.mul (.neg (.input 1)) (.const ⟨0,1⟩))
def thetaFusedRatioPositiveExpression : BallExpression :=
  .exp (.add (.neg (.mul .pi (.input 0)))
    (.mul (.mul (.rational 2) (.input 1)) (.const ⟨0,1⟩)))
def thetaFusedRatioNegativeExpression : BallExpression :=
  .exp (.sub (.neg (.mul .pi (.input 0)))
    (.mul (.mul (.rational 2) (.input 1)) (.const ⟨0,1⟩)))

structure DyadicThetaFusedSeed where
  positive : DyadicExpressionTrace
  negative : DyadicExpressionTrace
  positiveRatio : DyadicExpressionTrace
  negativeRatio : DyadicExpressionTrace
  deriving Repr

namespace DyadicThetaFusedSeed

def Valid (cfg : BallConfig) (bt bv : DyadicBall) (w : DyadicThetaFusedSeed) : Prop :=
  w.positive.Valid cfg (threeDyadic bt bv .zero) thetaFusedSeedPositiveExpression ∧
  w.negative.Valid cfg (threeDyadic bt bv .zero) thetaFusedSeedNegativeExpression ∧
  w.positiveRatio.Valid cfg (threeDyadic bt bv .zero) thetaFusedRatioPositiveExpression ∧
  w.negativeRatio.Valid cfg (threeDyadic bt bv .zero) thetaFusedRatioNegativeExpression

instance (cfg : BallConfig) (bt bv : DyadicBall) (w : DyadicThetaFusedSeed) :
    Decidable (w.Valid cfg bt bv) := by unfold Valid; infer_instance

def Contains (prec : ℕ) (t : ℝ) (v : ℂ) (w : DyadicThetaFusedSeed) : Prop :=
  (w.positive.output.toBall prec).Contains (Complex.exp (v*I)) ∧
  (w.negative.output.toBall prec).Contains (Complex.exp (-v*I)) ∧
  (w.positiveRatio.output.toBall prec).Contains (Complex.exp (-Real.pi*t+2*v*I)) ∧
  (w.negativeRatio.output.toBall prec).Contains (Complex.exp (-Real.pi*t-2*v*I))

theorem sound {bt bv : DyadicBall} {t : ℝ} {v : ℂ} (cfg : BallConfig)
    (ht : (bt.toBall cfg.prec).Contains (t : ℂ))
    (hv : (bv.toBall cfg.prec).Contains v)
    (w : DyadicThetaFusedSeed) (hw : w.Valid cfg bt bv) : w.Contains cfg.prec t v := by
  have henv := threeDyadic_contains ht hv (DyadicBall.zero_contains cfg.prec)
  have hI : (⟨0,1⟩ : QComplex).val = I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := w.positive.sound cfg _ _ henv _ hw.1
    simpa only [thetaFusedSeedPositiveExpression, BallExpression.value, threeValues, hI] using h
  · have h := w.negative.sound cfg _ _ henv _ hw.2.1
    simpa only [thetaFusedSeedNegativeExpression, BallExpression.value, threeValues, hI] using h
  · have h := w.positiveRatio.sound cfg _ _ henv _ hw.2.2.1
    simpa only [thetaFusedRatioPositiveExpression, BallExpression.value,
      BallExpression.value_rational, Rat.cast_ofNat, threeValues, hI, neg_mul] using h
  · have h := w.negativeRatio.sound cfg _ _ henv _ hw.2.2.2
    simpa only [thetaFusedRatioNegativeExpression, BallExpression.value,
      BallExpression.value_sub, BallExpression.value_rational, Rat.cast_ofNat,
      threeValues, hI, neg_mul] using h

end DyadicThetaFusedSeed

structure DyadicThetaFusedTrace where
  loop : DyadicThetaFusedLoop
  output : DyadicBall
  deriving Repr

namespace DyadicThetaFusedTrace

def Valid (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall) (seed : DyadicThetaFusedSeed)
    (w : DyadicThetaFusedTrace) : Prop :=
  w.loop.length = N ∧
  w.loop.Valid cfg j bq seed.positive.output seed.negative.output
    seed.positiveRatio.output seed.negativeRatio.output ∧
  w.output.Coarsens ((w.loop.state seed.positive.output seed.negative.output
    seed.positiveRatio.output seed.negativeRatio.output).sum.inflate err)

instance (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall) (seed : DyadicThetaFusedSeed)
    (w : DyadicThetaFusedTrace) : Decidable (w.Valid cfg j N err bq seed) := by
  unfold Valid
  infer_instance

theorem sound {bq : DyadicBall} {t : ℝ} {v : ℂ} (cfg : BallConfig) (j N err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (seed : DyadicThetaFusedSeed) (hs : seed.Contains cfg.prec t v)
    (htail : ‖thetaJet t j v-thetaPartial t j N v‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ))
    (w : DyadicThetaFusedTrace) (hw : w.Valid cfg j N err bq seed) :
    (w.output.toBall cfg.prec).Contains (thetaJet t j v) := by
  have hp := (w.loop.sound cfg j hq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hw.2.1).1
  rw [hw.1] at hp
  exact DyadicBall.coarsen_contains (DyadicBall.inflate_contains hp htail) hw.2.2

end DyadicThetaFusedTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaFusedTrace.sound
