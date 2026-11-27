import TwoAxisHelicoid.RangeDerivativeParameters

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaQuotient

def rangeVerticalExpression : BallExpression :=
  .sub (.mul (.mul (.pow .pi 2) (.rational (1/4)))
    (.sub (.pow (.input 1) 2) (.input 2))) (.div .pi (.input 0))

theorem value_rangeVerticalExpression (t a : ℝ) :
    rangeVerticalExpression.value (threeValues (t : ℂ)
      (thetaQuotient t 1 (Real.pi*a/2)) (thetaQuotient t 2 (Real.pi*a/2))) =
        thetaG t a := by
  simp only [rangeVerticalExpression, BallExpression.value, BallExpression.value_pow,
    BallExpression.value_sub, BallExpression.value_div, BallExpression.value_rational,
    threeValues, thetaG]
  push_cast
  ring

namespace RangeDerivativeParameters

def VerticalValid (s : RangeCertificateSetup) (p : RangeDerivativeParameters)
    (w : DyadicExpressionTrace) : Prop :=
  w.Valid s.config (threeDyadic p.base.height p.ratioA.output p.ratioA2.output)
    rangeVerticalExpression

instance (s : RangeCertificateSetup) (p : RangeDerivativeParameters)
    (w : DyadicExpressionTrace) : Decidable (p.VerticalValid s w) := by
  unfold VerticalValid
  infer_instance

theorem vertical_sound (s : RangeCertificateSetup) (p : RangeDerivativeParameters)
    {t a : ℝ} (hp : p.Encloses s t a) (w : DyadicExpressionTrace)
    (hw : p.VerticalValid s w) :
    (w.output.toBall s.config.prec).Contains (thetaG t a) := by
  have h := w.sound s.config _ _
    (threeDyadic_contains hp.height hp.ratioA hp.ratioA2) _ hw
  rw [value_rangeVerticalExpression] at h
  exact h

end RangeDerivativeParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeParameters.vertical_sound
