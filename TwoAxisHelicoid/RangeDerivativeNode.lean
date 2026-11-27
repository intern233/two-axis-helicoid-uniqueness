import TwoAxisHelicoid.RangeDerivativeTrace

namespace TwoAxisHelicoid

structure RangeDerivativeNode where
  point : DyadicBall
  function : RangeDerivativeTrace
  weightedA : DyadicExpressionTrace
  weightedT : DyadicExpressionTrace

namespace RangeDerivativeNode

def Valid (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RangeDerivativeNode) : Prop :=
  (w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid s p w.point ∧
  w.weightedA.Valid s.config (threeDyadic w.function.resultA.output .zero .zero)
    (.mul (.rational weight) (.input 0)) ∧
  w.weightedT.Valid s.config (threeDyadic w.function.resultT.output .zero .zero)
    (.mul (.rational weight) (.input 0))

instance (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RangeDerivativeNode) : Decidable (w.Valid s p center h node weight) := by
  unfold Valid; infer_instance

theorem sound (s : RangeCertificateSetup) (hs : s.Valid) (p : RangeDerivativeParameters) {t a : ℝ} (hp : p.Encloses s t a)
    (center : DyadicBall) {c : ℂ} (hcenter : (center.toBall s.config.prec).Contains c)
    (h node weight : ℚ) (w : RangeDerivativeNode) (hw : w.Valid s p center h node weight) :
    (w.weightedA.output.toBall s.config.prec).Contains
      ((weight : ℂ)*thetaAa t a (c+(h : ℂ)*(node : ℂ))) ∧
    (w.weightedT.output.toBall s.config.prec).Contains
      ((weight : ℂ)*thetaAtMidline t a (c+(h : ℂ)*(node : ℂ))) := by
  have hz := ComplexBall.coarsen_contains (ComplexBall.add_contains hcenter
    (ComplexBall.rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hf := w.function.sound s hs p hp hz hw.2.1
  have hzero := DyadicBall.zero_contains s.config.prec
  have ha := w.weightedA.sound s.config _ _ (threeDyadic_contains hf.1 hzero hzero)
    _ hw.2.2.1
  have ht := w.weightedT.sound s.config _ _ (threeDyadic_contains hf.2.1 hzero hzero)
    _ hw.2.2.2
  constructor
  · simpa only [BallExpression.value, BallExpression.value_rational, threeValues] using ha
  · simpa only [BallExpression.value, BallExpression.value_rational, threeValues] using ht

end RangeDerivativeNode
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeNode.sound
