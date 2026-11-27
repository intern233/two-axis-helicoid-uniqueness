import TwoAxisHelicoid.RootDerivativeTrace

namespace TwoAxisHelicoid

structure RootDerivativeNode where
  point : DyadicBall
  function : RootDerivativeTrace
  weightedA : DyadicExpressionTrace
  weightedT : DyadicExpressionTrace

namespace RootDerivativeNode

def Valid (p : RootDerivativeParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RootDerivativeNode) : Prop :=
  (w.point.toBall rootDyadicConfig.prec).coarsens
    (ComplexBall.add (center.toBall rootDyadicConfig.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid p w.point ∧
  w.weightedA.Valid rootDyadicConfig (threeDyadic w.function.resultA.output .zero .zero)
    (.mul (.rational weight) (.input 0)) ∧
  w.weightedT.Valid rootDyadicConfig (threeDyadic w.function.resultT.output .zero .zero)
    (.mul (.rational weight) (.input 0))

instance (p : RootDerivativeParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RootDerivativeNode) : Decidable (w.Valid p center h node weight) := by
  unfold Valid; infer_instance

theorem sound (p : RootDerivativeParameters) {t a : ℝ} (hp : p.Encloses t a)
    (center : DyadicBall) {c : ℂ} (hcenter : (center.toBall rootDyadicConfig.prec).Contains c)
    (h node weight : ℚ) (w : RootDerivativeNode) (hw : w.Valid p center h node weight) :
    (w.weightedA.output.toBall rootDyadicConfig.prec).Contains
      ((weight : ℂ)*thetaAa t a (c+(h : ℂ)*(node : ℂ))) ∧
    (w.weightedT.output.toBall rootDyadicConfig.prec).Contains
      ((weight : ℂ)*thetaAtMidline t a (c+(h : ℂ)*(node : ℂ))) := by
  have hz := ComplexBall.coarsen_contains (ComplexBall.add_contains hcenter
    (ComplexBall.rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hf := w.function.sound p hp hz hw.2.1
  have hzero := DyadicBall.zero_contains rootDyadicConfig.prec
  have ha := w.weightedA.sound rootDyadicConfig _ _ (threeDyadic_contains hf.1 hzero hzero)
    _ hw.2.2.1
  have ht := w.weightedT.sound rootDyadicConfig _ _ (threeDyadic_contains hf.2.1 hzero hzero)
    _ hw.2.2.2
  constructor
  · simpa only [BallExpression.value, BallExpression.value_rational, threeValues] using ha
  · simpa only [BallExpression.value, BallExpression.value_rational, threeValues] using ht

end RootDerivativeNode
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDerivativeNode.sound
