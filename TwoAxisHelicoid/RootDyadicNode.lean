import TwoAxisHelicoid.RootDyadicParameters

namespace TwoAxisHelicoid

structure RootDyadicNode where
  point : DyadicBall
  function : DyadicThetaATrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace RootDyadicNode

def output (w : RootDyadicNode) : DyadicBall := w.weighted.output

def Valid (p : RootDyadicParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RootDyadicNode) : Prop :=
  (w.point.toBall rootDyadicConfig.prec).coarsens
    (ComplexBall.add (center.toBall rootDyadicConfig.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid rootDyadicConfig 8 65536 p.q.output p.abscissa p.coefficient.output w.point ∧
  w.weighted.Valid rootDyadicConfig (threeDyadic w.function.output .zero .zero)
    (.mul (.rational weight) (.input 0))

instance (p : RootDyadicParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : RootDyadicNode) : Decidable (w.Valid p center h node weight) := by
  unfold Valid
  infer_instance

theorem sound {t a : ℝ} {c : ℂ} (p : RootDyadicParameters) (center : DyadicBall)
    (ht : 86/100 ≤ t)
    (hq : (p.q.output.toBall rootDyadicConfig.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (p.abscissa.toBall rootDyadicConfig.prec).Contains (a : ℂ))
    (hc : (p.coefficient.output.toBall rootDyadicConfig.prec).Contains (thetaACoefficient t a))
    (hcenter : (center.toBall rootDyadicConfig.prec).Contains c)
    (h node weight : ℚ) (w : RootDyadicNode) (hw : w.Valid p center h node weight) :
    (w.output.toBall rootDyadicConfig.prec).Contains
      ((weight : ℂ)*thetaA t a (c+(h : ℂ)*(node : ℂ))) := by
  have hz := ComplexBall.coarsen_contains (ComplexBall.add_contains hcenter
    (ComplexBall.rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hf := (w.function.sound rootDyadicConfig 8 65536 hq ha hc hz
    (root_dyadic_tail_zero ht) (root_dyadic_tail_one ht) hw.2.1).1
  have hzero := DyadicBall.zero_contains rootDyadicConfig.prec
  have hout := w.weighted.sound rootDyadicConfig _ _ (threeDyadic_contains hf hzero hzero)
    _ hw.2.2
  simpa only [output, BallExpression.value, BallExpression.value_rational, threeValues] using hout

end RootDyadicNode
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDyadicNode.sound
