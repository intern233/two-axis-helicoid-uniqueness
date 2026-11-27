import TwoAxisHelicoid.RootDyadicBounds
import TwoAxisHelicoid.DyadicCoefficientTrace
import TwoAxisHelicoid.RootEndpointConstants

namespace TwoAxisHelicoid

def thetaQExpression : BallExpression := .exp (.neg (.mul .pi (.input 0)))

structure RootDyadicParameters where
  height : DyadicBall
  abscissa : DyadicBall
  q : DyadicExpressionTrace
  coefficient : DyadicCoefficientTrace
  deriving Repr

namespace RootDyadicParameters

def Valid (tlo thi alo ahi : ℚ) (w : RootDyadicParameters) : Prop :=
  86/100 ≤ tlo ∧
  (w.height.toBall rootDyadicConfig.prec).coarsens (ComplexBall.realInterval tlo thi) ∧
  (w.abscissa.toBall rootDyadicConfig.prec).coarsens (ComplexBall.realInterval alo ahi) ∧
  w.q.Valid rootDyadicConfig (threeDyadic w.height .zero .zero) thetaQExpression ∧
  w.coefficient.Valid rootDyadicConfig 8 65536 w.q.output w.abscissa

instance (tlo thi alo ahi : ℚ) (w : RootDyadicParameters) :
    Decidable (w.Valid tlo thi alo ahi) := by unfold Valid; infer_instance

theorem sound {tlo thi alo ahi : ℚ} {t a : ℝ}
    (w : RootDyadicParameters) (hw : w.Valid tlo thi alo ahi)
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (86/100 : ℝ) ≤ t ∧
    (w.q.output.toBall rootDyadicConfig.prec).Contains (Complex.exp (-Real.pi*t)) ∧
    (w.abscissa.toBall rootDyadicConfig.prec).Contains (a : ℂ) ∧
    (w.coefficient.output.toBall rootDyadicConfig.prec).Contains (thetaACoefficient t a) := by
  rcases hw with ⟨htmin, hbt, hba, hq, hcoeff⟩
  have htmin' : (86/100 : ℝ) ≤ (tlo : ℝ) := by
    have hh : (((86/100 : ℚ) : ℝ)) ≤ (tlo : ℝ) := Rat.cast_le.mpr htmin
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have ht : (86/100 : ℝ) ≤ t := htmin'.trans htl
  have hb := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains htl htu) hbt
  have ha := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains hal hau) hba
  have hz := DyadicBall.zero_contains rootDyadicConfig.prec
  have hq' := w.q.sound rootDyadicConfig _ _ (threeDyadic_contains hb hz hz) _ hq
  have hq'' : (w.q.output.toBall rootDyadicConfig.prec).Contains (Complex.exp (-Real.pi*t)) := by
    simpa only [thetaQExpression, BallExpression.value, threeValues, neg_mul] using hq'
  exact ⟨ht, hq'', ha, w.coefficient.sound rootDyadicConfig 8 65536 hq'' ha
    (root_dyadic_tail_zero ht) (root_dyadic_tail_one ht) hcoeff⟩

end RootDyadicParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDyadicParameters.sound
