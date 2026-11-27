import TwoAxisHelicoid.RangeCertificateSetup
import TwoAxisHelicoid.RootDyadicParameters

namespace TwoAxisHelicoid

structure RangeDyadicParameters where
  height : DyadicBall
  abscissa : DyadicBall
  q : DyadicExpressionTrace
  coefficient : DyadicCoefficientTrace
  deriving Repr

namespace RangeDyadicParameters

def Valid (s : RangeCertificateSetup) (tlo thi alo ahi : ℚ) (w : RangeDyadicParameters) : Prop :=
  s.lower ≤ tlo ∧
  (w.height.toBall s.config.prec).coarsens (ComplexBall.realInterval tlo thi) ∧
  (w.abscissa.toBall s.config.prec).coarsens (ComplexBall.realInterval alo ahi) ∧
  w.q.Valid s.config (threeDyadic w.height .zero .zero) thetaQExpression ∧
  w.coefficient.Valid s.config s.terms s.error w.q.output w.abscissa

instance (s : RangeCertificateSetup) (tlo thi alo ahi : ℚ) (w : RangeDyadicParameters) :
    Decidable (w.Valid s tlo thi alo ahi) := by unfold Valid; infer_instance

theorem sound (s : RangeCertificateSetup) (hs : s.Valid) {tlo thi alo ahi : ℚ} {t a : ℝ}
    (w : RangeDyadicParameters) (hw : w.Valid s tlo thi alo ahi)
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (s.lower : ℝ) ≤ t ∧
    (w.q.output.toBall s.config.prec).Contains (Complex.exp (-Real.pi*t)) ∧
    (w.abscissa.toBall s.config.prec).Contains (a : ℂ) ∧
    (w.coefficient.output.toBall s.config.prec).Contains (thetaACoefficient t a) := by
  rcases hw with ⟨htmin, hbt, hba, hq, hcoeff⟩
  have htmin' : (s.lower : ℝ) ≤ (tlo : ℝ) := by
    exact_mod_cast htmin
  have ht : (s.lower : ℝ) ≤ t := htmin'.trans htl
  have hb := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains htl htu) hbt
  have ha := ComplexBall.coarsen_contains (ComplexBall.realInterval_contains hal hau) hba
  have hz := DyadicBall.zero_contains s.config.prec
  have hq' := w.q.sound s.config _ _ (threeDyadic_contains hb hz hz) _ hq
  have hq'' : (w.q.output.toBall s.config.prec).Contains (Complex.exp (-Real.pi*t)) := by
    simpa only [thetaQExpression, BallExpression.value, threeValues, neg_mul] using hq'
  exact ⟨ht, hq'', ha, w.coefficient.sound s.config s.terms s.error hq'' ha
    (s.tail_bound hs ht 0) (s.tail_bound hs ht 1) hcoeff⟩

end RangeDyadicParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDyadicParameters.sound
