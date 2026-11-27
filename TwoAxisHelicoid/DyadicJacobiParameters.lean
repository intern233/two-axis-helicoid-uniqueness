import TwoAxisHelicoid.JacobiExpressionValues
import TwoAxisHelicoid.DyadicJacobiProduct

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiNormalization

structure DyadicJacobiBaseParameters where
  height : DyadicBall
  abscissa : DyadicBall
  q : DyadicExpressionTrace
  r : DyadicExpressionTrace
  kappa : DyadicExpressionTrace
  beta : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiBaseParameters

def inputs (p : DyadicJacobiBaseParameters) : List DyadicBall := [p.height,p.abscissa,.zero]

def Valid (cfg : BallConfig) (p : DyadicJacobiBaseParameters) : Prop :=
  p.q.Valid cfg (dyadicInputList p.inputs) jacobiDualNomeExpression ∧
  p.r.Valid cfg (dyadicInputList p.inputs) jacobiDualRExpression ∧
  p.kappa.Valid cfg (dyadicInputList p.inputs) jacobiDualKappaExpression ∧
  p.beta.Valid cfg (dyadicInputList p.inputs) jacobiDualBetaExpression

instance (cfg : BallConfig) (p : DyadicJacobiBaseParameters) : Decidable (p.Valid cfg) := by
  unfold Valid
  infer_instance

theorem sound (cfg : BallConfig) {t a : ℝ} (p : DyadicJacobiBaseParameters)
    (ht : (p.height.toBall cfg.prec).Contains (t : ℂ))
    (ha : (p.abscissa.toBall cfg.prec).Contains (a : ℂ)) (hp : p.Valid cfg) :
    (p.q.output.toBall cfg.prec).Contains (jacobiNome (1/t)) ∧
    (p.r.output.toBall cfg.prec).Contains (dualProductR t a : ℂ) ∧
    (p.kappa.output.toBall cfg.prec).Contains (dualProductKappa t a : ℂ) ∧
    (p.beta.output.toBall cfg.prec).Contains (Complex.exp (-(dualProductKappa t a : ℂ))) := by
  have he := dyadicInputList_contains (.cons ht (.cons ha (.cons (DyadicBall.zero_contains cfg.prec) .nil)))
  change ∀ i, ((dyadicInputList p.inputs i).toBall cfg.prec).Contains
    (complexInputList [(t : ℂ),(a : ℂ),0] i) at he
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [value_jacobiDualNomeExpression] using p.q.sound cfg _ _ he _ hp.1
  · simpa only [value_jacobiDualRExpression] using p.r.sound cfg _ _ he _ hp.2.1
  · simpa only [value_jacobiDualKappaExpression] using p.kappa.sound cfg _ _ he _ hp.2.2.1
  · simpa only [value_jacobiDualBetaExpression] using p.beta.sound cfg _ _ he _ hp.2.2.2

end DyadicJacobiBaseParameters

structure DyadicJacobiParameters where
  base : DyadicJacobiBaseParameters
  qr : DyadicBall
  p0 : DyadicJacobiProductTrace
  pr : DyadicJacobiProductTrace
  pinvr : DyadicJacobiProductTrace
  normalization : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiParameters

def inputs (p : DyadicJacobiParameters) : List DyadicBall :=
  [p.base.r.output,p.p0.output,p.pr.output,p.pinvr.output]

def Valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiParameters) : Prop :=
  p.base.Valid cfg ∧ DyadicBall.ChecksMul cfg.prec p.qr p.base.q.output p.base.r.output ∧
  p.p0.Valid cfg.prec err p.base.q.output p.base.q.output ∧
  p.pr.Valid cfg.prec err p.base.q.output p.qr ∧
  p.pinvr.Valid cfg.prec err p.base.q.output p.base.beta.output.neg ∧
  p.normalization.Valid cfg (dyadicInputList p.inputs) jacobiNormalizationExpression

instance (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiParameters) : Decidable (p.Valid cfg err) := by
  unfold Valid
  infer_instance

theorem sound (cfg : BallConfig) (err : ℕ) {t a : ℝ} (p : DyadicJacobiParameters)
    (ht : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (ha : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ)) (hp : p.Valid cfg err) :
    (p.base.q.output.toBall cfg.prec).Contains (jacobiNome (1/t)) ∧
    (p.base.kappa.output.toBall cfg.prec).Contains (dualProductKappa t a : ℂ) ∧
    (p.normalization.output.toBall cfg.prec).Contains
      (jacobiNormalization (jacobiNome (1/t)) (dualProductR t a)) := by
  rcases hp with ⟨hbase, hqr, hp0, hpr, hpinv, hn⟩
  rcases p.base.sound cfg ht ha hbase with ⟨hq, hr, hk, hb⟩
  have hqr' := DyadicBall.mul_contains hq hr hqr
  have hqinv := DyadicBall.neg_contains hb
  rw [← dual_q_div_r, div_eq_mul_inv] at hqinv
  have h0 := p.p0.sound (x := 1) cfg.prec err hq (by simpa only [mul_one] using hq) hp0
  have h1 := p.pr.sound cfg.prec err hq hqr' hpr
  have h2 := p.pinvr.sound cfg.prec err hq hqinv hpinv
  have he := dyadicInputList_contains (.cons hr (.cons h0 (.cons h1 (.cons h2 .nil))))
  have hout := p.normalization.sound cfg _ _ he _ hn
  rw [value_jacobiNormalizationExpression] at hout
  exact ⟨hq, hk, hout⟩

end DyadicJacobiParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiParameters.sound
