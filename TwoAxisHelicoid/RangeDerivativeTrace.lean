import TwoAxisHelicoid.RangeDerivativeParameters

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaA thetaQuotient

structure RangeDerivativeTrace where
  base : DyadicThetaATrace
  thetaZ2 : DyadicThetaTrace
  thetaZ3 : DyadicThetaTrace
  thetaM1 : DyadicThetaTrace
  thetaM2 : DyadicThetaTrace
  resultA : DyadicExpressionTrace
  resultT : DyadicExpressionTrace

namespace RangeDerivativeTrace

def inputs (p : RangeDerivativeParameters) (w : RangeDerivativeTrace) : List DyadicBall :=
  [p.base.abscissa,w.base.output,w.base.theta0.output,w.base.theta1.output,w.thetaZ2.output,
    w.thetaZ3.output,w.base.thetaShifted.output,w.thetaM1.output,w.thetaM2.output,
    p.ratioA.output,p.ratioA2.output,p.ratioZero.output]

def Valid (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (z : DyadicBall) (w : RangeDerivativeTrace) : Prop :=
  w.base.Valid s.config s.terms s.error p.base.q.output p.base.abscissa p.base.coefficient.output z ∧
  w.thetaZ2.Valid s.config 2 s.terms s.error p.base.q.output w.base.seed ∧
  w.thetaZ3.Valid s.config 3 s.terms s.error p.base.q.output w.base.seed ∧
  w.thetaM1.Valid s.config 1 s.terms s.error p.base.q.output w.base.shiftedSeed ∧
  w.thetaM2.Valid s.config 2 s.terms s.error p.base.q.output w.base.shiftedSeed ∧
  0 < w.base.thetaShifted.output.lower ∧
  w.resultA.Valid s.config (dyadicInputList (w.inputs p)) derivativeAaExpression ∧
  w.resultT.Valid s.config (dyadicInputList (w.inputs p)) derivativeAtExpression

instance (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (z : DyadicBall) (w : RangeDerivativeTrace) : Decidable (w.Valid s p z) := by
  unfold Valid; infer_instance

theorem sound (s : RangeCertificateSetup) (hs : s.Valid) (p : RangeDerivativeParameters) {t a : ℝ} (hp : p.Encloses s t a)
    {bz : DyadicBall} {z : ℂ} (hz : (bz.toBall s.config.prec).Contains z)
    (w : RangeDerivativeTrace) (hw : w.Valid s p bz) :
    (w.resultA.output.toBall s.config.prec).Contains (thetaAa t a z) ∧
    (w.resultT.output.toBall s.config.prec).Contains (thetaAtMidline t a z) ∧
    z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t := by
  rcases hw with ⟨hb,hz2,hz3,hm1,hm2,hmn,hra,hrt⟩
  have hA := w.base.sound s.config s.terms s.error hp.q hp.abscissa hp.coefficient hz
    (s.tail_bound hs hp.height_lower 0) (s.tail_bound hs hp.height_lower 1) hb
  rcases hb with ⟨hav,ham,hyv,hym,hsv,hsm,ht0,ht1,htm,_,_⟩
  have he := threeDyadic_contains hz hp.abscissa (DyadicBall.zero_contains s.config.prec)
  have hv := w.base.argument.sound s.config _ _ he _ hav
  have hm := w.base.shiftedArgument.sound s.config _ _ he _ ham
  rw [value_thetaArgumentExpression] at hv
  rw [value_thetaShiftedArgumentExpression] at hm
  have hvs := w.base.seed.sound s.config hv hsv
  have hms := w.base.shiftedSeed.sound s.config hm hsm
  have hvy := DyadicBall.im_le_one hv hyv
  have hmy := DyadicBall.im_le_one hm hym
  have h0 := w.base.theta0.sound s.config 0 s.terms s.error hp.q _ hvs
    (s.tail_bound hs hp.height_lower 0 _ hvy) ht0
  have h1 := w.base.theta1.sound s.config 1 s.terms s.error hp.q _ hvs
    (s.tail_bound hs hp.height_lower 1 _ hvy) ht1
  have hm0 := w.base.thetaShifted.sound s.config 0 s.terms s.error hp.q _ hms
    (s.tail_bound hs hp.height_lower 0 _ hmy) htm
  have h2 := w.thetaZ2.sound s.config 2 s.terms s.error hp.q _ hvs
    (s.tail_bound hs hp.height_lower 2 _ hvy) hz2
  have h3 := w.thetaZ3.sound s.config 3 s.terms s.error hp.q _ hvs
    (s.tail_bound hs hp.height_lower 3 _ hvy) hz3
  have hm1' := w.thetaM1.sound s.config 1 s.terms s.error hp.q _ hms
    (s.tail_bound hs hp.height_lower 1 _ hmy) hm1
  have hm2' := w.thetaM2.sound s.config 2 s.terms s.error hp.q _ hms
    (s.tail_bound hs hp.height_lower 2 _ hmy) hm2
  have hi : ∀ i, ((dyadicInputList (w.inputs p) i).toBall s.config.prec).Contains
      (complexInputList (derivativeValues t a z) i) :=
    dyadicInputList_contains (.cons hp.abscissa (.cons hA.1 (.cons h0 (.cons h1 (.cons h2
      (.cons h3 (.cons hm0 (.cons hm1' (.cons hm2' (.cons hp.ratioA (.cons hp.ratioA2
        (.cons hp.ratioZero .nil))))))))))))
  have haout := w.resultA.sound s.config _ _ hi _ hra
  have htout := w.resultT.sound s.config _ _ hi _ hrt
  rw [value_derivativeAaExpression] at haout
  rw [value_derivativeAtExpression] at htout
  exact ⟨haout,htout,hA.2,ne_zero_of_lower_pos hm0 (DyadicBall.lower_pos_toBall hmn)⟩

end RangeDerivativeTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeTrace.sound
