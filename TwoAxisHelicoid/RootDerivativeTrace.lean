import TwoAxisHelicoid.RootDerivativeParameters

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaA thetaQuotient

structure RootDerivativeTrace where
  base : DyadicThetaATrace
  thetaZ2 : DyadicThetaTrace
  thetaZ3 : DyadicThetaTrace
  thetaM1 : DyadicThetaTrace
  thetaM2 : DyadicThetaTrace
  resultA : DyadicExpressionTrace
  resultT : DyadicExpressionTrace

namespace RootDerivativeTrace

def inputs (p : RootDerivativeParameters) (w : RootDerivativeTrace) : List DyadicBall :=
  [p.base.abscissa,w.base.output,w.base.theta0.output,w.base.theta1.output,w.thetaZ2.output,
    w.thetaZ3.output,w.base.thetaShifted.output,w.thetaM1.output,w.thetaM2.output,
    p.ratioA.output,p.ratioA2.output,p.ratioZero.output]

def Valid (p : RootDerivativeParameters) (z : DyadicBall) (w : RootDerivativeTrace) : Prop :=
  w.base.Valid rootDyadicConfig 8 65536 p.base.q.output p.base.abscissa p.base.coefficient.output z ∧
  w.thetaZ2.Valid rootDyadicConfig 2 8 4294967296 p.base.q.output w.base.seed ∧
  w.thetaZ3.Valid rootDyadicConfig 3 8 4294967296 p.base.q.output w.base.seed ∧
  w.thetaM1.Valid rootDyadicConfig 1 8 4294967296 p.base.q.output w.base.shiftedSeed ∧
  w.thetaM2.Valid rootDyadicConfig 2 8 4294967296 p.base.q.output w.base.shiftedSeed ∧
  0 < w.base.thetaShifted.output.lower ∧
  w.resultA.Valid rootDyadicConfig (dyadicInputList (w.inputs p)) derivativeAaExpression ∧
  w.resultT.Valid rootDyadicConfig (dyadicInputList (w.inputs p)) derivativeAtExpression

instance (p : RootDerivativeParameters) (z : DyadicBall) (w : RootDerivativeTrace) : Decidable (w.Valid p z) := by
  unfold Valid; infer_instance

theorem sound (p : RootDerivativeParameters) {t a : ℝ} (hp : p.Encloses t a)
    {bz : DyadicBall} {z : ℂ} (hz : (bz.toBall rootDyadicConfig.prec).Contains z)
    (w : RootDerivativeTrace) (hw : w.Valid p bz) :
    (w.resultA.output.toBall rootDyadicConfig.prec).Contains (thetaAa t a z) ∧
    (w.resultT.output.toBall rootDyadicConfig.prec).Contains (thetaAtMidline t a z) ∧
    z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t := by
  rcases hw with ⟨hb,hz2,hz3,hm1,hm2,hmn,hra,hrt⟩
  have hA := w.base.sound rootDyadicConfig 8 65536 hp.q hp.abscissa hp.coefficient hz
    (root_dyadic_tail_zero hp.height_lower) (root_dyadic_tail_one hp.height_lower) hb
  rcases hb with ⟨hav,ham,hyv,hym,hsv,hsm,ht0,ht1,htm,_,_⟩
  have he := threeDyadic_contains hz hp.abscissa (DyadicBall.zero_contains rootDyadicConfig.prec)
  have hv := w.base.argument.sound rootDyadicConfig _ _ he _ hav
  have hm := w.base.shiftedArgument.sound rootDyadicConfig _ _ he _ ham
  rw [value_thetaArgumentExpression] at hv
  rw [value_thetaShiftedArgumentExpression] at hm
  have hvs := w.base.seed.sound rootDyadicConfig hv hsv
  have hms := w.base.shiftedSeed.sound rootDyadicConfig hm hsm
  have hvy := DyadicBall.im_le_one hv hyv
  have hmy := DyadicBall.im_le_one hm hym
  have h0 := w.base.theta0.sound rootDyadicConfig 0 8 65536 hp.q _ hvs
    (root_dyadic_tail_zero hp.height_lower _ hvy) ht0
  have h1 := w.base.theta1.sound rootDyadicConfig 1 8 65536 hp.q _ hvs
    (root_dyadic_tail_one hp.height_lower _ hvy) ht1
  have hm0 := w.base.thetaShifted.sound rootDyadicConfig 0 8 65536 hp.q _ hms
    (root_dyadic_tail_zero hp.height_lower _ hmy) htm
  have h2 := w.thetaZ2.sound rootDyadicConfig 2 8 4294967296 hp.q _ hvs
    (root_derivative_tail_2 hp.height_lower _ hvy) hz2
  have h3 := w.thetaZ3.sound rootDyadicConfig 3 8 4294967296 hp.q _ hvs
    (root_derivative_tail_3 hp.height_lower _ hvy) hz3
  have hm1' := w.thetaM1.sound rootDyadicConfig 1 8 4294967296 hp.q _ hms
    (root_derivative_tail_1 hp.height_lower _ hmy) hm1
  have hm2' := w.thetaM2.sound rootDyadicConfig 2 8 4294967296 hp.q _ hms
    (root_derivative_tail_2 hp.height_lower _ hmy) hm2
  have hi : ∀ i, ((dyadicInputList (w.inputs p) i).toBall rootDyadicConfig.prec).Contains
      (complexInputList (derivativeValues t a z) i) :=
    dyadicInputList_contains (.cons hp.abscissa (.cons hA.1 (.cons h0 (.cons h1 (.cons h2
      (.cons h3 (.cons hm0 (.cons hm1' (.cons hm2' (.cons hp.ratioA (.cons hp.ratioA2
        (.cons hp.ratioZero .nil))))))))))))
  have haout := w.resultA.sound rootDyadicConfig _ _ hi _ hra
  have htout := w.resultT.sound rootDyadicConfig _ _ hi _ hrt
  rw [value_derivativeAaExpression] at haout
  rw [value_derivativeAtExpression] at htout
  exact ⟨haout,htout,hA.2,ne_zero_of_lower_pos hm0 (DyadicBall.lower_pos_toBall hmn)⟩

end RootDerivativeTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDerivativeTrace.sound
