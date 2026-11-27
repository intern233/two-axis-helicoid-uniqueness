import TwoAxisHelicoid.RangeDyadicParameters
import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaA thetaQuotient

structure RangeDerivativeParameters where
  base : RangeDyadicParameters
  thetaA1 : DyadicThetaTrace
  thetaA2 : DyadicThetaTrace
  thetaA3 : DyadicThetaTrace
  thetaA4 : DyadicThetaTrace
  thetaZero3 : DyadicThetaTrace
  ratioA : DyadicExpressionTrace
  ratioA2 : DyadicExpressionTrace
  ratioZero : DyadicExpressionTrace
  gt : DyadicExpressionTrace

namespace RangeDerivativeParameters

def Valid (s : RangeCertificateSetup) (tlo thi alo ahi : ℚ) (w : RangeDerivativeParameters) : Prop :=
  w.base.Valid s tlo thi alo ahi ∧
  w.thetaA1.Valid s.config 1 s.terms s.error w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA2.Valid s.config 2 s.terms s.error w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA3.Valid s.config 3 s.terms s.error w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA4.Valid s.config 4 s.terms s.error w.base.q.output w.base.coefficient.seedA ∧
  w.thetaZero3.Valid s.config 3 s.terms s.error w.base.q.output w.base.coefficient.seedZero ∧
  w.ratioA.Valid s.config (dyadicInputList [w.base.coefficient.thetaA.output,w.thetaA1.output]) quotientInputExpression ∧
  w.ratioA2.Valid s.config (dyadicInputList [w.base.coefficient.thetaA.output,w.thetaA2.output]) quotientInputExpression ∧
  w.ratioZero.Valid s.config (dyadicInputList [w.base.coefficient.thetaZero.output,w.thetaZero3.output]) quotientInputExpression ∧
  w.gt.Valid s.config (dyadicInputList [w.base.height,w.base.coefficient.thetaA.output,
    w.thetaA1.output,w.thetaA2.output,w.thetaA3.output,w.thetaA4.output]) thetaGtExpression ∧
  0 < w.base.coefficient.thetaZero.output.lower ∧
  0 < w.base.coefficient.thetaA.output.lower ∧
  1 ≤ (w.gt.output.toBall s.config.prec).center.re-(w.gt.output.toBall s.config.prec).radius

instance (s : RangeCertificateSetup) (tlo thi alo ahi : ℚ) (w : RangeDerivativeParameters) : Decidable (w.Valid s tlo thi alo ahi) := by unfold Valid; infer_instance

structure Encloses (s : RangeCertificateSetup) (w : RangeDerivativeParameters) (t a : ℝ) : Prop where
  height_lower : (s.lower : ℝ) ≤ t
  height : (w.base.height.toBall s.config.prec).Contains (t : ℂ)
  q : (w.base.q.output.toBall s.config.prec).Contains (Complex.exp (-Real.pi*t))
  abscissa : (w.base.abscissa.toBall s.config.prec).Contains (a : ℂ)
  coefficient : (w.base.coefficient.output.toBall s.config.prec).Contains (thetaACoefficient t a)
  ratioA : (w.ratioA.output.toBall s.config.prec).Contains (thetaQuotient t 1 (Real.pi*a/2))
  ratioA2 : (w.ratioA2.output.toBall s.config.prec).Contains (thetaQuotient t 2 (Real.pi*a/2))
  ratioZero : (w.ratioZero.output.toBall s.config.prec).Contains (thetaJet t 3 0/thetaJet t 1 0)
  zero_ne : thetaJet t 1 0 ≠ 0
  abscissa_ne : thetaJet t 0 (Real.pi*a/2) ≠ 0
  gt_lower : (1 : ℝ) ≤ (thetaGt t a).re

theorem sound (s : RangeCertificateSetup) (hs : s.Valid) {tlo thi alo ahi : ℚ}
    (w : RangeDerivativeParameters) (hw : w.Valid s tlo thi alo ahi) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) : w.Encloses s t a := by
  rcases hw with ⟨hbase,h1,h2,h3,h4,hz3,hr,hu,hc,hgt,hzn,han,hgtpos⟩
  rcases w.base.sound s hs hbase htl htu hal hau with ⟨ht,hq,ha,hcoeff⟩
  have hcv := hbase.2.2.2.2
  rcases hcv with ⟨harg,hy,hs0,hsa,hzero,ha0,_⟩
  have hz := DyadicBall.zero_contains s.config.prec
  have hv := w.base.coefficient.argument.sound s.config _ _ (threeDyadic_contains ha hz hz) _ harg
  rw [value_thetaArgumentExpression] at hv
  have hsz := w.base.coefficient.seedZero.sound s.config hz hs0
  have hsa' := w.base.coefficient.seedA.sound s.config hv hsa
  have hvy := DyadicBall.im_le_one hv hy
  have hz1 := w.base.coefficient.thetaZero.sound s.config 1 s.terms s.error hq _ hsz
    (s.tail_bound hs ht 1 0 (by norm_num)) hzero
  have ha0' := w.base.coefficient.thetaA.sound s.config 0 s.terms s.error hq _ hsa'
    (s.tail_bound hs ht 0 _ hvy) ha0
  have ha1 := w.thetaA1.sound s.config 1 s.terms s.error hq _ hsa'
    (s.tail_bound hs ht 1 _ hvy) h1
  have ha2 := w.thetaA2.sound s.config 2 s.terms s.error hq _ hsa'
    (s.tail_bound hs ht 2 _ hvy) h2
  have ha3 := w.thetaA3.sound s.config 3 s.terms s.error hq _ hsa'
    (s.tail_bound hs ht 3 _ hvy) h3
  have ha4 := w.thetaA4.sound s.config 4 s.terms s.error hq _ hsa'
    (s.tail_bound hs ht 4 _ hvy) h4
  have hz3' := w.thetaZero3.sound s.config 3 s.terms s.error hq _ hsz
    (s.tail_bound hs ht 3 0 (by norm_num)) hz3
  have hr' := w.ratioA.sound s.config _ _
    (dyadicInputList_contains (.cons ha0' (.cons ha1 .nil))) _ hr
  have hu' := w.ratioA2.sound s.config _ _
    (dyadicInputList_contains (.cons ha0' (.cons ha2 .nil))) _ hu
  have hc' := w.ratioZero.sound s.config _ _
    (dyadicInputList_contains (.cons hz1 (.cons hz3' .nil))) _ hc
  rw [value_quotientInputExpression] at hr' hu' hc'
  have hb := coarsen_contains (realInterval_contains htl htu) hbase.2.1
  have hgt' := w.gt.sound s.config _ _
    (dyadicInputList_contains (.cons hb (.cons ha0' (.cons ha1 (.cons ha2 (.cons ha3 (.cons ha4 .nil))))))) _ hgt
  rw [value_thetaGtExpression] at hgt'
  refine ⟨ht,hb,hq,ha,hcoeff,(by simpa only [thetaQuotient] using hr'),
    (by simpa only [thetaQuotient] using hu'),hc',
    ne_zero_of_lower_pos hz1 (DyadicBall.lower_pos_toBall hzn),
    ne_zero_of_lower_pos ha0' (DyadicBall.lower_pos_toBall han),?_⟩
  have hp : (1 : ℝ) ≤ (((w.gt.output.toBall s.config.prec).center.re-
      (w.gt.output.toBall s.config.prec).radius : ℚ) : ℝ) := by exact_mod_cast hgtpos
  exact hp.trans (by simpa using (re_bounds hgt').1)

end RangeDerivativeParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeParameters.sound
