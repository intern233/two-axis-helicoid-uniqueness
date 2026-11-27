import TwoAxisHelicoid.RootDyadicParameters
import TwoAxisHelicoid.RootDerivativeTail
import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaA thetaQuotient

structure RootDerivativeParameters where
  base : RootDyadicParameters
  thetaA1 : DyadicThetaTrace
  thetaA2 : DyadicThetaTrace
  thetaA3 : DyadicThetaTrace
  thetaA4 : DyadicThetaTrace
  thetaZero3 : DyadicThetaTrace
  ratioA : DyadicExpressionTrace
  ratioA2 : DyadicExpressionTrace
  ratioZero : DyadicExpressionTrace
  gt : DyadicExpressionTrace

namespace RootDerivativeParameters

def Valid (w : RootDerivativeParameters) : Prop :=
  w.base.Valid rootTLower rootTUpper rootALower rootAUpper ∧
  w.thetaA1.Valid rootDyadicConfig 1 8 4294967296 w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA2.Valid rootDyadicConfig 2 8 4294967296 w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA3.Valid rootDyadicConfig 3 8 4294967296 w.base.q.output w.base.coefficient.seedA ∧
  w.thetaA4.Valid rootDyadicConfig 4 8 4294967296 w.base.q.output w.base.coefficient.seedA ∧
  w.thetaZero3.Valid rootDyadicConfig 3 8 4294967296 w.base.q.output w.base.coefficient.seedZero ∧
  w.ratioA.Valid rootDyadicConfig (dyadicInputList [w.base.coefficient.thetaA.output,w.thetaA1.output]) quotientInputExpression ∧
  w.ratioA2.Valid rootDyadicConfig (dyadicInputList [w.base.coefficient.thetaA.output,w.thetaA2.output]) quotientInputExpression ∧
  w.ratioZero.Valid rootDyadicConfig (dyadicInputList [w.base.coefficient.thetaZero.output,w.thetaZero3.output]) quotientInputExpression ∧
  w.gt.Valid rootDyadicConfig (dyadicInputList [w.base.height,w.base.coefficient.thetaA.output,
    w.thetaA1.output,w.thetaA2.output,w.thetaA3.output,w.thetaA4.output]) thetaGtExpression ∧
  0 < w.base.coefficient.thetaZero.output.lower ∧
  0 < w.base.coefficient.thetaA.output.lower ∧
  1 ≤ (w.gt.output.toBall rootDyadicConfig.prec).center.re-(w.gt.output.toBall rootDyadicConfig.prec).radius

instance (w : RootDerivativeParameters) : Decidable w.Valid := by unfold Valid; infer_instance

structure Encloses (w : RootDerivativeParameters) (t a : ℝ) : Prop where
  height_lower : (86/100 : ℝ) ≤ t
  q : (w.base.q.output.toBall rootDyadicConfig.prec).Contains (Complex.exp (-Real.pi*t))
  abscissa : (w.base.abscissa.toBall rootDyadicConfig.prec).Contains (a : ℂ)
  coefficient : (w.base.coefficient.output.toBall rootDyadicConfig.prec).Contains (thetaACoefficient t a)
  ratioA : (w.ratioA.output.toBall rootDyadicConfig.prec).Contains (thetaQuotient t 1 (Real.pi*a/2))
  ratioA2 : (w.ratioA2.output.toBall rootDyadicConfig.prec).Contains (thetaQuotient t 2 (Real.pi*a/2))
  ratioZero : (w.ratioZero.output.toBall rootDyadicConfig.prec).Contains (thetaJet t 3 0/thetaJet t 1 0)
  zero_ne : thetaJet t 1 0 ≠ 0
  abscissa_ne : thetaJet t 0 (Real.pi*a/2) ≠ 0
  gt_lower : (1 : ℝ) ≤ (thetaGt t a).re

theorem sound (w : RootDerivativeParameters) (hw : w.Valid) {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) : w.Encloses t a := by
  rcases hw with ⟨hbase,h1,h2,h3,h4,hz3,hr,hu,hc,hgt,hzn,han,hgtpos⟩
  rcases w.base.sound hbase htl htu hal hau with ⟨ht,hq,ha,hcoeff⟩
  have hcv := hbase.2.2.2.2
  rcases hcv with ⟨harg,hy,hs0,hsa,hzero,ha0,_⟩
  have hz := DyadicBall.zero_contains rootDyadicConfig.prec
  have hv := w.base.coefficient.argument.sound rootDyadicConfig _ _ (threeDyadic_contains ha hz hz) _ harg
  rw [value_thetaArgumentExpression] at hv
  have hsz := w.base.coefficient.seedZero.sound rootDyadicConfig hz hs0
  have hsa' := w.base.coefficient.seedA.sound rootDyadicConfig hv hsa
  have hvy := DyadicBall.im_le_one hv hy
  have hz1 := w.base.coefficient.thetaZero.sound rootDyadicConfig 1 8 65536 hq _ hsz
    (root_dyadic_tail_one ht 0 (by norm_num)) hzero
  have ha0' := w.base.coefficient.thetaA.sound rootDyadicConfig 0 8 65536 hq _ hsa'
    (root_dyadic_tail_zero ht _ hvy) ha0
  have ha1 := w.thetaA1.sound rootDyadicConfig 1 8 4294967296 hq _ hsa'
    (root_derivative_tail_1 ht _ hvy) h1
  have ha2 := w.thetaA2.sound rootDyadicConfig 2 8 4294967296 hq _ hsa'
    (root_derivative_tail_2 ht _ hvy) h2
  have ha3 := w.thetaA3.sound rootDyadicConfig 3 8 4294967296 hq _ hsa'
    (root_derivative_tail_3 ht _ hvy) h3
  have ha4 := w.thetaA4.sound rootDyadicConfig 4 8 4294967296 hq _ hsa'
    (root_derivative_tail_4 ht _ hvy) h4
  have hz3' := w.thetaZero3.sound rootDyadicConfig 3 8 4294967296 hq _ hsz
    (root_derivative_tail_3 ht 0 (by norm_num)) hz3
  have hr' := w.ratioA.sound rootDyadicConfig _ _
    (dyadicInputList_contains (.cons ha0' (.cons ha1 .nil))) _ hr
  have hu' := w.ratioA2.sound rootDyadicConfig _ _
    (dyadicInputList_contains (.cons ha0' (.cons ha2 .nil))) _ hu
  have hc' := w.ratioZero.sound rootDyadicConfig _ _
    (dyadicInputList_contains (.cons hz1 (.cons hz3' .nil))) _ hc
  rw [value_quotientInputExpression] at hr' hu' hc'
  have hb := coarsen_contains (realInterval_contains htl htu) hbase.2.1
  have hgt' := w.gt.sound rootDyadicConfig _ _
    (dyadicInputList_contains (.cons hb (.cons ha0' (.cons ha1 (.cons ha2 (.cons ha3 (.cons ha4 .nil))))))) _ hgt
  rw [value_thetaGtExpression] at hgt'
  refine ⟨ht,hq,ha,hcoeff,(by simpa only [thetaQuotient] using hr'),
    (by simpa only [thetaQuotient] using hu'),hc',
    ne_zero_of_lower_pos hz1 (DyadicBall.lower_pos_toBall hzn),
    ne_zero_of_lower_pos ha0' (DyadicBall.lower_pos_toBall han),?_⟩
  have hp : (1 : ℝ) ≤ (((w.gt.output.toBall rootDyadicConfig.prec).center.re-
      (w.gt.output.toBall rootDyadicConfig.prec).radius : ℚ) : ℝ) := by exact_mod_cast hgtpos
  exact hp.trans (by simpa using (re_bounds hgt').1)

end RootDerivativeParameters
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDerivativeParameters.sound
