import TwoAxisHelicoid.DyadicThetaATrace
import TwoAxisHelicoid.HorizontalRangeSetup
import TwoAxisHelicoid.ThetaAllWeierstrass
import TwoAxisHelicoid.WeierstrassCoordinateData
import TwoAxisHelicoid.CertifiedSpatialDiskMargins

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaA thetaJet

def spatialHeightExpression : BallExpression :=
  .mul .imaginaryUnit (.sub (.mul (.mul (.pow .pi 2) (.rational (1/4)))
    (.sub (.pow (.div (.input 2) (.input 1)) 2) (.div (.input 3) (.input 1)))) (.div .pi (.input 0)))

def spatialFormExpression : Fin 3 → BallExpression :=
  ![.mul (.rational (-1/2)) (.add (.input 1) (.input 0)),
    .mul (.mul .imaginaryUnit (.rational (1/2))) (.sub (.input 0) (.input 1)),.input 2]

/-- A dyadic trace of the same three coordinate forms used by the
immersed surface. The argument, theta values and coefficient are shared
by the horizontal and height computations. -/
structure SpatialWeierstrassTrace where
  argument : DyadicBall
  positive : DyadicThetaATrace
  negative : DyadicThetaATrace
  second : DyadicThetaTrace
  height : DyadicExpressionTrace
  spatial : Fin 3 → DyadicExpressionTrace

namespace SpatialWeierstrassTrace

def Valid (w : SpatialWeierstrassTrace) (S : HorizontalRangeSetup) (bt bq ba bc : DyadicBall) : Prop :=
  w.positive.Valid S.config S.terms S.error bq ba bc w.argument ∧
  w.negative.Valid S.config S.terms S.error bq ba bc w.argument.neg ∧
  w.second.Valid S.config 2 S.terms S.error bq w.positive.seed ∧
  w.height.Valid S.config (fiveDyadic bt w.positive.theta0.output w.positive.theta1.output w.second.output .zero) spatialHeightExpression ∧
  ∀ j, (w.spatial j).Valid S.config (threeDyadic w.positive.output w.negative.output w.height.output) (spatialFormExpression j)

instance (w : SpatialWeierstrassTrace) (S : HorizontalRangeSetup) (bt bq ba bc : DyadicBall) :
    Decidable (w.Valid S bt bq ba bc) := by unfold Valid; infer_instance

theorem sound (w : SpatialWeierstrassTrace) (S : HorizontalRangeSetup) (svalid : S.Valid)
    {bt bq ba bc : DyadicBall} (check : w.Valid S bt bq ba bc) {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) (lower : (S.lower:ℝ)≤t)
    (tail : ∀ v : ℂ, |v.im|≤1 → ‖thetaJet t 2 v-thetaPartial t 2 S.terms v‖≤(S.error:ℝ)/(DyadicBall.denominator S.config.prec:ℝ))
    (tval : (bt.toBall S.config.prec).Contains (t:ℂ)) (qval : (bq.toBall S.config.prec).Contains (exp (-Real.pi*t)))
    (aval : (ba.toBall S.config.prec).Contains (a:ℂ)) (cval : (bc.toBall S.config.prec).Contains (thetaACoefficient t a))
    {z : ℂ} (inside : (w.argument.toBall S.config.prec).Contains z) :
    z∉(rhombicPeriodPair t ht).lattice ∧ ∀ j, ((w.spatial j).output.toBall S.config.prec).Contains (coordinateData t a 1 ht z j) := by
  obtain ⟨p,m,hh,hw,all⟩ := check
  have pval := w.positive.sound S.config S.terms S.error qval aval cval inside
    (S.tail_bound_one svalid lower 0) (S.tail_bound_one svalid lower 1) p
  have mval := w.negative.sound S.config S.terms S.error qval aval cval (DyadicBall.neg_contains inside)
    (S.tail_bound_one svalid lower 0) (S.tail_bound_one svalid lower 1) m
  have off : z∉(rhombicPeriodPair t ht).lattice := fun h => pval.2 ((thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mpr h)
  obtain ⟨arg,_,yi,_,seed,_,d0,d1,_⟩ := p
  have av := w.positive.argument.sound S.config _ _ (threeDyadic_contains inside aval (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at av
  have sem := w.positive.seed.sound S.config av seed
  have im := DyadicBall.im_le_one av yi
  have h0 := w.positive.theta0.sound S.config 0 S.terms S.error qval w.positive.seed sem (S.tail_bound_one svalid lower 0 _ im) d0
  have h1 := w.positive.theta1.sound S.config 1 S.terms S.error qval w.positive.seed sem (S.tail_bound_one svalid lower 1 _ im) d1
  have h2 := w.second.sound S.config 2 S.terms S.error qval w.positive.seed sem (tail _ im) hh
  have hH := w.height.sound S.config _ _ (fiveDyadic_contains tval h0 h1 h2 (DyadicBall.zero_contains _)) _ hw
  have aH : spatialHeightExpression.value (fiveValues t (thetaJet t 0 (Real.pi*z/2)) (thetaJet t 1 (Real.pi*z/2)) (thetaJet t 2 (Real.pi*z/2)) 0)=
      I*(thetaLogSecond t z-(Real.pi/t:ℝ)) := by
    simp [spatialHeightExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,BallExpression.value_sub,
      BallExpression.value_imaginaryUnit,thetaLogSecond,thetaQuotient,fiveValues]
    ring_nf
    exact Or.inl True.intro
  rw [aH] at hH
  have hP := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht off
  have hA := thetaG_eq_weierstrassP_of_pos ht ht a (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  rw [root] at hA
  have eq : thetaLogSecond t z-(Real.pi/t:ℝ)=(rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a := by linear_combination hP-hA
  rw [eq] at hH
  refine ⟨off,?_⟩
  intro j
  have h := (w.spatial j).sound S.config _ _ (threeDyadic_contains pval.1 mval.1 hH) _ (all j)
  convert h using 1
  fin_cases j <;> simp [coordinateData,spatialFormExpression,BallExpression.value,BallExpression.value_sub,BallExpression.value_imaginaryUnit,threeValues]
  ring_nf
  exact Or.inl True.intro

end SpatialWeierstrassTrace
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.SpatialWeierstrassTrace.sound
