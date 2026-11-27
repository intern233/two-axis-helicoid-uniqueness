import TwoAxisHelicoid.DyadicThetaATrace
import TwoAxisHelicoid.HorizontalRangeSetup
import TwoAxisHelicoid.ThetaAllWeierstrass
import TwoAxisHelicoid.ActualComplexHeight

namespace TwoAxisHelicoid
open Complex ComplexBall Set
attribute [local irreducible] thetaJet

/-- The vertical period equation eliminates the quasi-period from the
absolute height primitive. This formula needs only two theta jets. -/
theorem closed_vertical_height_formula {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) (z : ℂ) :
    actualComplexHeight t a 1 ht z= -I*((Real.pi/2:ℂ)*(thetaJet t 1 (Real.pi*z/2)/
      thetaJet t 0 (Real.pi*z/2))+((Real.pi/t:ℝ):ℂ)*z) := by
  have h := thetaG_eq_weierstrassP_of_pos ht ht a (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  rw [root] at h
  have e : thetaEtaExpression t+(rhombicPeriodPair t ht).weierstrassP a=((Real.pi/t:ℝ):ℂ) := by linear_combination -h
  have arg : (Real.pi/2:ℂ)*z=Real.pi*z/2 := by ring
  rw [actualComplexHeight,thetaZeta,← e]
  simp only [thetaScaledJet,pow_one,pow_zero,one_mul,arg,Complex.ofReal_one,mul_one]
  ring

def spatialHeightValueExpression : BallExpression :=
  .mul (.neg .imaginaryUnit) (.add (.mul (.mul .pi (.rational (1/2))) (.div (.input 3) (.input 2)))
    (.mul (.div .pi (.input 0)) (.input 1)))

structure SpatialHeightValueTrace where
  box : DyadicBall
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  theta0 : DyadicThetaTrace
  theta1 : DyadicThetaTrace
  height : DyadicExpressionTrace

namespace SpatialHeightValueTrace

def Valid (w : SpatialHeightValueTrace) (S : HorizontalRangeSetup) (bt bq : DyadicBall) : Prop :=
  w.argument.Valid S.config (threeDyadic w.box .zero .zero) thetaArgumentExpression ∧
  w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
  w.theta0.Valid S.config 0 S.terms S.error bq w.seed ∧ w.theta1.Valid S.config 1 S.terms S.error bq w.seed ∧
  0<w.theta0.output.lower ∧ w.height.Valid S.config (fiveDyadic bt w.box w.theta0.output w.theta1.output .zero) spatialHeightValueExpression

instance (w : SpatialHeightValueTrace) (S : HorizontalRangeSetup) (bt bq : DyadicBall) : Decidable (w.Valid S bt bq) := by
  unfold Valid
  infer_instance

theorem sound (w : SpatialHeightValueTrace) (S : HorizontalRangeSetup) (valid : S.Valid) {bt bq : DyadicBall}
    (check : w.Valid S bt bq) {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (root : thetaG t a=0)
    (lower : (S.lower:ℝ)≤t) (tval : (bt.toBall S.config.prec).Contains (t:ℂ))
    (qval : (bq.toBall S.config.prec).Contains (exp (-Real.pi*t))) {z : ℂ} (inside : (w.box.toBall S.config.prec).Contains z) :
    z∉(rhombicPeriodPair t ht).lattice ∧ (w.height.output.toBall S.config.prec).Contains (actualComplexHeight t a 1 ht z) := by
  obtain ⟨arg,yi,sd,t0,t1,lb,hx⟩ := check
  have hv := w.argument.sound S.config _ _ (threeDyadic_contains inside (DyadicBall.zero_contains _) (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at hv
  have hs := w.seed.sound S.config hv sd
  have im := DyadicBall.im_le_one hv yi
  have h0 := w.theta0.sound S.config 0 S.terms S.error qval w.seed hs (S.tail_bound_one valid lower 0 _ im) t0
  have h1 := w.theta1.sound S.config 1 S.terms S.error qval w.seed hs (S.tail_bound_one valid lower 1 _ im) t1
  have nz := ComplexBall.ne_zero_of_lower_pos h0 (DyadicBall.lower_pos_toBall lb)
  have ans := w.height.sound S.config _ _ (fiveDyadic_contains tval inside h0 h1 (DyadicBall.zero_contains _)) _ hx
  refine ⟨fun hz => nz ((thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mpr hz),?_⟩
  rw [closed_vertical_height_formula ht ha root]
  convert ans using 1
  simp [spatialHeightValueExpression,BallExpression.value,BallExpression.value_div,BallExpression.value_imaginaryUnit,fiveValues]
  ring_nf
  exact Or.inl True.intro

end SpatialHeightValueTrace
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.SpatialHeightValueTrace.sound
