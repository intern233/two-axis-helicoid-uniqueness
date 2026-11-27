import TwoAxisHelicoid.DyadicJacobiParameters
import TwoAxisHelicoid.DyadicJacobiSecond
import TwoAxisHelicoid.LeftProductError

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiRealE jacobiGeometricSeries verticalA thetaG
attribute [local simp] neg_div

def jacobiSmallNomeExpression (u : ℚ) : BallExpression :=
  .exp (.neg (.div .pi (.mul (.rational 2) (.rational u))))

theorem value_jacobiSmallNomeExpression (u : ℚ) :
    (jacobiSmallNomeExpression u).value (complexInputList []) = (leftNome (u : ℝ) : ℂ) := by
  simp [jacobiSmallNomeExpression, BallExpression.value, leftNome]

theorem leftNome_mono {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) : leftNome t ≤ leftNome u := by
  have hu0 := ht.trans_le htu
  apply Real.exp_le_exp.mpr
  change -Real.pi/(2*t) ≤ -Real.pi/(2*u)
  apply (div_le_div_iff₀ (by positivity : 0 < 2*t) (by positivity : 0 < 2*u)).mpr
  nlinarith [Real.pi_pos]

theorem verticalA_small_rectangle_upper {t u q : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hu : u ≤ 1/4) (hq : leftNome u ≤ q) : verticalA t ≤ 1/2+2*u*q := by
  have ha := verticalA_sharp_small_upper ht (htu.trans hu)
  have hq' := (leftNome_mono ht htu).trans hq
  have hm := mul_le_mul htu hq' (leftNome_pos t).le (ht.le.trans htu)
  nlinarith

theorem jacobiSmallNome_upper (cfg : BallConfig) (u q : ℚ) (w : DyadicExpressionTrace)
    (hw : w.Valid cfg (dyadicInputList []) (jacobiSmallNomeExpression u))
    (hq : (w.output.toBall cfg.prec).center.re+(w.output.toBall cfg.prec).radius ≤ q) :
    leftNome (u : ℝ) ≤ (q : ℝ) := by
  have h := w.sound cfg _ _ (dyadicInputList_contains (List.Forall₂.nil)) _ hw
  rw [value_jacobiSmallNomeExpression] at h
  have h' : leftNome (u : ℝ) ≤
      ((w.output.toBall cfg.prec).center.re+(w.output.toBall cfg.prec).radius : ℚ) := by
    simpa only [Complex.ofReal_re, Rat.cast_add] using (ComplexBall.re_bounds h).2
  exact h'.trans (Rat.cast_le.mpr hq)

theorem dual_q_div_r_real (t a : ℝ) :
    (-Real.exp (-Real.pi/t))/dualProductR t a = -Real.exp (-dualProductKappa t a) := by
  unfold dualProductR dualProductKappa
  rw [neg_div, ← Real.exp_sub]
  congr 2
  ring

structure DyadicJacobiVerticalTrace where
  first : DyadicJacobiSecondTrace
  second : DyadicJacobiSecondTrace
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiVerticalTrace

def Valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiBaseParameters)
    (w : DyadicJacobiVerticalTrace) : Prop :=
  w.first.Valid cfg err p.q.output p.r.output ∧
  w.second.Valid cfg err p.q.output p.beta.output.neg ∧
  DyadicBall.ChecksAdd w.output w.first.output w.second.output

instance (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiBaseParameters)
    (w : DyadicJacobiVerticalTrace) : Decidable (w.Valid cfg err p) := by
  unfold Valid
  infer_instance

theorem sound (cfg : BallConfig) (err : ℕ) {t a : ℝ} (p : DyadicJacobiBaseParameters)
    (hp : p.Valid cfg) (ht : (p.height.toBall cfg.prec).Contains (t : ℂ))
    (ha : (p.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : DyadicJacobiVerticalTrace) (hw : w.Valid cfg err p) :
    (w.output.toBall cfg.prec).Contains
      (jacobiRealE (-Real.exp (-Real.pi/t)) (dualProductR t a) : ℂ) := by
  rcases p.sound cfg ht ha hp with ⟨hq,hr,_,hb⟩
  rcases hw with ⟨hfirst,hsecond,hadd⟩
  have hQ : jacobiNome (1/t) = (-Real.exp (-Real.pi/t) : ℝ) := by
    rw [dual_nome_complex]
    push_cast
    rfl
  rw [hQ] at hq
  have hb' : (p.beta.output.toBall cfg.prec).Contains (Real.exp (-dualProductKappa t a) : ℂ) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg] using hb
  have hbneg := DyadicBall.neg_contains hb'
  rw [← Complex.ofReal_neg] at hbneg
  have hf := w.first.sound cfg err hq hr hfirst
  have hs := w.second.sound cfg err hq hbneg hsecond
  have hout := DyadicBall.add_contains hf hs hadd
  have hQlt : |-Real.exp (-Real.pi/t)| < 1 := by
    have h := DyadicBall.norm_le_normUpper hq
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    exact h.trans_lt (by exact_mod_cast hfirst.2.1)
  have hrlt : |dualProductR t a| < 1 := by
    have h := DyadicBall.norm_le_normUpper hr
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    exact h.trans_lt (by exact_mod_cast hfirst.2.2.1)
  rw [jacobiRealE_two_series hQlt hrlt, dual_q_div_r_real, Complex.ofReal_add]
  exact hout

theorem thetaG_pos (cfg : BallConfig) (err : ℕ) {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1) (p : DyadicJacobiBaseParameters) (hp : p.Valid cfg)
    (hbt : (p.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : DyadicJacobiVerticalTrace) (hw : w.Valid cfg err p)
    (hsign : 0 < (w.output.toBall cfg.prec).center.re-(w.output.toBall cfg.prec).radius) :
    0 < (thetaG t a).re := by
  have he := (ComplexBall.re_bounds (w.sound cfg err p hp hbt hba hw)).1
  rw [Complex.ofReal_re] at he
  rw [thetaG_re_eq_jacobiRealE ht ha0 ha1]
  exact mul_pos (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos ht))
    ((Rat.cast_pos.mpr hsign).trans_le (by simpa only [Rat.cast_sub, dualProductR] using he))

theorem thetaG_neg (cfg : BallConfig) (err : ℕ) {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1) (p : DyadicJacobiBaseParameters) (hp : p.Valid cfg)
    (hbt : (p.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : DyadicJacobiVerticalTrace) (hw : w.Valid cfg err p)
    (hsign : (w.output.toBall cfg.prec).center.re+(w.output.toBall cfg.prec).radius < 0) :
    (thetaG t a).re < 0 := by
  have he := (ComplexBall.re_bounds (w.sound cfg err p hp hbt hba hw)).2
  rw [Complex.ofReal_re] at he
  rw [thetaG_re_eq_jacobiRealE ht ha0 ha1]
  have he' : jacobiRealE (-Real.exp (-Real.pi/t)) (Real.exp (-Real.pi*a/t)) ≤
      ((w.output.toBall cfg.prec).center.re+(w.output.toBall cfg.prec).radius : ℚ) := by
    simpa only [Rat.cast_add, dualProductR] using he
  have hs' : ((w.output.toBall cfg.prec).center.re+(w.output.toBall cfg.prec).radius : ℚ) < (0 : ℝ) := by
    exact_mod_cast hsign
  exact mul_neg_of_pos_of_neg (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos ht))
    (he'.trans_lt hs')

end DyadicJacobiVerticalTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiVerticalTrace.thetaG_pos
#print axioms TwoAxisHelicoid.DyadicJacobiVerticalTrace.thetaG_neg
#print axioms TwoAxisHelicoid.verticalA_small_rectangle_upper
