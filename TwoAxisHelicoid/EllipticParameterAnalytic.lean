import TwoAxisHelicoid.ComplexVerticalFunction
import TwoAxisHelicoid.RightCoefficientIdentity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] complexThetaJet thetaJet thetaQuotient thetaLogSecond thetaLogFourth

theorem complexThetaJet_time_analyticAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => complexThetaJet s j z) t := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds ht] with s hs
  exact (complexThetaJet_time_hasDerivAt hs j z).differentiableAt

theorem thetaJet_parameter_analyticAt {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    AnalyticAt ℝ (fun s : ℝ => thetaJet s j z) t := by
  have hc := complexThetaJet_time_analyticAt (show 0 < (t:ℂ).re from ht) j z
  have hr : AnalyticAt ℝ (fun s : ℝ => complexThetaJet s j z) t :=
    (hc.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  simpa only [complexThetaJet_ofReal] using hr

theorem thetaQuotient_parameter_analyticAt {t : ℝ} (ht : 0 < t) (j : ℕ) {z : ℂ}
    (hz : thetaJet t 0 z ≠ 0) : AnalyticAt ℝ (fun s : ℝ => thetaQuotient s j z) t := by
  unfold thetaQuotient
  exact (thetaJet_parameter_analyticAt ht j z).div (thetaJet_parameter_analyticAt ht 0 z) hz

theorem thetaEtaExpression_analyticAt {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ thetaEtaExpression t := by
  have ha : AnalyticAt ℝ (fun s => -(Real.pi^2/12:ℂ)*(thetaJet s 3 0/thetaJet s 1 0)) t :=
    analyticAt_const.mul ((thetaJet_parameter_analyticAt ht 3 0).div
      (thetaJet_parameter_analyticAt ht 1 0) (thetaJet_one_at_zero_ne_zero_of_pos ht))
  apply ha.congr
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (thetaEtaExpression_jet_ratio hs).symm

theorem thetaLogSecond_parameter_analyticAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    AnalyticAt ℝ (fun s : ℝ => thetaLogSecond s z) t := by
  unfold thetaLogSecond
  have h1 := thetaQuotient_parameter_analyticAt ht 1 hz
  have h2 := thetaQuotient_parameter_analyticAt ht 2 hz
  exact analyticAt_const.mul ((h1.pow 2).sub h2)

theorem thetaLogFourth_parameter_analyticAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    AnalyticAt ℝ (fun s : ℝ => thetaLogFourth s z) t := by
  unfold thetaLogFourth
  have h1 := thetaQuotient_parameter_analyticAt ht 1 hz
  have h2 := thetaQuotient_parameter_analyticAt ht 2 hz
  have h3 := thetaQuotient_parameter_analyticAt ht 3 hz
  have h4 := thetaQuotient_parameter_analyticAt ht 4 hz
  exact analyticAt_const.mul (((((analyticAt_const.mul (h2.pow 2)).sub
    ((analyticAt_const.mul (h1.pow 2)).mul h2)).add (analyticAt_const.mul (h1.pow 4))).add
    ((analyticAt_const.mul h1).mul h3)).sub h4)

theorem ellipticFReal_analyticAt {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ ellipticFReal t := by
  have hn : thetaJet t 0 (Real.pi*(1:ℂ)/2) ≠ 0 := by
    simpa only [Complex.ofReal_one] using theta_vertical_denominator ht
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
  have hL := thetaLogSecond_parameter_analyticAt ht hn
  have hr : AnalyticAt ℝ (fun s : ℝ => (thetaLogSecond s 1).re) t :=
    (Complex.reCLM.analyticAt _).comp (f := fun s : ℝ => thetaLogSecond s 1) (x := t) hL
  simpa only [thetaLogSecond_one_real,Complex.ofReal_re] using hr

noncomputable def ellipticIReal (t : ℝ) : ℝ :=
  (2*(thetaLogSecond t 1-thetaEtaExpression t)*thetaLogSecond t 1-thetaLogFourth t 1/6).re

theorem ellipticIReal_eq {t : ℝ} (ht : 0 < t) : ellipticIReal t = ellipticI t ht := by
  let L := rhombicPeriodPair t ht
  have hz : (1:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  unfold ellipticIReal ellipticI
  rw [thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz,
    thetaLogFourth_eq_weierstrassP_second ht hz,rhombic_weierstrass_second_order ht hz]
  congr 1
  ring

theorem ellipticIReal_analyticAt {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ ellipticIReal t := by
  have hn : thetaJet t 0 (Real.pi*(1:ℂ)/2) ≠ 0 := by
    simpa only [Complex.ofReal_one] using theta_vertical_denominator ht
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
  have hL := thetaLogSecond_parameter_analyticAt ht hn
  have hQ := thetaLogFourth_parameter_analyticAt ht hn
  have hE := thetaEtaExpression_analyticAt ht
  have hbase : AnalyticAt ℝ (fun s : ℝ =>
      2*(thetaLogSecond s 1-thetaEtaExpression s)*thetaLogSecond s 1-thetaLogFourth s 1/6) t :=
    ((analyticAt_const.mul (hL.sub hE)).mul hL).sub hQ.div_const
  exact (Complex.reCLM.analyticAt _).comp
    (f := fun s : ℝ => 2*(thetaLogSecond s 1-thetaEtaExpression s)*thetaLogSecond s 1-thetaLogFourth s 1/6)
    (x := t) hbase

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_analyticAt
#print axioms TwoAxisHelicoid.ellipticIReal_eq
#print axioms TwoAxisHelicoid.ellipticIReal_analyticAt
