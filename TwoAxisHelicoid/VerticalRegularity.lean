import TwoAxisHelicoid.EllipticVerticalDomain
import TwoAxisHelicoid.ThetaCompositeContinuity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaG

theorem theta_vertical_denominator {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha2 : a < 2) :
    thetaJet t 0 (Real.pi*a/2) ≠ 0 := by
  have hn := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (a:ℂ)).mp
    (real_not_mem_rhombic_lattice_of_pos ht ha0 ha2)
  exact hn

theorem thetaG_real_a_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha2 : a < 2) :
    HasDerivAt (fun b => (thetaG t b).re) (thetaGa t a).re a :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
    (thetaG_a_hasDerivAt ht a (theta_vertical_denominator ht ha0 ha2))

theorem thetaG_real_t_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha2 : a < 2) :
    HasDerivAt (fun s => (thetaG s a).re) (thetaGt t a).re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (thetaG_parameter_hasDerivAt ht a (theta_vertical_denominator ht ha0 ha2))

theorem thetaGa_re_eq_wp_deriv {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha2 : a < 2) :
    (thetaGa t a).re = ((rhombicPeriodPair t ht).derivWeierstrassP a).re := by
  have hd := ((rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht ha0 ha2).add_const
    (thetaEtaExpression t).re).sub_const (Real.pi/t)
  have he : (fun b : ℝ => (thetaG t b).re) =ᶠ[𝓝 a]
      fun b => ((rhombicPeriodPair t ht).weierstrassP b).re+(thetaEtaExpression t).re-Real.pi/t := by
    filter_upwards [Ioo_mem_nhds ha0 ha2] with b hb
    rw [thetaG_eq_weierstrassP_of_pos ht ht b
      (real_not_mem_rhombic_lattice_of_pos ht hb.1 hb.2)]
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re]
  exact (thetaG_real_a_hasDerivAt ht ha0 ha2).unique (hd.congr_of_eventuallyEq he)

theorem thetaGa_re_neg_unit {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1) :
    (thetaGa t a).re < 0 := by
  rw [thetaGa_re_eq_wp_deriv ht ha0 (by linarith)]
  exact rhombic_weierstrassP_derivative_real_neg_of_pos ht ht ha0 ha1

theorem theta_vertical_quotient_continuousAt {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha2 : a < 2) (j : ℕ) :
    ContinuousAt (fun p : ℝ × ℝ => thetaQuotient p.1 j (Real.pi*p.2/2)) (t,a) := by
  have hpair : ContinuousAt (fun p : ℝ × ℝ => (p.1,(Real.pi*p.2/2:ℂ))) (t,a) := by fun_prop
  have hc (k : ℕ) : ContinuousAt (fun p : ℝ × ℝ => thetaJet p.1 k (Real.pi*p.2/2)) (t,a) := by
    have h := (thetaJet_joint_continuousAt ht k (Real.pi*a/2)).comp
      (f := fun p : ℝ × ℝ => (p.1,(Real.pi*p.2/2:ℂ))) (x := (t,a)) hpair
    exact h
  unfold thetaQuotient
  exact (hc j).div (hc 0) (theta_vertical_denominator ht ha0 ha2)

theorem thetaG_real_joint_continuousAt {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha2 : a < 2) :
    ContinuousAt (fun p : ℝ × ℝ => (thetaG p.1 p.2).re) (t,a) := by
  have h1 := theta_vertical_quotient_continuousAt ht ha0 ha2 1
  have h2 := theta_vertical_quotient_continuousAt ht ha0 ha2 2
  have hp : ContinuousAt (fun p : ℝ × ℝ => ((Real.pi/p.1:ℝ):ℂ)) (t,a) :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.div continuous_fst.continuousAt ht.ne')
  unfold thetaG
  exact Complex.continuous_re.continuousAt.comp
    ((continuousAt_const.mul ((h1.pow 2).sub h2)).sub hp)

theorem thetaGa_joint_continuousAt {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha2 : a < 2) :
    ContinuousAt (fun p : ℝ × ℝ => thetaGa p.1 p.2) (t,a) := by
  have h1 := theta_vertical_quotient_continuousAt ht ha0 ha2 1
  have h2 := theta_vertical_quotient_continuousAt ht ha0 ha2 2
  have h3 := theta_vertical_quotient_continuousAt ht ha0 ha2 3
  exact continuousAt_const.mul ((((continuousAt_const.mul h1).mul h2).sub
    (continuousAt_const.mul (h1.pow 3))).sub h3)

theorem thetaGt_joint_continuousAt {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha2 : a < 2) :
    ContinuousAt (fun p : ℝ × ℝ => thetaGt p.1 p.2) (t,a) := by
  have h1 := theta_vertical_quotient_continuousAt ht ha0 ha2 1
  have h2 := theta_vertical_quotient_continuousAt ht ha0 ha2 2
  have h3 := theta_vertical_quotient_continuousAt ht ha0 ha2 3
  have h4 := theta_vertical_quotient_continuousAt ht ha0 ha2 4
  have hp : ContinuousAt (fun p : ℝ × ℝ => ((Real.pi/p.1^2:ℝ):ℂ)) (t,a) :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.div (continuous_fst.continuousAt.pow 2) (pow_ne_zero 2 ht.ne'))
  exact (continuousAt_const.mul (((continuousAt_const.mul h1).mul (h3.sub (h1.mul h2))).sub
    (h4.sub (h2.pow 2)))).add hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGa_re_neg_unit
