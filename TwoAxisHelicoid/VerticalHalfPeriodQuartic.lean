import TwoAxisHelicoid.VerticalSquareLimit
import TwoAxisHelicoid.EllipticParameterAnalytic
import Mathlib.Analysis.Asymptotics.Lemmas

namespace TwoAxisHelicoid
open Complex Set Filter Asymptotics
open scoped Topology
attribute [local irreducible] thetaG thetaLogFourth thetaEtaExpression ellipticFReal verticalA

private theorem half_period_curvature_difference {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0:ℝ) 2) :
    (thetaLogFourth t x).re-(thetaLogFourth t 1).re =
      6*((thetaG t x).re-(thetaG t 1).re)*
        (((thetaG t x).re-(thetaG t 1).re)+2*(ellipticFReal t-(thetaEtaExpression t).re)) := by
  let L := rhombicPeriodPair t ht
  have hxL : (x:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
  have h1L : (1:ℂ) ∉ L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
  have curvature (w : ℝ) (hw : (w:ℂ) ∉ L.lattice) :
      (thetaLogFourth t w).re = 6*(L.weierstrassP w).re^2-(L.g₂/2).re := by
    rw [thetaLogFourth_eq_weierstrassP_second ht hw,rhombic_weierstrass_second_order ht hw]
    simp [L,pow_two,Complex.mul_re,rhombic_weierstrassP_real ht w]
  have curvature1 : (thetaLogFourth t 1).re = 6*(L.weierstrassP 1).re^2-(L.g₂/2).re := by
    simpa only [Complex.ofReal_one] using curvature 1 (by simpa only [Complex.ofReal_one] using h1L)
  have eF := congrArg Complex.re (thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht h1L)
  rw [thetaLogSecond_one_real,Complex.ofReal_re,Complex.add_re] at eF
  have val : ellipticFReal t-(thetaEtaExpression t).re=(L.weierstrassP 1).re := by
    change ellipticFReal t = (L.weierstrassP 1).re+(thetaEtaExpression t).re at eF
    linarith
  have difference : (thetaG t x).re-(thetaG t 1).re =
      (L.weierstrassP x).re-(L.weierstrassP 1).re := by
    rw [thetaG_eq_weierstrassP_of_pos ht ht x hxL,thetaG_eq_weierstrassP_of_pos ht ht 1
      (by simpa only [Complex.ofReal_one] using h1L)]
    simp only [Complex.ofReal_one,Complex.sub_re,Complex.add_re,L]
    ring
  rw [curvature x hxL,curvature1,difference,val]
  ring

/-- The pre-inversion expansion printed in Appendix A.1. The coefficient
here is the real part of the actual second spatial derivative of ℘ at 1
by thetaLogFourth_one_re. Two second-order mean values and the ℘ equation
give the fourth-order error without assuming a square-root law. -/
theorem vertical_half_period_quartic_on_branch :
    (fun t : ℝ => Real.pi/t-ellipticFReal t-(thetaLogFourth t 1).re/2*(1-verticalA t)^2)
      =O[𝓝[<] ellipticVerticalUpper] (fun t => (1-verticalA t)^4) := by
  classical
  let T := ellipticVerticalUpper
  let c := verticalMeanPoint
  let D := Ioo (0:ℝ) T
  have inner (t : ℝ) (ht : t ∈ D) : ∃ d ∈ Ioo (c t) 1,
      (thetaG t (c t)).re-(thetaG t 1).re=(thetaLogFourth t d).re/2*(c t-1)^2 := by
    have hc := (verticalMeanPoint_spec ht).1
    have h0 := (verticalA_spec ht).1.1.trans hc.1
    exact exists_second_order_mean hc.2
      (fun x hx => thetaG_real_a_hasDerivAt ht.1 (h0.trans_le hx.1) (by linarith [hx.2]))
      (fun x hx => thetaGa_real_hasDerivAt ht.1 (h0.trans_le hx.1) (by linarith [hx.2]))
      (by rw [thetaGa_one]; rfl)
  let d := fun t => if ht : t ∈ D then (inner t ht).choose else 1
  have spec (t : ℝ) (ht : t ∈ D) : d t ∈ Ioo (c t) 1 ∧
      (thetaG t (c t)).re-(thetaG t 1).re=(thetaLogFourth t (d t)).re/2*(c t-1)^2 := by
    simpa only [d,dite_eq_left ht] using (inner t ht).choose_spec
  have hdom : ∀ᶠ t in 𝓝[<] T, t ∈ D := verticalDomain_eventually_left
  have hc : Tendsto c (𝓝[<] T) (𝓝 1) := verticalMeanPoint_tendsto_one
  have hd : Tendsto d (𝓝[<] T) (𝓝 1) := hc.squeeze' tendsto_const_nhds
    (hdom.mono fun t ht => (spec t ht).1.1.le) (hdom.mono fun t ht => (spec t ht).1.2.le)
  let J := fun t => (thetaLogFourth t (d t)).re
  let J₀ := (thetaLogFourth T 1).re
  have hJ : Tendsto J (𝓝[<] T) (𝓝 J₀) := by
    have joint := thetaLogFourth_real_joint_continuousAt ellipticVerticalUpper_pos
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
    have args : Tendsto (fun t : ℝ => (t,d t)) (𝓝[<] T) (𝓝 (T,1)) :=
      (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds hd
    simpa only [J,J₀,Complex.ofReal_one,Function.comp_def] using joint.tendsto.comp args
  let r := fun t => (thetaG t (c t)).re-(thetaG t 1).re
  have hr : Tendsto r (𝓝[<] T) (𝓝 0) := by
    have h := ((hJ.div_const 2).mul ((hc.sub_const 1).pow 2)).congr'
      (hdom.mono fun t ht => (spec t ht).2.symm)
    simpa only [sub_self,zero_pow (by decide : 2≠0),mul_zero] using h
  let e := fun t => ellipticFReal t-(thetaEtaExpression t).re
  have he : ContinuousAt e T := (ellipticFReal_analyticAt ellipticVerticalUpper_pos).continuousAt.sub
    (Complex.continuous_re.continuousAt.comp (thetaEtaExpression_analyticAt ellipticVerticalUpper_pos).continuousAt)
  let K := fun t => 3/2*J t*(r t+2*e t)
  let K₀ := 3/2*J₀*(0+2*e T)
  have hK : Tendsto K (𝓝[<] T) (𝓝 K₀) := (tendsto_const_nhds.mul hJ).mul
    (hr.add (tendsto_const_nhds.mul (he.tendsto.mono_left nhdsWithin_le_nhds)))
  apply IsBigO.of_bound (‖K₀‖+1)
  filter_upwards [hdom,hK.norm.eventually (eventually_lt_nhds (lt_add_one ‖K₀‖))] with t ht bound
  have cm := (verticalMeanPoint_spec ht).1
  have hc0 := (verticalA_spec ht).1.1.trans cm.1
  have curve := half_period_curvature_difference ht.1 ⟨hc0,by linarith [cm.2]⟩
  have outer := (verticalMeanPoint_spec ht).2
  rw [thetaG_one_eq_ellipticFReal] at outer
  have ir := (spec t ht).2
  change r t=J t/2*(c t-1)^2 at ir
  change (thetaLogFourth t (c t)).re-(thetaLogFourth t 1).re = 6*r t*(r t+2*e t) at curve
  have factor : Real.pi/t-ellipticFReal t-(thetaLogFourth t 1).re/2*(1-verticalA t)^2 =
      K t*(c t-1)^2*(1-verticalA t)^2 := by
    dsimp only [K]
    linear_combination outer + ((1-verticalA t)^2/2)*curve +
      (3*(r t+2*e t)*(1-verticalA t)^2)*ir
  have inner_le : (c t-1)^2 ≤ (1-verticalA t)^2 := by
    rw [sub_sq_comm (c t) 1]
    exact pow_le_pow_left₀ (sub_nonneg.mpr cm.2.le) (sub_le_sub_left cm.1.le 1) 2
  change ‖Real.pi/t-ellipticFReal t-(thetaLogFourth t 1).re/2*(1-verticalA t)^2‖ ≤ _
  rw [factor]
  calc
    _ = ‖K t‖*(c t-1)^2*(1-verticalA t)^2 := by
      simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (c t-1)),
        abs_of_nonneg (sq_nonneg (1-verticalA t))]
    _ ≤ (‖K₀‖+1)*(1-verticalA t)^2*(1-verticalA t)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul bound.le inner_le (sq_nonneg _) (by positivity))
        (sq_nonneg _)
    _ = (‖K₀‖+1)*‖(1-verticalA t)^4‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1-verticalA t)^4)]
      ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.vertical_half_period_quartic_on_branch
