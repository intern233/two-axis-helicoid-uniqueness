import TwoAxisHelicoid.ZetaAxisParameterDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaZeta zetaPoleRegular

/-- Both copies of ℘ are integrated on the upward path z = iy, from 0
to 2it. Their summed integral is the derivative of the actual ζ integral. -/
theorem zeta_axis_derivative_wp_integral {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    let W := (rhombicPeriodPair t ht).weierstrassP
    let V := I * (∫ y : ℝ in 0..2*t,
      W (-(a : ℂ)+(y : ℂ)*I) + W ((a : ℂ)+(y : ℂ)*I))
    HasDerivAt (fun u : ℝ => I * (∫ y : ℝ in 0..2*t, zetaAxisDifference t u y)) V a ∧
      V = -2*zetaImaginaryQuasi t := by
  intro W V
  let w := fun (x y : ℝ) => W ((x : ℂ)+(y : ℂ)*I)
  have cont (x : ℝ) (hx : |x| < 1) (hn : x ≠ 0) : Continuous (w x) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP _
      (rhombic_noninteger_vertical_not_mem ht hx hn y)).continuousAt.comp
        (f := fun v : ℝ => (x : ℂ)+(v : ℂ)*I) (by fun_prop)
  have segment (x : ℝ) (hx : |x| < 1) (hn : x ≠ 0) :
      I * (∫ y : ℝ in 0..2*t, w x y) = -zetaImaginaryQuasi t := by
    have hd (y : ℝ) : HasDerivAt (fun v : ℝ => -thetaZeta t ((x : ℂ)+(v : ℂ)*I))
        (I*w x y) y := by
      have path : HasDerivAt (fun z : ℂ => (x : ℂ)+z*I) I (y : ℂ) := by
        simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)
      have ζ := thetaZeta_hasDerivAt_of_pos ht ht (rhombic_noninteger_vertical_not_mem ht hx hn y)
      simpa only [Pi.neg_apply,Function.comp_apply,neg_mul,neg_neg,mul_comm I,w,W] using
        ((ζ.comp (y : ℂ) path).neg).comp_ofReal
    have evaluated := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2*t)
      (fun y _ => hd y) ((continuous_const.mul (cont x hx hn)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at evaluated
    have base : (x : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
      simpa using rhombic_noninteger_vertical_not_mem ht hx hn 0
    have top : (x : ℂ)+((2*t : ℝ) : ℂ)*I = (x : ℂ)+2*I*t := by push_cast; ring
    simp only [top,thetaZeta_add_vertical ht base,Complex.ofReal_zero,zero_mul,add_zero] at evaluated
    linear_combination evaluated
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  have hm : |-a| < 1 := by simpa using hp
  have value : V = -2*zetaImaginaryQuasi t := by
    change I * (∫ y : ℝ in 0..2*t, W (-(a : ℂ)+(y : ℂ)*I) + w a y) = _
    simp_rw [← Complex.ofReal_neg]
    change I * (∫ y : ℝ in 0..2*t, w (-a) y + w a y) = _
    rw [intervalIntegral.integral_add ((cont (-a) hm (neg_ne_zero.mpr ha.1.ne')).intervalIntegrable _ _)
      ((cont a hp ha.1.ne').intervalIntegrable _ _),mul_add,
      segment (-a) hm (neg_ne_zero.mpr ha.1.ne'),segment a hp ha.1.ne']
    ring
  exact ⟨value.symm ▸ thetaZeta_axis_integral_hasDerivAt ht ha,value⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.zeta_axis_derivative_wp_integral
