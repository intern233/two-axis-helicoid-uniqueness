import TwoAxisHelicoid.AllHorizontalRegularity
import TwoAxisHelicoid.AllHeightPeriods
import TwoAxisHelicoid.VerticalBranchLimit

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaSigma thetaSigmaKernel thetaZeta

theorem thetaA_one_eq_weierstrassP {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaA t 1 z = (rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP 1 := by
  have h1 : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht z h1 hz]
  have hadd := thetaSigma_addition_of_pos ht ht h1 hz
  have hq := thetaSigma_add_two t (z-1)
  rw [show z-1+2 = z+1 by ring,sub_add_cancel] at hq
  rw [hq] at hadd
  simp only [thetaSigmaKernel,Complex.ofReal_one,sub_self,mul_zero,zero_mul,zero_add]
  linear_combination -hadd

theorem weierstrass_midline_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in (-1)..1, (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))) =
      -2*thetaEtaExpression t := by
  let P := (rhombicPeriodPair t ht).weierstrassP
  have hc : Continuous (fun x : ℝ => P ((x:ℂ)+I*((t/2:ℝ):ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hp := (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt
    exact hp.comp (f := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)) (by fun_prop)
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -thetaZeta t ((y:ℂ)+I*((t/2:ℝ):ℂ)))
      (P ((x:ℂ)+I*((t/2:ℝ):ℂ))) x := by
    have harg := (hasDerivAt_id x).ofReal_comp.add_const (I*((t/2:ℝ):ℂ))
    have h := ((thetaZeta_hasDerivAt_of_pos ht ht (rhombic_midline_not_mem ht x)).comp x harg).neg
    convert h using 1
    · funext y
      rfl
    · simp only [Complex.ofReal_one,mul_one,neg_neg,P]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable (-1) 1 (μ := volume))
  have hq := thetaZeta_add_two t ((-1:ℂ)+I*((t/2:ℝ):ℂ))
  rw [show (-1:ℂ)+I*((t/2:ℝ):ℂ)+2 = 1+I*((t/2:ℝ):ℂ) by ring] at hq
  simp only [Complex.ofReal_one,Complex.ofReal_neg] at hi
  change (∫ x : ℝ in (-1)..1, P ((x:ℂ)+I*((t/2:ℝ):ℂ))) = _
  linear_combination hi-hq

theorem thetaHorizontalPeriod_one {t : ℝ} (ht : 0 < t) :
    thetaHorizontalPeriod t 1 = -ellipticFReal t := by
  have h1 : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have he := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht h1
  have hint : IntervalIntegrable (fun x : ℝ =>
      (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))) volume (-1) 1 := by
    have hc : Continuous (fun x : ℝ => (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
        (f := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)) (by fun_prop)
    exact hc.intervalIntegrable (-1) 1
  unfold thetaHorizontalPeriod ellipticFReal
  simp_rw [thetaA_one_eq_weierstrassP ht (rhombic_midline_not_mem ht _)]
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,weierstrass_midline_integral ht,
    intervalIntegral.integral_const,he]
  norm_num [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.real_smul]
  ring

theorem thetaHorizontalPeriod_right_endpoint :
    thetaHorizontalPeriod ellipticVerticalUpper 1 = -Real.pi/ellipticVerticalUpper := by
  rw [thetaHorizontalPeriod_one ellipticVerticalUpper_pos]
  have h := thetaG_one_eq_ellipticFReal ellipticVerticalUpper
  rw [thetaG_vertical_upper_one_zero,Complex.zero_re] at h
  rw [neg_div]
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaHorizontalPeriod_right_endpoint
