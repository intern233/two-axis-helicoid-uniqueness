import TwoAxisHelicoid.ZetaAxisIntegral
import TwoAxisHelicoid.AxisRelativePhase

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaZeta thetaEtaExpression thetaG thetaGauss

theorem closed_height_weierstrass_value {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) :
    (rhombicPeriodPair t ht).weierstrassP a = (Real.pi : ℂ)/t-thetaEtaExpression t := by
  have h := thetaG_eq_weierstrassP_of_pos ht ht a
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  rw [hG] at h
  push_cast at h
  linear_combination -h

theorem axisClosedRegularOmega_actual_differential {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) (hc : c ≠ 0) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    deriv (thetaGauss t a m) z/thetaGauss t a m z-
      I*((2*(a-(m : ℝ))/c : ℝ) : ℂ)*(coordinateData t a c ht z 2) =
      axisClosedRegularOmega t a m z := by
  rw [thetaGauss_log_derivative ht a m hz hm hp]
  have hi : I*((2*(a-(m : ℝ))/c : ℝ) : ℂ)*(coordinateData t a c ht z 2) =
      2*((m : ℂ)-a)*((rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a) := by
    dsimp [coordinateData]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hc]
    ring_nf
    simp [I_sq,sub_eq_add_neg]
  rw [hi]
  unfold thetaGaussLogDerivative axisClosedRegularOmega
  rw [closed_height_weierstrass_value ht ha hG]
  ring

theorem axisClosedRegularOmega_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    Continuous (fun y : ℝ => axisClosedRegularOmega t a m (I*y)) := by
  have he : (fun y : ℝ => axisClosedRegularOmega t a m (I*y)) =
      fun y => zetaAxisDifference t a y+
        (2*(m : ℂ)*thetaEtaExpression t+2*((m : ℂ)-a)*((Real.pi : ℂ)/t-thetaEtaExpression t)) := by
    funext y
    unfold axisClosedRegularOmega zetaAxisDifference
    rw [show I*(y : ℂ)-(a : ℂ) = -(a : ℂ)+(y : ℂ)*I by ring,
      show I*(y : ℂ)+(a : ℂ) = (a : ℂ)+(y : ℂ)*I by ring]
    ring
  rw [he]
  exact (zetaAxisDifference_continuous ht ha).add continuous_const

theorem axisClosedRegularOmega_eq_regularCoefficient {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    axisClosedRegularOmega t a 1 z = axisRegularCoefficient t ht a z := by
  have h := thetaZeta_symmetric_difference ht
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])) hz hm hp
  unfold axisClosedRegularOmega axisRegularCoefficient
  rw [h,closed_height_weierstrass_value ht ha hG]
  norm_num only [Int.cast_one]
  ring

theorem axisClosedRegularOmega_eq_on_axis {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0)
    (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    axisClosedRegularOmega t a 1 (I*y) = axisRegularCoefficient t ht a (I*y) := by
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  apply axisClosedRegularOmega_eq_regularCoefficient ht ha hG
  · simpa only [Complex.ofReal_zero,zero_add,mul_comm] using
      rhombic_vertical_strip_not_mem ht (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hy
  · have h := rhombic_noninteger_vertical_not_mem ht (x := -a) (by simpa using hp)
      (neg_ne_zero.mpr ha.1.ne') y
    simpa only [Complex.ofReal_neg,show -(a : ℂ)+(y : ℂ)*I = I*(y : ℂ)-a by ring] using h
  · simpa only [show (a : ℂ)+(y : ℂ)*I = I*(y : ℂ)+a by ring] using
      rhombic_noninteger_vertical_not_mem ht hp ha.1.ne' y

theorem axisClosedRegularOmega_integral_re {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    (∫ y : ℝ in 0..2*t, (axisClosedRegularOmega t a m (I*y)).re) =
      2*Real.pi*(2*(m : ℝ)-1) := by
  have hI := (axisClosedRegularOmega_continuous ht ha m).intervalIntegrable (μ := volume) 0 (2*t)
  have hi := congrArg Complex.im (axisClosedRegularOmega_integral ht ha m)
  have he := Complex.reCLM.intervalIntegral_comp_comm hI
  change (∫ y : ℝ in 0..2*t, (axisClosedRegularOmega t a m (I*y)).re) =
    (∫ y : ℝ in 0..2*t, axisClosedRegularOmega t a m (I*y)).re at he
  rw [he]
  simpa [Complex.mul_im,Complex.mul_re] using hi

theorem axisRegularCoefficient_intervalIntegrable {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) :
    IntervalIntegrable (fun y : ℝ => (axisRegularCoefficient t ht a (I*y)).re) volume 0 (2*t) := by
  have hI := (Complex.continuous_re.comp (axisClosedRegularOmega_continuous ht ha 1)).intervalIntegrable
    (μ := volume) 0 (2*t)
  apply hI.congr_uIoo
  intro y hy
  rw [uIoo_of_le (by linarith : 0 ≤ 2*t)] at hy
  exact congrArg Complex.re (axisClosedRegularOmega_eq_on_axis ht ha hG hy)

theorem axisRegularCoefficient_integral_two_pi {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) :
    (∫ y : ℝ in 0..2*t, (axisRegularCoefficient t ht a (I*y)).re) = 2*Real.pi := by
  calc
    _ = ∫ y : ℝ in 0..2*t, (axisClosedRegularOmega t a 1 (I*y)).re := by
      apply intervalIntegral.integral_congr_uIoo
      intro y hy
      rw [uIoo_of_le (by linarith : 0 ≤ 2*t)] at hy
      exact (congrArg Complex.re (axisClosedRegularOmega_eq_on_axis ht ha hG hy)).symm
    _ = _ := by
      have h := axisClosedRegularOmega_integral_re ht ha 1
      norm_num at h
      exact h

/-- The relative phase has exactly one full turn along the closed vertical
cycle of the actual basic branch. Values assigned at its removable endpoints
do not affect the ordinary interval integral. -/
theorem axisRelativePhase_total_increment {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) :
    axisRelativePhase t ht a (2*t)-axisRelativePhase t ht a 0 = 2*Real.pi := by
  have hI := axisRegularCoefficient_intervalIntegrable ht ha hG
  have h0t := hI.mono_set (show uIcc (0 : ℝ) t ⊆ uIcc 0 (2*t) by
    rw [uIcc_of_le ht.le,uIcc_of_le (by linarith : 0 ≤ 2*t)]
    exact Icc_subset_Icc le_rfl (by linarith))
  have ht2t := hI.mono_set (show uIcc t (2*t) ⊆ uIcc 0 (2*t) by
    rw [uIcc_of_le (by linarith : t ≤ 2*t),uIcc_of_le (by linarith : 0 ≤ 2*t)]
    exact Icc_subset_Icc ht.le le_rfl)
  have he := intervalIntegral.integral_add_adjacent_intervals h0t ht2t
  unfold axisRelativePhase
  rw [intervalIntegral.integral_symm 0 t]
  rw [axisRegularCoefficient_integral_two_pi ht ha hG] at he
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisClosedRegularOmega_actual_differential
#print axioms TwoAxisHelicoid.axisRelativePhase_total_increment
