import TwoAxisHelicoid.LeftMomentEstimates
import TwoAxisHelicoid.LeftActualPeriod

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
set_option maxHeartbeats 1000000
attribute [local irreducible] verticalA thetaA dualThetaA

theorem leftPeriod_error_le_moments {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    |actualPeriodAlong t-leftComparisonPeriod t| ≤
      (100*leftKappa t*leftNome t)*leftErrorMoment t 0+
        4*leftErrorMoment t 1+3*leftErrorMoment t 2 := by
  have hdomain := small_height_mem_vertical_domain ht (by linarith : t ≤ 1/4)
  have hab : -(1/(2*t)) ≤ 1/(2*t) :=
    le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
  have hA := (leftActualPathDifferential_continuous hdomain).intervalIntegrable
    (μ := volume) (-(1/(2*t))) (1/(2*t))
  have hC := (leftComparison_path_continuous t).intervalIntegrable
    (μ := volume) (-(1/(2*t))) (1/(2*t))
  have hD := hA.sub hC
  have h0 := (leftErrorMoment_integrable t 0).const_mul (100*leftKappa t*leftNome t)
  have h1 := (leftErrorMoment_integrable t 1).const_mul 4
  have h2 := (leftErrorMoment_integrable t 2).const_mul 3
  have hM := (h0.add h1).add h2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab hD.norm hM (fun y hy => by
    have h := leftActualPath_error_norm_le ht htu hy
    calc
      _ ≤ ‖leftComparisonFunction t (leftPathW y)‖*
        (100*leftKappa t*leftNome t+4*leftProductB t (Real.exp (-Real.pi*y))+
          3*(leftProductB t (Real.exp (-Real.pi*y)))^2) := h
      _ = _ := by simp only [pow_zero, pow_one, mul_one]; ring)
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have he : actualPeriodAlong t-leftComparisonPeriod t =
      -(∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)),
        leftActualPathDifferential t y-I*leftComparisonFunction t (leftPathW y)).re := by
    rw [actualPeriodAlong_eq_left_path hdomain, leftComparisonPeriod,
      intervalIntegral.integral_sub hA hC, Complex.sub_re]
    ring
  rw [he, abs_neg]
  exact (Complex.abs_re_le_norm _).trans
    ((intervalIntegral.norm_integral_le_integral_norm hab).trans hmono)

theorem leftPeriod_error_lt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    |actualPeriodAlong t-leftComparisonPeriod t| < 69*(Real.pi/t) := by
  have hκ0 : 0 < leftKappa t := by linarith [leftKappa_gt ht htu]
  have hq0 := leftNome_pos t
  have h0 := mul_le_mul_of_nonneg_left (leftErrorMoment_zero_le ht htu)
    (show 0 ≤ 100*leftKappa t*leftNome t by positivity)
  have h1 := mul_le_mul_of_nonneg_left (leftErrorMoment_one_le ht htu) (by norm_num : (0 : ℝ) ≤ 4)
  have h2 := mul_le_mul_of_nonneg_left (leftErrorMoment_two_le ht htu) (by norm_num : (0 : ℝ) ≤ 3)
  have hm := add_le_add (add_le_add h0 h1) h2
  have he : (100*leftKappa t*leftNome t)*
      ((Real.pi/t)*(Real.exp (leftKappa t)/(2*leftKappa t)+leftKappa0 t))+
      4*((Real.pi/t)*3)+3*((Real.pi/t)*2) =
      (Real.pi/t)*(50*leftNome t*Real.exp (leftKappa t)+
        100*leftKappa t*leftNome t*leftKappa0 t+18) := by
    field_simp [ht.ne', hκ0.ne']
    ring
  rw [he] at hm
  have hc := mul_lt_mul_of_pos_left (left_moment_error_coefficient_lt ht htu)
    (div_pos Real.pi_pos ht)
  rw [mul_comm (Real.pi/t) 69] at hc
  exact (leftPeriod_error_le_moments ht htu).trans_lt (hm.trans_lt hc)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftPeriod_error_le_moments
#print axioms TwoAxisHelicoid.leftPeriod_error_lt
