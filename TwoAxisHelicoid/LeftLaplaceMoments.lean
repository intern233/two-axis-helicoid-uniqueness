import TwoAxisHelicoid.LeftChordKernel

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 1000000

theorem left_integral_shifted_exp {κ : ℝ} (hκ : 0 < κ) :
    (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)) = (Real.exp κ-1)/κ := by
  have hd (x : ℝ) : HasDerivAt (fun v : ℝ => -Real.exp (-κ*v)/κ)
      (Real.exp (-κ*x)) x := by
    have h := (((hasDerivAt_id x).const_mul (-κ)).exp.neg).div_const κ
    simp only [id_eq, Pi.neg_apply, mul_one] at h
    convert h using 1
    field_simp [hκ.ne']
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 0)
    (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)
  convert hi using 1
  simp only [mul_zero, Real.exp_zero, mul_neg, mul_one, neg_neg]
  ring

theorem left_integral_shifted_exp_linear {κ : ℝ} (hκ : 0 < κ) :
    (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*((v+1)/2)) =
      (Real.exp κ-κ-1)/(2*κ^2) := by
  have hd (x : ℝ) : HasDerivAt
      (fun v : ℝ => -Real.exp (-κ*v)*((v+1)/κ+1/κ^2)/2)
      (Real.exp (-κ*x)*((x+1)/2)) x := by
    have h := ((((hasDerivAt_id x).const_mul (-κ)).exp.neg).mul
      ((((hasDerivAt_id x).add_const 1).div_const κ).add_const (1/κ^2))).div_const 2
    simp only [id_eq, Pi.neg_apply, mul_one] at h
    convert h using 1
    field_simp [hκ.ne']
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 0)
    (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)
  convert hi using 1
  simp only [mul_zero, Real.exp_zero, mul_neg, mul_one, neg_neg, zero_add, neg_add_cancel]
  field_simp [hκ.ne']
  ring

theorem left_integral_shifted_exp_quadratic {κ : ℝ} (hκ : 0 < κ) :
    (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*(v+1)^2) =
      (2*Real.exp κ-κ^2-2*κ-2)/κ^3 := by
  have hd (x : ℝ) : HasDerivAt
      (fun v : ℝ => -Real.exp (-κ*v)*((v+1)^2/κ+2*(v+1)/κ^2+2/κ^3))
      (Real.exp (-κ*x)*(x+1)^2) x := by
    have hp := (((((hasDerivAt_id x).add_const 1).pow 2).div_const κ).add
      ((((hasDerivAt_id x).add_const 1).const_mul 2).div_const (κ^2))).add_const (2/κ^3)
    have h := (((hasDerivAt_id x).const_mul (-κ)).exp.neg).mul hp
    simp only [id_eq, Pi.neg_apply, Pi.add_apply, Pi.pow_apply, mul_one, Nat.reduceSub, pow_one] at h
    convert h using 1
    field_simp [hκ.ne']
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 0)
    (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)
  convert hi using 1
  simp only [mul_zero, Real.exp_zero, mul_neg, mul_one, neg_neg, zero_add, neg_add_cancel,
    zero_pow (by decide : 2 ≠ 0), one_pow, zero_div, add_zero]
  field_simp [hκ.ne']
  ring

theorem left_integral_shifted_exp_le {κ : ℝ} (hκ : 0 < κ) :
    (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)) ≤ Real.exp κ/κ := by
  rw [left_integral_shifted_exp hκ]
  exact div_le_div_of_nonneg_right (by linarith) hκ.le

theorem left_integral_shifted_exp_quadratic_le {κ : ℝ} (hκ : 0 < κ) :
    (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*(v+1)^2) ≤ 2*Real.exp κ/κ^3 := by
  rw [left_integral_shifted_exp_quadratic hκ]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg κ]) (by positivity)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_integral_shifted_exp_linear
#print axioms TwoAxisHelicoid.left_integral_shifted_exp_quadratic_le
