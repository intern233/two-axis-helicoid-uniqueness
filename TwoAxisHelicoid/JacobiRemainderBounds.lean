import TwoAxisHelicoid.ProductAnnulusBounds

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct

noncomputable def jacobiRemainderProduct (Q r x : ℂ) : ℂ :=
  jacobiFactorProduct Q (r*x)*jacobiFactorProduct Q (Q/(r*x))

theorem jacobiPairProduct_remainder {Q r x : ℂ} (hQ : ‖Q‖ < 1) :
    jacobiPairProduct Q (r*x) = (1-Q/(r*x))*jacobiRemainderProduct Q r x := by
  unfold jacobiPairProduct jacobiRemainderProduct
  rw [div_eq_mul_inv, ← jacobiFactorProduct_shift hQ ((r*x)⁻¹)]
  ring

theorem small_remainder_argument_bounds {q r : ℝ} (hq0 : 0 < q)
    (hrl : q/2 ≤ r) (hru : r ≤ q) {Q x : ℂ} (hQ : ‖Q‖ = q^2)
    (hxl : q ≤ ‖x‖) (hxu : ‖x‖ ≤ q⁻¹) :
    ‖(r : ℂ)*x‖ ≤ 1 ∧ ‖Q/((r : ℂ)*x)‖ ≤ 2 := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < ‖x‖ := hq0.trans_le hxl
  have hnorm : ‖(r : ℂ)*x‖ = r*‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  constructor
  · rw [hnorm]
    have h := mul_le_mul hru hxu (norm_nonneg x) hq0.le
    have he : q*q⁻¹ = 1 := mul_inv_cancel₀ hq0.ne'
    rwa [he] at h
  · rw [norm_div, hQ, hnorm]
    apply (div_le_iff₀ (mul_pos hr0 hx0)).mpr
    have h := mul_le_mul hrl hxl hq0.le hr0.le
    nlinarith

theorem jacobiRemainderProduct_annulus_bound {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    (hrl : q/2 ≤ r) (hru : r ≤ q) {Q x : ℂ} (hQ : ‖Q‖ = q^2)
    (hxl : q ≤ ‖x‖) (hxu : ‖x‖ ≤ q⁻¹) :
    ‖jacobiRemainderProduct Q r x-1‖ ≤ 5*q^2 := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have hd : 0 < 1-q^2 := by nlinarith
  have hb := small_remainder_argument_bounds hq0 hrl hru hQ hxl hxu
  have hs : q^2*‖(r : ℂ)*x‖/(1-q^2)+q^2*‖Q/((r : ℂ)*x)‖/(1-q^2) ≤ 4*q^2 := by
    rw [← add_div]
    apply (div_le_iff₀ hd).mpr
    have h₁ := mul_le_mul_of_nonneg_left hb.1 (sq_nonneg q)
    have h₂ := mul_le_mul_of_nonneg_left hb.2 (sq_nonneg q)
    have hd' : (3/4 : ℝ) ≤ 1-q^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd' (sq_nonneg q)]
  have h := jacobi_two_products_sub_one_norm_le hQ1 ((r : ℂ)*x) (Q/((r : ℂ)*x))
  rw [hQ] at h
  have he := exp_sub_one_le_add_sq (by positivity : 0 ≤ 4*q^2) (by nlinarith : 4*q^2 ≤ 1)
  have hq4 : (q^2)^2 ≤ (1/16 : ℝ)*q^2 := by
    have hcap : q^2 ≤ 1/16 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg q)]
  have hm := Real.exp_le_exp.mpr hs
  change ‖jacobiFactorProduct Q ((r : ℂ)*x)*jacobiFactorProduct Q (Q/((r : ℂ)*x))-1‖ ≤ _
  nlinarith

theorem jacobiRemainderProduct_square_bound {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    (hrl : q/2 ≤ r) (hru : r ≤ q) {Q x : ℂ} (hQ : ‖Q‖ = q^2)
    (hxl : q ≤ ‖x‖) (hxu : ‖x‖ ≤ q⁻¹) :
    ‖(jacobiRemainderProduct Q r x)^2-1‖ ≤ 11*q^2 := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have h := square_sub_one_norm_le (jacobiRemainderProduct_annulus_bound hq0 hq hrl hru hQ hxl hxu)
  have hcap : q^2 ≤ 1/25 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg q)]

theorem jacobiFactorProduct_one_small_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q : ℂ} (hQ : ‖Q‖ = q^2) : ‖jacobiFactorProduct Q 1-1‖ ≤ 2*q^2 := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have h := jacobiFactorProduct_sub_one_norm_le hQ1 (1 : ℂ)
  rw [hQ, norm_one, mul_one] at h
  have hs : q^2/(1-q^2) ≤ (3/2)*q^2 := by
    apply (div_le_iff₀ (by nlinarith : 0 < 1-q^2)).mpr
    have hh : (2/3 : ℝ) ≤ 1-q^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg q)]
  have he := exp_sub_one_le_add_sq (by positivity : 0 ≤ (3/2)*q^2)
    (by nlinarith : (3/2)*q^2 ≤ 1)
  have hcap : q^2 ≤ 1/10 := by nlinarith
  have hm := Real.exp_le_exp.mpr hs
  nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg q)]

theorem jacobiFactorProduct_fourth_power_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q : ℂ} (hQ : ‖Q‖ = q^2) : ‖(jacobiFactorProduct Q 1)^4-1‖ ≤ 9*q^2 := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hp := jacobiFactorProduct_one_small_bound hq0 hq hQ
  have h := four_factors_sub_one_norm_le hp hp hp hp
  have heq : jacobiFactorProduct Q 1*jacobiFactorProduct Q 1*
      jacobiFactorProduct Q 1*jacobiFactorProduct Q 1 = (jacobiFactorProduct Q 1)^4 := by ring
  rw [heq, show 2*q^2+2*q^2+2*q^2+2*q^2 = 8*q^2 by ring] at h
  have he := exp_sub_one_le_add_sq (by positivity : 0 ≤ 8*q^2) (by nlinarith : 8*q^2 ≤ 1)
  have hcap : q^2 ≤ 1/64 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg q)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiRemainderProduct_annulus_bound
#print axioms TwoAxisHelicoid.jacobiFactorProduct_fourth_power_bound
