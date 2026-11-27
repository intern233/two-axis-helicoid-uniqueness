import TwoAxisHelicoid.ProductPerturbationBounds
import TwoAxisHelicoid.JacobiLogDerivative

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct

theorem small_annulus_products {q : ℝ} (hq0 : 0 < q) (_hq : q ≤ 1/100000)
    {x : ℂ} (hl : q ≤ ‖x‖) (hu : ‖x‖ ≤ q⁻¹) :
    q^2*‖x‖ ≤ q ∧ q^2*‖x⁻¹‖ ≤ q := by
  have hx0 : 0 < ‖x‖ := hq0.trans_le hl
  constructor
  · have h := mul_le_mul_of_nonneg_left hu (sq_nonneg q)
    have he : q^2*q⁻¹ = q := by field_simp
    rwa [he] at h
  · rw [norm_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ hx0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hl hq0.le]

theorem small_annulus_sum_le {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {x : ℂ} (hl : q ≤ ‖x‖) (hu : ‖x‖ ≤ q⁻¹) :
    q^2*‖x‖/(1-q^2)+q^2*‖x⁻¹‖/(1-q^2) ≤ 3*q := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hd : 0 < 1-q^2 := by nlinarith
  have h := small_annulus_products hq0 hq hl hu
  rw [← add_div]
  apply (div_le_iff₀ hd).mpr
  have hh : (2/3 : ℝ) ≤ 1-q^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh hq0.le]

theorem jacobiPairProduct_annulus_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q x : ℂ} (hQ : ‖Q‖ = q^2) (hl : q ≤ ‖x‖) (hu : ‖x‖ ≤ q⁻¹) :
    ‖jacobiPairProduct Q x-1‖ ≤ 4*q := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have h := jacobiPairProduct_sub_one_norm_le hQ1 x
  rw [hQ] at h
  have hs := small_annulus_sum_le hq0 hq hl hu
  have he := exp_sub_one_le_add_sq (by positivity : 0 ≤ 3*q) (by linarith : 3*q ≤ 1)
  have hm := Real.exp_le_exp.mpr hs
  nlinarith

theorem jacobiPairProduct_annulus_inverse_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q x : ℂ} (hQ : ‖Q‖ = q^2) (hl : q ≤ ‖x‖) (hu : ‖x‖ ≤ q⁻¹) :
    ‖((jacobiPairProduct Q x)⁻¹)^2-1‖ ≤ 12*q := by
  have h := inverse_square_sub_one_norm_le (jacobiPairProduct_annulus_bound hq0 hq hQ hl hu)
    (by linarith : 4*q ≤ 1/100)
  linarith

theorem jacobiPairProduct_euler_logDeriv {Q x : ℂ} (hQ : ‖Q‖ < 1) (hx : x ≠ 0)
    (hp : ‖Q‖*‖x‖ < 1) (hm : ‖Q‖*‖x⁻¹‖ < 1) :
    x*logDeriv (jacobiPairProduct Q) x =
      x*logDeriv (jacobiFactorProduct Q) x-x⁻¹*logDeriv (jacobiFactorProduct Q) x⁻¹ := by
  have hp0 := jacobiFactorProduct_ne_zero_of_norm hQ hp
  have hm0 := jacobiFactorProduct_ne_zero_of_norm hQ hm
  have hdp := (jacobiFactorProduct_differentiable hQ x).hasDerivAt
  have hdm := ((jacobiFactorProduct_differentiable hQ x⁻¹).hasDerivAt).comp x (hasDerivAt_inv hx)
  have hd := hdp.mul hdm
  change HasDerivAt (jacobiPairProduct Q) _ x at hd
  rw [logDeriv_apply, hd.deriv]
  simp only [jacobiPairProduct, logDeriv_apply, Function.comp_apply]
  field_simp [hp0, hm0, hx]
  ring

theorem jacobi_factor_euler_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q x : ℂ} (hQ : ‖Q‖ = q^2) (hx : q^2*‖x‖ ≤ q) :
    ‖x*logDeriv (jacobiFactorProduct Q) x‖ ≤ 2*q := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have hpx : ‖Q‖*‖x‖ < 1 := by rw [hQ]; linarith
  have h := mul_le_mul_of_nonneg_left (jacobiFactorProduct_logDeriv_norm_le hQ1 hpx)
    (norm_nonneg x)
  rw [norm_mul]
  apply h.trans
  rw [hQ]
  have hd : 0 < (1-q^2)*(1-q^2*‖x‖) := mul_pos (by nlinarith) (by linarith)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  have hd1 : (3/4 : ℝ) ≤ 1-q^2 := by nlinarith
  have hd2 : (3/4 : ℝ) ≤ 1-q^2*‖x‖ := by linarith
  have hd3 := mul_le_mul hd1 hd2 (by norm_num : (0 : ℝ) ≤ 3/4) (by nlinarith : 0 ≤ 1-q^2)
  nlinarith [mul_le_mul_of_nonneg_left hd3 hq0.le]

theorem jacobiPairProduct_annulus_log_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    {Q x : ℂ} (hQ : ‖Q‖ = q^2) (hl : q ≤ ‖x‖) (hu : ‖x‖ ≤ q⁻¹) :
    ‖x*logDeriv (jacobiPairProduct Q) x‖ ≤ 4*q := by
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have hx : x ≠ 0 := norm_pos_iff.mp (hq0.trans_le hl)
  have hp := small_annulus_products hq0 hq hl hu
  have hm : ‖Q‖*‖x⁻¹‖ < 1 := by rw [hQ]; linarith [hp.2]
  have hn : ‖Q‖*‖x‖ < 1 := by rw [hQ]; linarith [hp.1]
  rw [jacobiPairProduct_euler_logDeriv hQ1 hx hn hm]
  have h₁ := jacobi_factor_euler_bound hq0 hq hQ hp.1
  have h₂ := jacobi_factor_euler_bound hq0 hq hQ hp.2
  exact (norm_sub_le _ _).trans (by linarith)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiPairProduct_annulus_bound
#print axioms TwoAxisHelicoid.jacobiPairProduct_annulus_inverse_bound
#print axioms TwoAxisHelicoid.jacobiPairProduct_annulus_log_bound
