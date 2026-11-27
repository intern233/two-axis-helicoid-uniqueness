import TwoAxisHelicoid.JacobiNormalizationBounds
import TwoAxisHelicoid.DualProductIdentity

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiRemainderProduct

noncomputable def jacobiProductError (Q r : ℂ) (k : ℝ) (x : ℂ) : ℂ :=
  jacobiNormalization Q r*
    (((1-r*x)*jacobiPairProduct Q (r*x))/jacobiPairProduct Q x)^2*
    Complex.exp (-2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x)

noncomputable def jacobiSmallCorrection (Q r : ℂ) (k : ℝ) (x : ℂ) : ℂ :=
  jacobiNormalization Q r*(jacobiRemainderProduct Q r x)^2*
    ((jacobiPairProduct Q x)⁻¹)^2*
    Complex.exp (-2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x)

theorem jacobiProductError_factor {Q r x : ℂ} (hQ : ‖Q‖ < 1) (k : ℝ) :
    jacobiProductError Q r k x =
      jacobiSmallCorrection Q r k x*((1-r*x)*(1-Q/(r*x)))^2 := by
  unfold jacobiProductError jacobiSmallCorrection
  rw [jacobiPairProduct_remainder hQ]
  simp only [div_eq_mul_inv, mul_pow]
  ring

theorem jacobiSmallCorrection_bound {q r k : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    (hrl : q/2 ≤ r) (hru : r ≤ q)
    (hroot : 0 ≤ q^2/r-r ∧ q^2/r-r ≤ 12*q^2)
    (hk : 25/2 < k) (hkq : k*q < 1/10000)
    {x : ℂ} (hxl : q ≤ ‖x‖) (hxu : ‖x‖ ≤ q⁻¹) :
    ‖jacobiSmallCorrection (-(q^2 : ℝ) : ℂ) r k x-1‖ ≤ 40*k*q := by
  let Q : ℂ := -(q^2 : ℝ)
  have hQ : ‖Q‖ = q^2 := by simp only [Q, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  have hk0 : 0 < k := by linarith
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hc := jacobiNormalization_small_bound hq0 hq hrl hru hroot
  have hr := jacobiRemainderProduct_square_bound hq0 hq hrl hru hQ hxl hxu
  have hd := jacobiPairProduct_annulus_inverse_bound hq0 hq hQ hxl hxu
  have hj := jacobiPairProduct_annulus_log_bound hq0 hq hQ hxl hxu
  have hz : ‖-2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x‖ ≤ 8*k*q := by
    have he : -2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x =
        (-(2*k : ℝ) : ℂ)*(x*logDeriv (jacobiPairProduct Q) x) := by push_cast; ring
    rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*k)]
    nlinarith [mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ 2*k)]
  have hexp : ‖Complex.exp (-2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x)-1‖ ≤ 16*k*q := by
    have h := Complex.norm_exp_sub_one_le (hz.trans (by linarith : 8*k*q ≤ 1))
    linarith
  have hf := four_factors_sub_one_norm_le hc hr hd hexp
  let u : ℝ := 20*q+11*q^2+12*q+16*k*q
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ 19*k*q := by
    dsimp [u]
    nlinarith [mul_le_mul_of_nonneg_right hk.le hq0.le]
  have he := Real.abs_exp_sub_one_le (x := u) (by rw [abs_of_nonneg hu0]; linarith)
  have he' := (le_abs_self (Real.exp u-1)).trans he
  rw [abs_of_nonneg hu0] at he'
  change ‖jacobiSmallCorrection Q r k x-1‖ ≤ 40*k*q
  change ‖jacobiNormalization Q r*(jacobiRemainderProduct Q r x)^2*
    ((jacobiPairProduct Q x)⁻¹)^2*Complex.exp (-2*(k : ℂ)*x*logDeriv (jacobiPairProduct Q) x)-1‖ ≤ _
  change _ ≤ Real.exp u-1 at hf
  nlinarith

noncomputable def jacobiLinearFactor (q B : ℝ) : ℂ := (1-q^2 : ℝ)-I*B

theorem jacobiLinearFactor_norm_sq {q B : ℝ} :
    ‖jacobiLinearFactor q B‖^2 = (1-q^2)^2+B^2 := by
  have hre : (jacobiLinearFactor q B).re = 1-q^2 := by
    change ((1-q^2 : ℝ) : ℂ).re-(I*(B : ℂ)).re = _
    rw [Complex.ofReal_re]
    simp only [Complex.mul_re, I_re, I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero]
  have him : (jacobiLinearFactor q B).im = -B := by
    change ((1-q^2 : ℝ) : ℂ).im-(I*(B : ℂ)).im = _
    rw [Complex.ofReal_im]
    simp only [Complex.mul_im, I_re, I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, one_mul, zero_sub]
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hre, him]
  ring

theorem jacobiLinearFactor_square_bound {q B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hB : 0 ≤ B) :
    ‖(jacobiLinearFactor q B)^2‖ ≤ 1+B^2 ∧
      ‖(jacobiLinearFactor q B)^2-1‖ ≤ 4*q^2+2*B+2*B^2 := by
  have hq2 : q^2 ≤ 1 := by nlinarith [sq_nonneg (1-q)]
  have hq4 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg q)
  constructor
  · rw [norm_pow, jacobiLinearFactor_norm_sq]
    nlinarith
  · have he : jacobiLinearFactor q B-1 = -(q^2 : ℝ)-I*B := by
      unfold jacobiLinearFactor
      push_cast
      ring
    have hn : ‖jacobiLinearFactor q B-1‖ ≤ q^2+B := by
      rw [he]
      have h := norm_sub_le (-(q^2 : ℝ) : ℂ) (I*B)
      simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq,
        norm_mul, Complex.norm_I, one_mul, abs_of_nonneg hB] using h
    have h := square_sub_one_norm_le hn
    nlinarith [sq_nonneg (q^2-B)]

theorem correction_times_linear_square_bound {q k B : ℝ} {G : ℂ}
    (hq0 : 0 < q) (hq : q ≤ 1/100000) (hk : 25/2 < k) (hkq : k*q < 1/10000)
    (hB : 0 ≤ B) (hG : ‖G-1‖ ≤ 40*k*q) :
    ‖G*(jacobiLinearFactor q B)^2-1‖ ≤ 100*k*q+4*B+3*B^2 := by
  have hL := jacobiLinearFactor_square_bound hq0.le (by linarith) hB
  have hmul := mul_le_mul hG hL.1 (norm_nonneg _) (by nlinarith : 0 ≤ 40*k*q)
  have hsum : ‖G*(jacobiLinearFactor q B)^2-1‖ ≤
      40*k*q*(1+B^2)+4*q^2+2*B+2*B^2 := by
    calc
      _ = ‖(G-1)*(jacobiLinearFactor q B)^2+((jacobiLinearFactor q B)^2-1)‖ := by congr 1; ring
      _ ≤ ‖G-1‖*‖(jacobiLinearFactor q B)^2‖+‖(jacobiLinearFactor q B)^2-1‖ := by
        exact (norm_add_le ((G-1)*(jacobiLinearFactor q B)^2)
          ((jacobiLinearFactor q B)^2-1)).trans_eq
          (congrArg (fun v : ℝ => v+‖(jacobiLinearFactor q B)^2-1‖)
            (norm_mul (G-1) ((jacobiLinearFactor q B)^2)))
      _ ≤ _ := by linarith
  have hq2 := mul_le_mul_of_nonneg_left hq hq0.le
  have hsmall : 4*q^2 ≤ 60*k*q := by
    nlinarith [mul_le_mul_of_nonneg_right hk.le hq0.le]
  have hquad := mul_le_mul_of_nonneg_right (show 40*k*q ≤ 1 by linarith) (sq_nonneg B)
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiSmallCorrection_bound
#print axioms TwoAxisHelicoid.correction_times_linear_square_bound
