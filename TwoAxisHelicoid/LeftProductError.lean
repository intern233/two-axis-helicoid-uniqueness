import TwoAxisHelicoid.JacobiProductErrorBounds
import TwoAxisHelicoid.LeftNumericalConstants

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiProductError

theorem leftEpsilon_eq_abscissa (t : ℝ) :
    leftEpsilon t = Real.pi*(verticalA t-1/2)/t := by
  unfold leftEpsilon leftNome leftRootR
  rw [← Real.exp_sub, Real.log_exp]
  ring

theorem leftBeta_eq_exp_kappa {t : ℝ} (ht : 0 < t) :
    leftBeta t = Real.exp (-dualProductKappa t (verticalA t)) := by
  unfold leftBeta leftRootR
  rw [leftNome_sq ht, ← Real.exp_sub]
  congr 1
  unfold dualProductKappa
  ring

theorem leftKappa_eq_dualProductKappa {t : ℝ} (ht : 0 < t) :
    leftKappa t = dualProductKappa t (verticalA t) := by
  rw [leftKappa, leftBeta_eq_exp_kappa ht, Real.log_exp, neg_neg]

theorem jacobiNome_inverse_eq_leftNome {t : ℝ} (ht : 0 < t) :
    jacobiNome (1/t) = (-((leftNome t)^2 : ℝ) : ℂ) := by
  rw [jacobiNome_eq_neg_exp, leftNome_sq ht]
  congr 2
  ring

theorem verticalA_sharp_small_upper {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    verticalA t ≤ 1/2+2*t*leftNome t := by
  have he := (leftEpsilon_bounds ht htu).2
  rw [leftEpsilon_eq_abscissa] at he
  have hmul := (div_le_iff₀ ht).mp he
  have ha := (verticalA_small_bounds ht htu).1
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sub_nonneg.mpr ha.le)
  nlinarith

noncomputable def leftProductB (t ρ : ℝ) : ℝ := leftBeta t/ρ+leftRootR t*ρ

theorem product_linear_factor_imaginary {q r ρ : ℝ} (hr : r ≠ 0) (hρ : ρ ≠ 0) :
    (1-(r : ℂ)*(I*ρ))*(1-(-(q^2 : ℝ) : ℂ)/((r : ℂ)*(I*ρ))) =
      jacobiLinearFactor q (q^2/r/ρ+r*ρ) := by
  unfold jacobiLinearFactor
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hr, Complex.ofReal_ne_zero.mpr hρ]
  ring_nf
  simp only [I_sq]
  ring

/-- Manuscript Lemma 7.3 on the complete annulus swept by the dual path. -/
theorem left_product_error_bound {t ρ : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hρl : leftNome t ≤ ρ) (hρu : ρ ≤ (leftNome t)⁻¹) :
    ‖jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t) (I*ρ)-1‖ ≤
      100*leftKappa t*leftNome t+4*leftProductB t ρ+3*(leftProductB t ρ)^2 := by
  have hq0 := leftNome_pos t
  have hq := (leftNome_lt_ten_neg_five ht htu).le
  have hr := leftRootR_bounds ht (by linarith)
  have hroot := leftBeta_sub_r_bounds ht (by linarith)
  have hk := leftKappa_gt ht htu
  have hkq := leftKappa_mul_nome_lt ht htu
  have hρ0 : 0 < ρ := hq0.trans_le hρl
  have hx : ‖(I*(ρ : ℂ))‖ = ρ := by
    rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hG := jacobiSmallCorrection_bound hq0 hq hr.1.le hr.2.le hroot hk hkq
    (x := I*ρ) (by rwa [hx]) (by rwa [hx])
  have hB : 0 ≤ leftProductB t ρ := by
    exact (add_pos (div_pos (leftBeta_pos t) hρ0) (mul_pos (leftRootR_pos t) hρ0)).le
  have hfinal := correction_times_linear_square_bound hq0 hq hk hkq hB hG
  rw [jacobiNome_inverse_eq_leftNome ht]
  have hQ : ‖(-((leftNome t)^2 : ℝ) : ℂ)‖ < 1 := by
    rw [← jacobiNome_inverse_eq_leftNome ht]
    exact jacobiNome_norm_lt_one (one_div_pos.mpr ht)
  rw [jacobiProductError_factor hQ, product_linear_factor_imaginary (leftRootR_pos t).ne' hρ0.ne']
  exact hfinal

theorem jacobiExp_half_midline (y : ℝ) :
    jacobiExp ((1/2 : ℂ)+I*y) = I*(Real.exp (-Real.pi*y) : ℂ) := by
  unfold jacobiExp
  have he : I*(Real.pi : ℂ)*((1/2 : ℂ)+I*y) = Real.pi/2*I+(-Real.pi*y : ℝ) := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.ofReal_exp]

theorem left_product_error_full_path {t y : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hyl : -(1/(2*t)) ≤ y) (hyu : y ≤ 1/(2*t)) :
    ‖jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t)
      (jacobiExp ((1/2 : ℂ)+I*y))-1‖ ≤
      100*leftKappa t*leftNome t+4*leftProductB t (Real.exp (-Real.pi*y))+
        3*(leftProductB t (Real.exp (-Real.pi*y)))^2 := by
  rw [jacobiExp_half_midline]
  apply left_product_error_bound ht htu
  · unfold leftNome
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hyu (neg_nonpos.mpr Real.pi_pos.le)
    convert h using 1
    ring
  · unfold leftNome
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hyl (neg_nonpos.mpr Real.pi_pos.le)
    convert h using 1
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_sharp_small_upper
#print axioms TwoAxisHelicoid.left_product_error_full_path
