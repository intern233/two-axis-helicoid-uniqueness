import TwoAxisHelicoid.LeftComparisonPath

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA thetaA dualThetaA

noncomputable def leftActualPathDifferential (t y : ℝ) : ℂ :=
  I*(I*(t : ℂ)*dualThetaA t (verticalA t) (leftPathW y))

theorem actualPeriodAlong_eq_left_path {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    actualPeriodAlong t =
      -(∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), leftActualPathDifferential t y).re := by
  have hsub := intervalIntegral.integral_comp_div
    (fun y : ℝ => dualThetaA t (verticalA t) (leftPathW y)) ht.1.ne'
    (a := (-1/2 : ℝ)) (b := (1/2 : ℝ))
  have he (y : ℝ) : leftActualPathDifferential t y =
      -(t : ℂ)*dualThetaA t (verticalA t) (leftPathW y) := by
    unfold leftActualPathDifferential
    simp only [← mul_assoc]
    rw [← pow_two, I_sq, neg_one_mul]
  simp only [div_div, neg_div, Complex.real_smul] at hsub
  rw [actualPeriodAlong_eq_dual ht]
  change (∫ x : ℝ in (-1/2)..(1/2), dualThetaA t (verticalA t) (leftPathW (x/t))).re = _
  simp only [neg_div]
  rw [hsub]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, neg_mul, Complex.neg_re, neg_neg]

theorem leftActualPathDifferential_continuous {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) : Continuous (leftActualPathDifferential t) := by
  have ha := (verticalA_spec ht).1
  have hreg := real_not_mem_rhombic_lattice_of_pos ht.1 ha.1 (by linarith [ha.2])
  have he (y : ℝ) : dualThetaA t (verticalA t) (leftPathW y) =
      thetaA t (verticalA t) (((-(t*y) : ℝ) : ℂ)+I*((t/2 : ℝ) : ℂ)) := by
    have h := dualThetaA_midline ht.1 hreg (t*y)
    have hdiv : t*y/t = y := by field_simp [ht.1.ne']
    rw [hdiv] at h
    exact h
  have hc := (horizontal_integrand_continuous ht.1 (verticalA t)).comp
    (by fun_prop : Continuous (fun y : ℝ => -(t*y)))
  unfold leftActualPathDifferential
  simp_rw [he]
  exact continuous_const.mul (continuous_const.mul hc)

theorem leftPathRho_bounds {t y : ℝ}
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    leftNome t ≤ Real.exp (-Real.pi*y) ∧ Real.exp (-Real.pi*y) ≤ 1/leftNome t := by
  constructor
  · unfold leftNome
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hy.2 (neg_nonpos.mpr Real.pi_pos.le)
    convert h using 1
    ring
  · unfold leftNome
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hy.1 (neg_nonpos.mpr Real.pi_pos.le)
    convert h using 1
    ring

theorem leftPath_product_region {t y : ℝ} (ht : 0 < t)
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    ‖jacobiNome (1/t)‖*‖jacobiExp (leftPathW y)‖ < 1 ∧
      ‖jacobiNome (1/t)‖*‖(jacobiExp (leftPathW y))⁻¹‖ < 1 := by
  have hq0 := leftNome_pos t
  have hq1 : leftNome t < 1 := by
    unfold leftNome
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (by positivity)
  have hρ := leftPathRho_bounds hy
  have hx : ‖jacobiExp (leftPathW y)‖ = Real.exp (-Real.pi*y) := by
    rw [leftPathW, jacobiExp_half_midline]
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hQ : ‖jacobiNome (1/t)‖ = (leftNome t)^2 := by
    rw [jacobiNome_inverse_eq_leftNome ht]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  rw [hQ, norm_inv, hx]
  constructor
  · have hm := mul_le_mul_of_nonneg_left hρ.2 (sq_nonneg (leftNome t))
    have he : (leftNome t)^2*(1/leftNome t) = leftNome t := by field_simp [hq0.ne']
    rw [he] at hm
    exact hm.trans_lt hq1
  · rw [← div_eq_mul_inv]
    apply lt_of_le_of_lt _ hq1
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρ.1 hq0.le]

theorem leftActualPath_error_norm_le {t y : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    ‖leftActualPathDifferential t y-I*leftComparisonFunction t (leftPathW y)‖ ≤
      ‖leftComparisonFunction t (leftPathW y)‖*
        (100*leftKappa t*leftNome t+4*leftProductB t (Real.exp (-Real.pi*y))+
          3*(leftProductB t (Real.exp (-Real.pi*y)))^2) := by
  have hreg := leftPath_product_region ht hy
  have hf := actual_dual_comparison_factorization ht htu (leftPathX_ne_one y) hreg.1 hreg.2
  have he : leftActualPathDifferential t y-I*leftComparisonFunction t (leftPathW y) =
      (I*leftComparisonFunction t (leftPathW y))*
        (jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t)
          (jacobiExp (leftPathW y))-1) := by
    unfold leftActualPathDifferential
    rw [hf]
    ring
  rw [he, norm_mul, norm_mul, norm_I, one_mul]
  exact mul_le_mul_of_nonneg_left (left_product_error_full_path ht htu hy.1 hy.2)
    (norm_nonneg _)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_eq_left_path
#print axioms TwoAxisHelicoid.leftActualPath_error_norm_le
