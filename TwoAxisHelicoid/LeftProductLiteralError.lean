import TwoAxisHelicoid.LeftActualPeriod

namespace TwoAxisHelicoid
open Complex Set

/-- The real and imaginary parts of the squared factor retain the two
coefficients in the penultimate estimate of the proof of Lemma 7.3. -/
theorem jacobiLinearFactor_square_literal_error {q B : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hB : 0 ≤ B) :
    ‖(jacobiLinearFactor q B)^2-1‖ ≤ 2*q^2+2*B+B^2 := by
  let a := 1-q^2
  let L := jacobiLinearFactor q B
  have ha : 0 ≤ a := by
    dsimp [a]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]
  have ha1 : a ≤ 1 := by dsimp [a]; nlinarith [sq_nonneg q]
  have hre : L.re = a := by
    change ((1-q^2 : ℝ) : ℂ).re-(I*(B : ℂ)).re = 1-q^2
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero]
  have him : L.im = -B := by
    change ((1-q^2 : ℝ) : ℂ).im-(I*(B : ℂ)).im = -B
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add, zero_sub]
  have ere : (L^2-1).re = a^2-B^2-1 := by
    simp only [Complex.sub_re, pow_two, Complex.mul_re, hre, him, Complex.one_re]
    ring
  have eim : (L^2-1).im = -(2*a*B) := by
    simp only [Complex.sub_im, pow_two, Complex.mul_im, hre, him, Complex.one_im]
    ring
  have negre : a^2-B^2-1 ≤ 0 := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1), sq_nonneg B]
  have nonneg : 0 ≤ 2*a*B := by positivity
  have hnorm := Complex.norm_le_abs_re_add_abs_im (L^2-1)
  rw [ere, eim, abs_of_nonpos negre, abs_neg, abs_of_nonneg nonneg] at hnorm
  have hab : a*B ≤ B := by simpa using mul_le_mul_of_nonneg_right ha1 hB
  have hquad : 1-a^2 ≤ 2*q^2 := by dsimp [a]; nlinarith [sq_nonneg (q^2)]
  change ‖L^2-1‖ ≤ _
  linarith

private theorem product_error_of_factor_bounds {q B d : ℝ} {G : ℂ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hB : 0 ≤ B) (hG : ‖G-1‖ ≤ d) :
    ‖G*(jacobiLinearFactor q B)^2-1‖ ≤ d*(1+B^2)+2*q^2+2*B+B^2 := by
  let L := jacobiLinearFactor q B
  have hL := (jacobiLinearFactor_square_bound hq hq1 hB).1
  have hdelta := jacobiLinearFactor_square_literal_error hq hq1 hB
  have hmul := mul_le_mul hG hL (norm_nonneg _) ((norm_nonneg _).trans hG)
  calc
    _ = ‖(G-1)*L^2+(L^2-1)‖ := by dsimp [L]; congr 1; ring
    _ ≤ ‖(G-1)*L^2‖+‖L^2-1‖ := norm_add_le _ _
    _ = ‖G-1‖*‖L^2‖+‖L^2-1‖ := by rw [norm_mul]
    _ ≤ d*(1+B^2)+(2*q^2+2*B+B^2) := add_le_add hmul hdelta
    _ = _ := by ring

/-- The actual Jacobi correction on the annulus of Lemma 7.3, with the
literal constants in the final display of its proof. -/
theorem left_product_literal_error_on_annulus {t ρ : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hρl : leftNome t ≤ ρ) (hρu : ρ ≤ (leftNome t)⁻¹) :
    ‖jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t) (I*ρ)-1‖ ≤
      40*leftKappa t*leftNome t*(1+(leftProductB t ρ)^2)+
        2*(leftNome t)^2+2*leftProductB t ρ+(leftProductB t ρ)^2 := by
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
  have hB : 0 ≤ leftProductB t ρ :=
    (add_pos (div_pos (leftBeta_pos t) hρ0) (mul_pos (leftRootR_pos t) hρ0)).le
  have hfinal := product_error_of_factor_bounds hq0.le (by linarith) hB hG
  rw [jacobiNome_inverse_eq_leftNome ht]
  have hQ : ‖(-((leftNome t)^2 : ℝ) : ℂ)‖ < 1 := by
    rw [← jacobiNome_inverse_eq_leftNome ht]
    exact jacobiNome_norm_lt_one (one_div_pos.mpr ht)
  rw [jacobiProductError_factor hQ, product_linear_factor_imaginary (leftRootR_pos t).ne' hρ0.ne']
  exact hfinal

/-- The same estimate at every point of the complete integration path,
including both endpoints. -/
theorem left_product_literal_error_full_path {t y : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    let B := leftProductB t (Real.exp (-Real.pi*y))
    ‖jacobiProductError (jacobiNome (1/t)) (leftRootR t) (leftKappa t)
      (jacobiExp ((1/2 : ℂ)+I*y))-1‖ ≤
      40*leftKappa t*leftNome t*(1+B^2)+2*(leftNome t)^2+2*B+B^2 := by
  dsimp only
  rw [jacobiExp_half_midline]
  obtain ⟨hl, hu⟩ := leftPathRho_bounds hy
  exact left_product_literal_error_on_annulus ht htu hl (by simpa only [one_div] using hu)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiLinearFactor_square_literal_error
#print axioms TwoAxisHelicoid.left_product_literal_error_on_annulus
#print axioms TwoAxisHelicoid.left_product_literal_error_full_path
