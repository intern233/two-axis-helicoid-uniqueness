import TwoAxisHelicoid.JacobiProductEstimates

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 400000

theorem exp_sub_one_le_add_sq {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u-1 ≤ u+u^2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := u)
    (by simpa only [abs_of_nonneg hu] using hu1))).2
  linarith

theorem square_sub_one_norm_le {z : ℂ} {d : ℝ} (h : ‖z-1‖ ≤ d) :
    ‖z^2-1‖ ≤ d*(2+d) := by
  have hd : 0 ≤ d := (norm_nonneg _).trans h
  have hz : ‖z‖ ≤ 1+d := by
    have hn := norm_le_norm_sub_add z (1 : ℂ)
    norm_num only [norm_one] at hn
    linarith
  have hp : ‖z+1‖ ≤ 2+d := by
    have hn := norm_add_le z (1 : ℂ)
    norm_num only [norm_one] at hn
    linarith
  calc
    ‖z^2-1‖ = ‖(z-1)*(z+1)‖ := by congr 1; ring
    _ = ‖z-1‖*‖z+1‖ := norm_mul _ _
    _ ≤ d*(2+d) := mul_le_mul h hp (norm_nonneg _) hd

theorem inverse_square_sub_one_norm_le {z : ℂ} {d : ℝ}
    (h : ‖z-1‖ ≤ d) (hd : d ≤ 1/100) :
    ‖(z⁻¹)^2-1‖ ≤ 3*d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans h
  have hd1 : 0 < 1-d := by linarith
  have hzlower : 1-d ≤ ‖z‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) z
    rw [norm_sub_rev] at hn
    norm_num only [norm_one] at hn
    linarith
  have hz : z ≠ 0 := norm_pos_iff.mp (hd1.trans_le hzlower)
  have he : (z⁻¹)^2-1 = -(z^2-1)/z^2 := by field_simp; ring
  rw [he, norm_div, norm_neg, norm_pow]
  have hsq : (1-d)^2 ≤ ‖z‖^2 := sq_le_sq₀ hd1.le (norm_nonneg _) |>.mpr hzlower
  have hn := square_sub_one_norm_le h
  have hb : d*(2+d) ≤ 3*d*(1-d)^2 := by
    have hc : 2+d ≤ 3*(1-d)^2 := by nlinarith [sq_nonneg d]
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hc)]
  calc
    ‖z^2-1‖/‖z‖^2 ≤ (d*(2+d))/‖z‖^2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ ≤ (d*(2+d))/(1-d)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd1) hsq
    _ ≤ 3*d := (div_le_iff₀ (sq_pos_of_pos hd1)).mpr hb

theorem four_factors_sub_one_norm_le {z₀ z₁ z₂ z₃ : ℂ} {d₀ d₁ d₂ d₃ : ℝ}
    (h₀ : ‖z₀-1‖ ≤ d₀) (h₁ : ‖z₁-1‖ ≤ d₁)
    (h₂ : ‖z₂-1‖ ≤ d₂) (h₃ : ‖z₃-1‖ ≤ d₃) :
    ‖z₀*z₁*z₂*z₃-1‖ ≤ Real.exp (d₀+d₁+d₂+d₃)-1 := by
  let f : Fin 4 → ℂ := ![z₀-1,z₁-1,z₂-1,z₃-1]
  have h := Finset.norm_prod_one_add_sub_one_le Finset.univ f
  have hp : (∏ i : Fin 4, (1+f i)) = z₀*z₁*z₂*z₃ := by
    simp [f, Fin.prod_univ_succ, mul_assoc]
  rw [hp] at h
  have hs : (∑ i : Fin 4, ‖f i‖) ≤ d₀+d₁+d₂+d₃ := by
    simp only [f, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    linarith
  exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hs) 1)

theorem jacobi_two_products_sub_one_norm_le {q : ℂ} (hq : ‖q‖ < 1) (x y : ℂ) :
    ‖jacobiFactorProduct q x*jacobiFactorProduct q y-1‖ ≤
      Real.exp (‖q‖*‖x‖/(1-‖q‖)+‖q‖*‖y‖/(1-‖q‖))-1 := by
  let u := jacobiFactorProduct q x
  let v := jacobiFactorProduct q y
  let A := ‖q‖*‖x‖/(1-‖q‖)
  let B := ‖q‖*‖y‖/(1-‖q‖)
  have ha : ‖u-1‖ ≤ Real.exp A-1 := jacobiFactorProduct_sub_one_norm_le hq x
  have hb : ‖v-1‖ ≤ Real.exp B-1 := jacobiFactorProduct_sub_one_norm_le hq y
  have hA : 0 ≤ Real.exp A-1 := (norm_nonneg (u-1)).trans ha
  have hv : ‖v‖ ≤ Real.exp B := by
    have hv' := norm_le_norm_sub_add v (1 : ℂ)
    norm_num only [norm_one] at hv'
    linarith
  have hm := mul_le_mul ha hv (norm_nonneg v) hA
  change ‖u*v-1‖ ≤ Real.exp (A+B)-1
  calc
    ‖u*v-1‖ = ‖(u-1)*v+(v-1)‖ := by congr 1; ring
    _ ≤ ‖u-1‖*‖v‖+‖v-1‖ := by simpa only [norm_mul] using norm_add_le ((u-1)*v) (v-1)
    _ ≤ (Real.exp A-1)*Real.exp B+(Real.exp B-1) := add_le_add hm hb
    _ = Real.exp (A+B)-1 := by rw [Real.exp_add]; ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.inverse_square_sub_one_norm_le
#print axioms TwoAxisHelicoid.four_factors_sub_one_norm_le
