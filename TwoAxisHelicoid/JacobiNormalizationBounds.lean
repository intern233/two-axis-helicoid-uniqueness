import TwoAxisHelicoid.JacobiRemainderBounds
import TwoAxisHelicoid.JacobiRatioIdentity

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiRemainderProduct

theorem mul_sub_one_norm_le {u v : ℂ} {d e : ℝ}
    (hu : ‖u-1‖ ≤ d) (hv : ‖v-1‖ ≤ e) :
    ‖u*v-1‖ ≤ d*(1+e)+e := by
  have hd : 0 ≤ d := (norm_nonneg _).trans hu
  have hv' : ‖v‖ ≤ 1+e := by
    have h := norm_le_norm_sub_add v (1 : ℂ)
    norm_num only [norm_one] at h
    linarith
  calc
    ‖u*v-1‖ = ‖(u-1)*v+(v-1)‖ := by congr 1; ring
    _ ≤ ‖u-1‖*‖v‖+‖v-1‖ := by simpa only [norm_mul] using norm_add_le ((u-1)*v) (v-1)
    _ ≤ d*(1+e)+e := add_le_add (mul_le_mul hu hv' (norm_nonneg v) hd) hv

theorem jacobiNormalization_small_bound {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100000)
    (hrl : q/2 ≤ r) (hru : r ≤ q)
    (hroot : 0 ≤ q^2/r-r ∧ q^2/r-r ≤ 12*q^2) :
    ‖jacobiNormalization (-(q^2 : ℝ) : ℂ) r-1‖ ≤ 20*q := by
  let Q : ℂ := -(q^2 : ℝ)
  let R : ℂ := jacobiRemainderProduct Q r 1
  let c : ℝ := 1+q^2/r-r-q^2
  have hr0 : 0 < r := by linarith
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  have hQ : ‖Q‖ = q^2 := by simp only [Q, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  have hQ1 : ‖Q‖ < 1 := by rw [hQ]; nlinarith
  have hR : ‖R-1‖ ≤ 5*q^2 := by
    apply jacobiRemainderProduct_annulus_bound hq0 hq hrl hru hQ
    · rw [norm_one]
      linarith
    · rw [norm_one, ← one_div]
      apply (le_div_iff₀ hq0).mpr
      linarith
  have hc : ‖(c : ℂ)-1‖ ≤ 13*q^2 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    dsimp [c]
    constructor <;> linarith [sq_nonneg q]
  have hM : ‖(c : ℂ)*R-1‖ ≤ 19*q^2 := by
    have h := mul_sub_one_norm_le hc hR
    have hcap : q^2 ≤ 1/65 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg q)]
  have hInv : ‖(((c : ℂ)*R)⁻¹)^2-1‖ ≤ 57*q^2 := by
    have h := inverse_square_sub_one_norm_le hM (by nlinarith : 19*q^2 ≤ 1/100)
    linarith
  have hP := jacobiFactorProduct_fourth_power_bound hq0 hq hQ
  have hfinal := mul_sub_one_norm_le hP hInv
  have hden : (1-(r : ℂ))*jacobiPairProduct Q r = (c : ℂ)*R := by
    have he := jacobiPairProduct_remainder (r := (r : ℂ)) (x := (1 : ℂ)) hQ1
    simp only [mul_one] at he
    rw [he]
    dsimp only [c, R, Q]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr0.ne']
    ring
  have he : jacobiNormalization Q r = (jacobiFactorProduct Q 1)^4*(((c : ℂ)*R)⁻¹)^2 := by
    unfold jacobiNormalization
    rw [← mul_pow, hden, div_eq_mul_inv, inv_pow]
  change ‖jacobiNormalization Q r-1‖ ≤ _
  rw [he]
  have hcap : q^2 ≤ 1/513 := by nlinarith
  have hq4 := mul_le_mul_of_nonneg_left hcap (sq_nonneg q)
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiNormalization_small_bound
