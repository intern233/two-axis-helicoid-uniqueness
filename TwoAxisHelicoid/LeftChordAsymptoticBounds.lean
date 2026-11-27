import TwoAxisHelicoid.LeftChordKernel
import TwoAxisHelicoid.LeftChordBounds

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 1000000

theorem left_chord_negative_denominator {h v : ℝ} (hv : v ≤ 0) :
    1 ≤ h^2+(v-1)^2 := by
  nlinarith [sq_nonneg h, sq_nonneg v]

theorem left_chord_negative_ratio_abs {h v : ℝ} (hh : h ≤ 1) (hh0 : 0 ≤ h)
    (hvl : -1 ≤ v) (hvu : v ≤ 0) :
    |(1-h^2-v^2)/(h^2+(v-1)^2)| ≤ 1 := by
  have hd := left_chord_negative_denominator (h := h) hvu
  have hv2 : v^2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ v+1) (neg_nonneg.mpr hvu)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  rw [abs_div, abs_of_pos (by linarith : 0 < h^2+(v-1)^2)]
  apply (div_le_iff₀ (by linarith : 0 < h^2+(v-1)^2)).mpr
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg h, sq_nonneg v]

theorem left_chord_negative_ratio_remainder {h v : ℝ}
    (hvl : -1 ≤ v) (hvu : v ≤ 0) :
    |(1-h^2-v^2)/(h^2+(v-1)^2)-(v+1)/2| ≤ (v+1)^2+2*h^2 := by
  have hd := left_chord_negative_denominator (h := h) hvu
  have hd0 : 0 < h^2+(v-1)^2 := by linarith
  have hw0 : 0 ≤ v+1 := by linarith
  have hw1 : v+1 ≤ 1 := by linarith
  have he : (1-h^2-v^2)/(h^2+(v-1)^2)-(v+1)/2 =
      ((v+1)^2*(1-(v+1)/2)-h^2*(1+(v+1)/2))/(h^2+(v-1)^2) := by
    field_simp [hd0.ne']
    ring
  have hA0 : 0 ≤ (v+1)^2*(1-(v+1)/2) := mul_nonneg (sq_nonneg _) (by linarith)
  have hA : (v+1)^2*(1-(v+1)/2) ≤ (v+1)^2 := by
    nlinarith only [mul_nonneg (sq_nonneg (v+1)) hw0]
  have hB0 : 0 ≤ h^2*(1+(v+1)/2) := mul_nonneg (sq_nonneg _) (by linarith)
  have hB : h^2*(1+(v+1)/2) ≤ 2*h^2 := by
    nlinarith only [mul_nonneg (sq_nonneg h) (show 0 ≤ 1-(v+1)/2 by linarith)]
  rw [he, abs_div, abs_of_pos hd0]
  calc
    _ ≤ |(v+1)^2*(1-(v+1)/2)-h^2*(1+(v+1)/2)| := div_le_self (abs_nonneg _) hd
    _ ≤ (v+1)^2+2*h^2 := by rw [abs_le]; constructor <;> linarith

theorem left_cos_sub_one_abs_le (x : ℝ) : |Real.cos x-1| ≤ x^2/2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem leftChordRealKernel_negative_remainder {κ h v : ℝ}
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hhu : h ≤ 1)
    (hvl : -1 ≤ v) (hvu : v ≤ 0) :
    |leftChordRealKernel κ h v-Real.exp (-κ*v)*((v+1)/2)| ≤
      Real.exp (-κ*v)*((v+1)^2+5*κ^2*h^2) := by
  have hd := left_chord_negative_denominator (h := h) hvu
  have hd0 : 0 < h^2+(v-1)^2 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hR := left_chord_negative_ratio_abs hhu hh hvl hvu
  have hE := left_chord_negative_ratio_remainder (h := h) hvl hvu
  have hcos := left_cos_sub_one_abs_le (κ*h)
  have hsin : |Real.sin (κ*h)| ≤ κ*h := by
    simpa only [abs_of_nonneg (mul_nonneg hκ0 hh)] using (Real.abs_sin_le_abs (x := κ*h))
  have hS : |2*h*Real.sin (κ*h)/(h^2+(v-1)^2)| ≤ 2*κ*h^2 := by
    rw [abs_div, abs_of_pos hd0, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*h)]
    calc
      _ ≤ 2*h*|Real.sin (κ*h)| := div_le_self (by positivity) hd
      _ ≤ 2*h*(κ*h) := mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = _ := by ring
  have hC : |((1-h^2-v^2)/(h^2+(v-1)^2))*(Real.cos (κ*h)-1)| ≤ κ^2*h^2/2 := by
    rw [abs_mul]
    calc
      _ ≤ 1*((κ*h)^2/2) := mul_le_mul hR hcos (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have he : ((1-h^2-v^2)*Real.cos (κ*h)+2*h*Real.sin (κ*h))/(h^2+(v-1)^2)-(v+1)/2 =
      ((1-h^2-v^2)/(h^2+(v-1)^2)-(v+1)/2)+
        ((1-h^2-v^2)/(h^2+(v-1)^2))*(Real.cos (κ*h)-1)+
        2*h*Real.sin (κ*h)/(h^2+(v-1)^2) := by ring
  have hbound : |((1-h^2-v^2)*Real.cos (κ*h)+2*h*Real.sin (κ*h))/(h^2+(v-1)^2)-(v+1)/2| ≤
      (v+1)^2+5*κ^2*h^2 := by
    rw [he]
    calc
      _ ≤ (|(1-h^2-v^2)/(h^2+(v-1)^2)-(v+1)/2|+
          |((1-h^2-v^2)/(h^2+(v-1)^2))*(Real.cos (κ*h)-1)|)+
          |2*h*Real.sin (κ*h)/(h^2+(v-1)^2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ ((v+1)^2+2*h^2)+κ^2*h^2/2+2*κ*h^2 := add_le_add (add_le_add hE hC) hS
      _ ≤ _ := by
        have hk2 : 1 ≤ κ^2 := by nlinarith
        have hk : κ ≤ κ^2 := by nlinarith
        nlinarith only [mul_le_mul_of_nonneg_right hk2 (sq_nonneg h),
          mul_le_mul_of_nonneg_right hk (sq_nonneg h), sq_nonneg (κ*h)]
  unfold leftChordRealKernel
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordRealKernel_negative_remainder
