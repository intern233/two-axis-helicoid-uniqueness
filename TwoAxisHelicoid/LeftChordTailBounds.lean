import TwoAxisHelicoid.LeftChordAsymptoticBounds

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 1000000

theorem leftChordRealKernel_abs_le {κ h v : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) :
    |leftChordRealKernel κ h v| ≤ Real.exp (-κ*v)*
      ((|1-h^2-v^2|+2*κ*h^2)/(h^2+(v-1)^2)) := by
  have hd : 0 < h^2+(v-1)^2 := by positivity
  have hs : |Real.sin (κ*h)| ≤ κ*h := by
    simpa only [abs_of_nonneg (mul_nonneg hκ hh.le)] using
      (Real.abs_sin_le_abs (x := κ*h))
  have hc := Real.abs_cos_le_one (κ*h)
  have hn : |(1-h^2-v^2)*Real.cos (κ*h)+2*h*Real.sin (κ*h)| ≤
      |1-h^2-v^2|+2*κ*h^2 := by
    calc
      _ ≤ |1-h^2-v^2| * |Real.cos (κ*h)|+2*h*|Real.sin (κ*h)| := by
        convert abs_add_le ((1-h^2-v^2)*Real.cos (κ*h)) (2*h*Real.sin (κ*h)) using 1
        rw [abs_mul,abs_mul,abs_of_pos (by positivity : 0 < 2*h)]
      _ ≤ |1-h^2-v^2| * 1+2*h*(κ*h) :=
        add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hs (by positivity))
      _ = _ := by ring
  unfold leftChordRealKernel
  rw [abs_mul,abs_of_pos (Real.exp_pos _),abs_div,abs_of_pos hd]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hd.le) (Real.exp_pos _).le

theorem leftChordRealKernel_end_strip_bound {κ h k v : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (hk : 0 ≤ k) (hsq : h^2+k^2=1)
    (hvl : -1 ≤ v) (hvu : v ≤ -k) :
    |leftChordRealKernel κ h v| ≤ Real.exp κ*((1+2*κ)*h^2) := by
  have hv0 : v ≤ 0 := by linarith
  have hv2 : v^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ v+1 by linarith) (neg_nonneg.mpr hv0)]
  have hkv : k^2 ≤ v^2 := by
    nlinarith [mul_nonneg (show 0 ≤ -v-k by linarith) (show 0 ≤ -v+k by linarith)]
  have hn : |1-h^2-v^2| ≤ h^2 := by rw [abs_le]; constructor <;> nlinarith
  have hd := left_chord_negative_denominator (h := h) hv0
  have hd0 : 0 < h^2+(v-1)^2 := by linarith
  have hr : (|1-h^2-v^2|+2*κ*h^2)/(h^2+(v-1)^2) ≤ (1+2*κ)*h^2 := by
    calc
      _ ≤ |1-h^2-v^2|+2*κ*h^2 := div_le_self (by positivity) hd
      _ ≤ _ := by linarith
  have he : Real.exp (-κ*v) ≤ Real.exp κ := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hκ (show 0 ≤ v+1 by linarith)]
  exact (leftChordRealKernel_abs_le hκ hh).trans
    (mul_le_mul he hr (by positivity) (Real.exp_pos _).le)

theorem left_chord_positive_numerator {h k v : ℝ} (hk : 0 ≤ k)
    (hsq : h^2+k^2=1) (hv0 : 0 ≤ v) (hvk : v ≤ k) : 0 ≤ 1-h^2-v^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hvk) (show 0 ≤ k+v by linarith)]

theorem leftChordRealKernel_positive_near_bound {κ h k v : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (hk : 0 ≤ k) (hsq : h^2+k^2=1)
    (hv0 : 0 ≤ v) (hvk : v ≤ k) (hvu : v ≤ 1/2) :
    |leftChordRealKernel κ h v| ≤ 4+2*κ := by
  have hn := left_chord_positive_numerator hk hsq hv0 hvk
  have hd0 : 0 < h^2+(v-1)^2 := by positivity
  have hd : (1/4 : ℝ) ≤ h^2+(v-1)^2 := by nlinarith [sq_nonneg h,sq_nonneg (v-1/2)]
  have hr : (|1-h^2-v^2|+2*κ*h^2)/(h^2+(v-1)^2) ≤ 4+2*κ := by
    rw [abs_of_nonneg hn]
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [hd,sq_nonneg h,sq_nonneg v,mul_nonneg hκ (sq_nonneg (v-1))]
  have he : Real.exp (-κ*v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hb := mul_le_mul he hr (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using (leftChordRealKernel_abs_le hκ hh).trans hb

theorem leftChordRealKernel_positive_far_bound {κ h k v : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (hk : 0 ≤ k) (hku : k ≤ 1) (hsq : h^2+k^2=1)
    (hvl : 1/2 ≤ v) (hvk : v ≤ k) :
    |leftChordRealKernel κ h v| ≤ Real.exp (-κ/2)*(1/h+2*κ) := by
  have hv0 : 0 ≤ v := by linarith
  have hv1 : v ≤ 1 := hvk.trans hku
  have hn := left_chord_positive_numerator hk hsq hv0 hvk
  have hd0 : 0 < h^2+(v-1)^2 := by positivity
  have hratio : (1-h^2-v^2)/(h^2+(v-1)^2) ≤ 1/h := by
    apply (div_le_div_iff₀ hd0 hh).mpr
    have hnum : 1-h^2-v^2 ≤ 2*(1-v) := by nlinarith [sq_nonneg h,sq_nonneg (v-1)]
    have hm := mul_le_mul_of_nonneg_right hnum hh.le
    nlinarith only [hm,sq_nonneg (h-(1-v))]
  have hS : 2*κ*h^2/(h^2+(v-1)^2) ≤ 2*κ := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [mul_nonneg hκ (sq_nonneg (v-1))]
  have hr : (|1-h^2-v^2|+2*κ*h^2)/(h^2+(v-1)^2) ≤ 1/h+2*κ := by
    rw [abs_of_nonneg hn,add_div]
    exact add_le_add hratio hS
  have he : Real.exp (-κ*v) ≤ Real.exp (-κ/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hκ (show 0 ≤ v-1/2 by linarith)]
  exact (leftChordRealKernel_abs_le hκ hh).trans
    (mul_le_mul he hr (by positivity) (Real.exp_pos _).le)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordRealKernel_positive_far_bound
