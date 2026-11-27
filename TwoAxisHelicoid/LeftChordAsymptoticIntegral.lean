import TwoAxisHelicoid.LeftChordTailBounds
import TwoAxisHelicoid.LeftLaplaceMoments

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 1200000

theorem left_abs_integral_le_const {a b C : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ∀ v ∈ Icc a b, |f v| ≤ C) : |∫ v : ℝ in a..b, f v| ≤ (b-a)*C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := f) (C := C) (fun v hv => by
      rw [uIoc_of_le hab] at hv
      simpa only [Real.norm_eq_abs] using hf v ⟨hv.1.le,hv.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using h

theorem leftChordRealKernel_negative_integral_remainder {κ h : ℝ}
    (hκ : 1 ≤ κ) (hh : 0 < h) (hhu : h ≤ 1) :
    |(∫ v : ℝ in (-1)..0, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2)| ≤
      2*Real.exp κ/κ^3+5*κ*h^2*Real.exp κ+(κ+1)/(2*κ^2) := by
  have hκ0 : 0 < κ := by linarith
  have hc := leftChordRealKernel_continuous hh.ne' κ
  have hl : Continuous (fun v : ℝ => Real.exp (-κ*v)*((v+1)/2)) := by fun_prop
  have he1 : Continuous (fun v : ℝ => Real.exp (-κ*v)*(v+1)^2) := by fun_prop
  have he2 : Continuous (fun v : ℝ => (5*κ^2*h^2)*Real.exp (-κ*v)) := by fun_prop
  have hpoint (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0) :
      |leftChordRealKernel κ h v-Real.exp (-κ*v)*((v+1)/2)| ≤
        Real.exp (-κ*v)*(v+1)^2+(5*κ^2*h^2)*Real.exp (-κ*v) := by
    convert leftChordRealKernel_negative_remainder hκ hh.le hhu hv.1 hv.2 using 1
    ring
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1 : ℝ) ≤ 0)
    (((hc.sub hl).abs).intervalIntegrable (-1) 0) ((he1.add he2).intervalIntegrable (-1) 0) hpoint
  simp only [Pi.sub_apply,Pi.add_apply] at hm
  rw [intervalIntegral.integral_add (he1.intervalIntegrable (-1) 0) (he2.intervalIntegrable (-1) 0),
    intervalIntegral.integral_const_mul] at hm
  have hm' := add_le_add (left_integral_shifted_exp_quadratic_le hκ0)
    (mul_le_mul_of_nonneg_left (left_integral_shifted_exp_le hκ0) (by positivity : 0 ≤ 5*κ^2*h^2))
  have herr : |(∫ v : ℝ in (-1)..0, leftChordRealKernel κ h v)-
      (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*((v+1)/2))| ≤
      2*Real.exp κ/κ^3+5*κ*h^2*Real.exp κ := by
    rw [← intervalIntegral.integral_sub (hc.intervalIntegrable (-1) 0) (hl.intervalIntegrable (-1) 0)]
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (-1 : ℝ) ≤ 0)).trans
      (hm.trans (hm'.trans_eq ?_))
    field_simp [hκ0.ne']
  have hbase : |(∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*((v+1)/2))-
      Real.exp κ/(2*κ^2)| = (κ+1)/(2*κ^2) := by
    rw [left_integral_shifted_exp_linear hκ0]
    have hid : (Real.exp κ-κ-1)/(2*κ^2)-Real.exp κ/(2*κ^2) = -((κ+1)/(2*κ^2)) := by ring
    rw [hid,abs_neg,abs_of_nonneg (by positivity : 0 ≤ (κ+1)/(2*κ^2))]
  calc
    _ ≤ |(∫ v : ℝ in (-1)..0, leftChordRealKernel κ h v)-
        (∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*((v+1)/2))|+
        |(∫ v : ℝ in (-1)..0, Real.exp (-κ*v)*((v+1)/2))-Real.exp κ/(2*κ^2)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by rw [hbase]; exact add_le_add herr (le_refl _)

theorem leftChordRealKernel_end_strip_integral_bound {κ h k : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (hk : 0 ≤ k) (hku : k ≤ 1) (hsq : h^2+k^2=1) :
    |∫ v : ℝ in (-1)..(-k), leftChordRealKernel κ h v| ≤ Real.exp κ*(1+2*κ)*h^4 := by
  have hab : (-1 : ℝ) ≤ -k := by linarith
  have hb := left_abs_integral_le_const hab (fun v hv =>
    leftChordRealKernel_end_strip_bound hκ hh hk hsq hv.1 hv.2)
  have hwidth : 1-k ≤ h^2 := by nlinarith [mul_nonneg hk (sub_nonneg.mpr hku)]
  have hm := mul_le_mul_of_nonneg_right hwidth
    (show 0 ≤ Real.exp κ*((1+2*κ)*h^2) by positivity)
  calc
    _ ≤ ((-k)-(-1))*(Real.exp κ*((1+2*κ)*h^2)) := hb
    _ = (1-k)*(Real.exp κ*((1+2*κ)*h^2)) := by ring
    _ ≤ h^2*(Real.exp κ*((1+2*κ)*h^2)) := hm
    _ = _ := by ring

theorem leftChordRealKernel_positive_integral_bound {κ h k : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (hkl : 1/2 ≤ k) (hku : k ≤ 1) (hsq : h^2+k^2=1) :
    |∫ v : ℝ in (0)..k, leftChordRealKernel κ h v| ≤
      2+κ+Real.exp (-κ/2)*(1/h+2*κ) := by
  have hk : 0 ≤ k := by linarith
  have hc := leftChordRealKernel_continuous hh.ne' κ
  have hn := left_abs_integral_le_const (by norm_num : (0 : ℝ) ≤ 1/2) (fun v hv =>
    leftChordRealKernel_positive_near_bound hκ hh hk hsq hv.1 (hv.2.trans hkl) hv.2)
  have hf := left_abs_integral_le_const hkl (fun v hv =>
    leftChordRealKernel_positive_far_bound hκ hh hk hku hsq hv.1 hv.2)
  have hn' : |∫ v : ℝ in (0)..(1/2), leftChordRealKernel κ h v| ≤ 2+κ := by
    convert hn using 1
    ring
  have hf' : |∫ v : ℝ in (1/2)..k, leftChordRealKernel κ h v| ≤
      Real.exp (-κ/2)*(1/h+2*κ) := by
    refine hf.trans ?_
    have hm := mul_le_mul_of_nonneg_right (show k-1/2 ≤ 1 by linarith)
      (show 0 ≤ Real.exp (-κ/2)*(1/h+2*κ) by positivity)
    simpa only [one_mul] using hm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (0) (1/2))
    (hc.intervalIntegrable (1/2) k)]
  exact (abs_add_le _ _).trans (add_le_add hn' hf')

theorem leftChordRealKernel_integral_asymptotic_bound {κ h k : ℝ}
    (hκ : 1 ≤ κ) (hh : 0 < h) (hhu : h ≤ 1)
    (hkl : 1/2 ≤ k) (hku : k ≤ 1) (hsq : h^2+k^2=1) :
    |(∫ v : ℝ in (-k)..k, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2)| ≤
      2*Real.exp κ/κ^3+5*κ*h^2*Real.exp κ+(κ+1)/(2*κ^2)+
        Real.exp κ*(1+2*κ)*h^4+(2+κ+Real.exp (-κ/2)*(1/h+2*κ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hk : 0 ≤ k := by linarith
  have hc := leftChordRealKernel_continuous hh.ne' κ
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) (-k)) (hc.intervalIntegrable (-k) 0)
  have hwhole := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-k) 0) (hc.intervalIntegrable (0) k)
  have he : (∫ v : ℝ in (-k)..k, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2) =
      ((∫ v : ℝ in (-1)..0, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2))-
        (∫ v : ℝ in (-1)..(-k), leftChordRealKernel κ h v)+
        (∫ v : ℝ in (0)..k, leftChordRealKernel κ h v) := by linarith
  rw [he]
  have hn := leftChordRealKernel_negative_integral_remainder hκ hh hhu
  have hs := leftChordRealKernel_end_strip_integral_bound hκ0 hh hk hku hsq
  have hp := leftChordRealKernel_positive_integral_bound hκ0 hh hkl hku hsq
  exact (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) (le_refl _)).trans
    (add_le_add (add_le_add hn hs) hp))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordRealKernel_integral_asymptotic_bound
