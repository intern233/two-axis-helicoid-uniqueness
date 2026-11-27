import TwoAxisHelicoid.LeftChordKernel
import TwoAxisHelicoid.LeftChordBounds

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 800000

theorem leftChordRealKernel_nonneg {κ h k v : ℝ}
    (hκ0 : 0 ≤ κ*h) (hκh : κ*h ≤ 1/10) (hh : 0 ≤ h)
    (hsq : h^2+k^2 = 1) (hv : v ∈ Icc (-k) k) :
    0 ≤ leftChordRealKernel κ h v := by
  have htrig := left_chord_trig_bounds hκ0 hκh
  have hv2 : v^2 ≤ k^2 := by
    nlinarith [mul_nonneg (show 0 ≤ v+k by linarith [hv.1])
      (show 0 ≤ k-v by linarith [hv.2])]
  have hA : 0 ≤ 1-h^2-v^2 := by linarith
  unfold leftChordRealKernel
  exact mul_nonneg (Real.exp_pos _).le (div_nonneg
    (add_nonneg (mul_nonneg hA (by linarith [htrig.1]))
      (mul_nonneg (by positivity) htrig.2)) (by positivity))

theorem leftChordRealKernel_subinterval_lower {κ h k v : ℝ}
    (hκ : 25/2 < κ) (hh : 0 < h) (hk : 0 ≤ k)
    (hsq : h^2+k^2 = 1) (hκh : κ*h ≤ 1/10)
    (hv : v ∈ Icc (-1+1/(2*κ)) (-1+2/κ)) :
    (27/320 : ℝ)*(Real.exp κ/κ) < leftChordRealKernel κ h v := by
  have hκ0 : 0 < κ := by linarith
  have hb := left_chord_parameter_estimates hκ hh hk hsq hκh
  have hξ := left_chord_subinterval_estimates hκ hb.2.2.1 hv.1 hv.2
  have htrig := left_chord_trig_bounds (mul_pos hκ0 hh).le hκh
  have hr := left_chord_ratio_lower hh hξ.1 hξ.2.1 hξ.2.2 htrig.1 htrig.2
  rw [show -1+(v+1) = v by ring] at hr
  have hm := mul_le_mul_of_nonneg_left hr (Real.exp_pos (-κ*v)).le
  have he := mul_lt_mul_of_pos_left (shifted_exponential_lower hκ0 hv.1 hv.2)
    (by norm_num : (0 : ℝ) < 27/80)
  calc
    (27/320 : ℝ)*(Real.exp κ/κ) = (27/80)*(Real.exp κ/(4*κ)) := by ring
    _ < Real.exp (-κ*v)*((27/80)*(v+1)) := by
      convert he using 1
      ring
    _ ≤ leftChordRealKernel κ h v := hm

theorem leftChordRealKernel_integral_lower {κ h k : ℝ}
    (hκ : 25/2 < κ) (hh : 0 < h) (hk : 0 ≤ k)
    (hsq : h^2+k^2 = 1) (hκh : κ*h ≤ 1/10) :
    Real.exp κ/(8*κ^2) ≤ ∫ v : ℝ in (-k)..k, leftChordRealKernel κ h v := by
  have hκ0 : 0 < κ := by linarith
  have hb := left_chord_parameter_estimates hκ hh hk hsq hκh
  have hab : -1+1/(2*κ) ≤ -1+2/κ := by
    have hd : 1/(2*κ) ≤ 2/κ := by
      apply (div_le_div_iff₀ (show 0 < 2*κ by positivity) hκ0).mpr
      linarith
    linarith only [hd]
  have hc := leftChordRealKernel_continuous hh.ne' κ
  have hpoint (v : ℝ) (hv : v ∈ Icc (-1+1/(2*κ)) (-1+2/κ)) :
      (27/320 : ℝ)*(Real.exp κ/κ) ≤ leftChordRealKernel κ h v :=
    (leftChordRealKernel_subinterval_lower hκ hh hk hsq hκh hv).le
  have hl := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    (hc.intervalIntegrable _ _) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl
  have he : ((-1+2/κ)-(-1+1/(2*κ)))*((27/320)*(Real.exp κ/κ)) =
      (81/640)*(Real.exp κ/κ^2) := by field_simp [hκ0.ne']; ring
  rw [he] at hl
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (-k) k)] leftChordRealKernel κ h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact leftChordRealKernel_nonneg (mul_pos hκ0 hh).le hκh hh.le hsq ⟨hv.1.le,hv.2⟩
  have hmono := intervalIntegral.integral_mono_interval hb.2.2.2.1 hab hb.2.2.2.2 hn
    (hc.intervalIntegrable (-k) k)
  have hbase : Real.exp κ/(8*κ^2) ≤ (81/640)*(Real.exp κ/κ^2) := by
    rw [show Real.exp κ/(8*κ^2) = (1/8)*(Real.exp κ/κ^2) by ring]
    have hp : 0 ≤ Real.exp κ/κ^2 := by positivity
    nlinarith
  exact hbase.trans (hl.trans hmono)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordRealKernel_integral_lower
