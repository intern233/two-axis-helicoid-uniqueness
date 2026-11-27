import TwoAxisHelicoid.LeftKernelExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 800000

theorem left_chord_trig_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/10) :
    (9/10 : ℝ) ≤ Real.cos x ∧ 0 ≤ Real.sin x := by
  constructor
  · have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_gt_three])

theorem left_chord_ratio_lower {h ξ c s : ℝ} (hh : 0 < h)
    (hξ0 : 0 < ξ) (hξu : ξ ≤ 1/4) (hhξ : h^2 ≤ ξ/4)
    (hc : 9/10 ≤ c) (hs : 0 ≤ s) :
    (27/80 : ℝ)*ξ ≤
      ((1-h^2-(-1+ξ)^2)*c+2*h*s)/(h^2+(-1+ξ-1)^2) := by
  have hξsq : ξ^2 ≤ ξ/4 := by
    nlinarith [mul_nonneg hξ0.le (sub_nonneg.mpr hξu)]
  have hA : (3/2 : ℝ)*ξ ≤ 1-h^2-(-1+ξ)^2 := by nlinarith
  have hA0 : 0 ≤ 1-h^2-(-1+ξ)^2 := by nlinarith
  have hm := mul_le_mul hA hc (by norm_num : (0 : ℝ) ≤ 9/10) hA0
  have hn : (27/20 : ℝ)*ξ ≤ (1-h^2-(-1+ξ)^2)*c+2*h*s := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2*h by positivity) hs]
  have hd0 : 0 < h^2+(-1+ξ-1)^2 := by positivity
  have hd4 : h^2+(-1+ξ-1)^2 ≤ 4 := by nlinarith
  apply (le_div_iff₀ hd0).mpr
  have hb := mul_le_mul_of_nonneg_left hd4 (show (0 : ℝ) ≤ (27/80)*ξ by positivity)
  nlinarith

theorem left_chord_parameter_estimates {κ h k : ℝ} (hκ : 25/2 < κ) (hh : 0 < h)
    (hk : 0 ≤ k) (hsq : h^2+k^2 = 1) (hκh : κ*h ≤ 1/10) :
    h ≤ 1/10 ∧ k ≤ 1 ∧ h^2 ≤ 1/(8*κ) ∧
      -k ≤ -1+1/(2*κ) ∧ -1+2/κ ≤ k := by
  have hκ0 : 0 < κ := by linarith
  have hhsmall : h ≤ 1/10 := by nlinarith
  have hku : k ≤ 1 := by nlinarith [sq_nonneg h]
  have hprod : κ*h*h ≤ (1/100 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hκh hh.le
    nlinarith
  have hh2 : h^2 ≤ 1/(8*κ) := by
    apply (le_div_iff₀ (show 0 < 8*κ by positivity)).mpr
    nlinarith
  have hdiff : 1-k ≤ h^2 := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hku)]
  have hhalf : h^2 ≤ 1/(2*κ) := by
    apply (le_div_iff₀ (show 0 < 2*κ by positivity)).mpr
    nlinarith
  refine ⟨hhsmall,hku,hh2,by linarith,?_⟩
  have htwo : 2/κ ≤ 1 := (div_le_one hκ0).mpr (by linarith)
  linarith

theorem left_chord_subinterval_estimates {κ h v : ℝ} (hκ : 25/2 < κ)
    (hh2 : h^2 ≤ 1/(8*κ)) (hvl : -1+1/(2*κ) ≤ v) (hvu : v ≤ -1+2/κ) :
    0 < v+1 ∧ v+1 ≤ 1/4 ∧ h^2 ≤ (v+1)/4 := by
  have hκ0 : 0 < κ := by linarith
  have hl : 1/(2*κ) ≤ v+1 := by linarith
  have hu : v+1 ≤ 2/κ := by linarith
  have hsmall : 2/κ ≤ 1/4 := (div_le_iff₀ hκ0).mpr (by linarith)
  have he : 1/(8*κ) = (1/(2*κ))/4 := by ring
  rw [he] at hh2
  refine ⟨lt_of_lt_of_le (by positivity : 0 < 1/(2*κ)) hl, hu.trans hsmall, ?_⟩
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_chord_ratio_lower
#print axioms TwoAxisHelicoid.left_chord_parameter_estimates
