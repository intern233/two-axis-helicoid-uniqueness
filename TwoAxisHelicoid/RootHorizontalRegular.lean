import TwoAxisHelicoid.RootHorizontalTail
import TwoAxisHelicoid.RootVerticalConstants
import TwoAxisHelicoid.ThetaPeriodIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace TwoAxisHelicoid

theorem im_le_sineJet_norm {v : ℂ} (hv : 0 ≤ v.im) : v.im ≤ ‖sineJet 0 v‖ := by
  have hn : ‖sineJet 0 v‖ = ‖Complex.exp (v*Complex.I)-Complex.exp (-v*Complex.I)‖/2 := by
    simp [sineJet]
  have hr : Real.exp v.im-Real.exp (-v.im) ≤
      ‖Complex.exp (v*Complex.I)-Complex.exp (-v*Complex.I)‖ := by
    simpa only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_sub, mul_one, neg_neg, norm_sub_rev] using
      norm_sub_norm_le (Complex.exp (-v*Complex.I)) (Complex.exp (v*Complex.I))
  calc
    v.im ≤ Real.sinh v.im := Real.self_le_sinh_iff.mpr hv
    _ ≤ ‖sineJet 0 v‖ := by
      rw [Real.sinh_eq, hn]
      exact div_le_div_of_nonneg_right hr (by norm_num)

theorem root_height_bounds {t : ℝ} (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    (86/100 : ℝ) ≤ t ∧ t ≤ 87/100 := by
  constructor <;> norm_num [rootTLower, rootTUpper] at * <;> linarith

theorem root_horizontal_argument_im {t : ℝ} (htl : (rootTLower : ℝ) ≤ t)
    (htu : t ≤ (rootTUpper : ℝ)) (x : ℝ) :
    64/100 ≤ (Real.pi*((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))/2).im ∧
      (Real.pi*((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))/2).im ≤ 69/100 := by
  have ht := root_height_bounds htl htu
  have he : (Real.pi*((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))/2).im = Real.pi*t/4 := by
    simp [Complex.mul_im, Complex.mul_re, Complex.div_ofNat_im]
    ring
  rw [he]
  constructor
  · nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le)
      (sub_nonneg.mpr ht.1)]
  · nlinarith [Real.pi_lt_d2, mul_nonneg (sub_nonneg.mpr Real.pi_lt_d2.le)
      (sub_nonneg.mpr ht.2)]

theorem root_horizontal_regular {t : ℝ} (htl : (rootTLower : ℝ) ≤ t)
    (htu : t ≤ (rootTUpper : ℝ)) (x : ℝ) :
    (x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ) ∈ thetaRegular t := by
  let v : ℂ := Real.pi*((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ))/2
  have hi := root_horizontal_argument_im htl htu x
  have hi0 : 0 ≤ v.im := by dsimp [v]; linarith [hi.1]
  have his : |v.im| ≤ 69/100 := by rw [abs_of_nonneg hi0]; exact hi.2
  have he : thetaPartial t 0 1 v = sineJet 0 v := by
    simp [thetaPartial, thetaTerm, thetaSign]
  have htail := root_horizontal_sine_remainder (root_height_bounds htl htu).1 his
  rw [he] at htail
  change thetaJet t 0 v ≠ 0
  intro hzero
  rw [hzero, zero_sub, norm_neg] at htail
  have hnorm := im_le_sineJet_norm hi0
  linarith [hi.1]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_horizontal_regular
