import TwoAxisHelicoid.LeftMobiusComparison

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000

noncomputable def leftArcPoint (r : ℝ) : ℂ :=
  ⟨2*r/(1+r^2), (r^2-1)/(1+r^2)⟩

noncomputable def leftChordH (q : ℝ) : ℝ := 2*q/(1+q^2)
noncomputable def leftChordK (q : ℝ) : ℝ := (1-q^2)/(1+q^2)

theorem leftMobius_I_mul_real (r : ℝ) : leftMobius (I*(r : ℂ)) = leftArcPoint r := by
  have hd : (1+r^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  apply Complex.ext <;>
    simp [leftMobius, leftArcPoint, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> field_simp [hd] <;> ring

theorem leftArcPoint_re (r : ℝ) : (leftArcPoint r).re = 2*r/(1+r^2) := by
  rfl

theorem leftArcPoint_im (r : ℝ) : (leftArcPoint r).im = (r^2-1)/(1+r^2) := by
  rfl

theorem leftArcPoint_norm (r : ℝ) : ‖leftArcPoint r‖ = 1 := by
  have hd : (1+r^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hs : ‖leftArcPoint r‖^2 = 1 := by
    rw [Complex.sq_norm, normSq_apply, leftArcPoint_re, leftArcPoint_im]
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (leftArcPoint r)]

theorem leftChordH_pos {q : ℝ} (hq : 0 < q) : 0 < leftChordH q := by
  unfold leftChordH
  positivity

theorem leftArcPoint_re_lower {q r : ℝ} (hq : 0 < q)
    (hrl : q ≤ r) (hru : r ≤ 1/q) : leftChordH q ≤ (leftArcPoint r).re := by
  rw [leftArcPoint_re, leftChordH]
  have hqr : q*r ≤ 1 := by
    have hh := (le_div_iff₀ hq).mp hru
    nlinarith
  apply (div_le_div_iff₀ (by positivity : 0 < 1+q^2) (by positivity : 0 < 1+r^2)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hrl) (sub_nonneg.mpr hqr)]

theorem leftArcPoint_at_q (q : ℝ) :
    leftArcPoint q = (leftChordH q : ℂ)-I*(leftChordK q : ℂ) := by
  apply Complex.ext
  · simp only [leftArcPoint_re, sub_re, mul_re, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, sub_self, sub_zero]
    rfl
  · simp only [leftArcPoint_im, sub_im, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, one_mul, zero_add, zero_sub]
    unfold leftChordK
    ring

theorem leftArcPoint_at_inv {q : ℝ} (hq : q ≠ 0) :
    leftArcPoint (1/q) = (leftChordH q : ℂ)+I*(leftChordK q : ℂ) := by
  apply Complex.ext <;>
    simp only [leftArcPoint_re, leftArcPoint_im, add_re, add_im, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, one_mul,
      sub_self, add_zero, zero_add]
  all_goals simp only [leftChordH, leftChordK]
  all_goals field_simp [hq]
  all_goals ring

theorem leftChordH_sq_add_K_sq (q : ℝ) : (leftChordH q)^2+(leftChordK q)^2 = 1 := by
  unfold leftChordH leftChordK
  field_simp [ne_of_gt (show (0 : ℝ) < 1+q^2 by positivity)]
  ring

theorem leftComparison_mem_ball {h : ℝ} (hh : 0 < h) {u : ℂ}
    (hre : h ≤ u.re) (hnorm : ‖u‖ ≤ 1) : u ∈ ball ((1/h : ℝ) : ℂ) (1/h) := by
  have hR : (0 : ℝ) < 1/h := one_div_pos.mpr hh
  have hmul : (1/h)*h = 1 := by field_simp
  have hRe : 1 ≤ (1/h)*u.re := by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hre)]
  have hn := norm_nonneg u
  have hdist := norm_nonneg (u-((1/h : ℝ) : ℂ))
  have hs := Complex.sq_norm u
  have hd := Complex.sq_norm (u-((1/h : ℝ) : ℂ))
  simp only [normSq_apply] at hs
  simp only [normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hd
  apply mem_ball_iff_norm.mpr
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftArcPoint_re_lower
#print axioms TwoAxisHelicoid.leftComparison_mem_ball
