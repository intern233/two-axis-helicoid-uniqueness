import TwoAxisHelicoid.LeftMobiusComparison

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory
set_option maxHeartbeats 800000

noncomputable def leftChordRealKernel (k h v : ℝ) : ℝ :=
  Real.exp (-k*v)*(((1-h^2-v^2)*Real.cos (k*h)+2*h*Real.sin (k*h))/(h^2+(v-1)^2))

theorem leftChordDifferential_line_ne_pole {h : ℝ} (hh : h ≠ 0) (v : ℝ) :
    (h : ℂ)+I*(v : ℂ) ≠ I := by
  intro he
  have hr := congrArg Complex.re he
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_self, add_zero] at hr
  exact hh hr

theorem leftChordDifferential_line_continuous (t k : ℝ) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun v : ℝ => I*leftChordDifferential t k ((h : ℂ)+I*(v : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact continuousAt_const.mul
    ((leftChordDifferential_differentiableAt t k
      (leftChordDifferential_line_ne_pole hh v)).continuousAt.comp
        (f := fun u : ℝ => (h : ℂ)+I*(u : ℂ)) (by fun_prop))

theorem leftChordDifferential_re {t h : ℝ} (ht : t ≠ 0) (hh : h ≠ 0) (k v : ℝ) :
    (I*leftChordDifferential t k ((h : ℂ)+I*(v : ℂ))).re =
      (Real.pi/(2*t))*leftChordRealKernel k h v := by
  have hd : h^2+(v-1)^2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero hh, sq_nonneg (v-1)])
  unfold leftChordDifferential leftChordRealKernel
  norm_num only [mul_re, mul_im, div_re, div_im, add_re, add_im, sub_re, sub_im,
    ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat, normSq_apply,
    exp_re, exp_im, zero_mul, mul_zero, one_mul, zero_add, add_zero,
    sub_zero, zero_sub]
  field_simp [ht, hd]
  ring

theorem leftChordRealKernel_continuous {h : ℝ} (hh : h ≠ 0) (k : ℝ) :
    Continuous (leftChordRealKernel k h) := by
  unfold leftChordRealKernel
  have hd (v : ℝ) : h^2+(v-1)^2 ≠ 0 := ne_of_gt
    (show (0 : ℝ) < h^2+(v-1)^2 by nlinarith [sq_pos_of_ne_zero hh, sq_nonneg (v-1)])
  fun_prop (disch := exact hd _)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordDifferential_re
