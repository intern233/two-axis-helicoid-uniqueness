import TwoAxisHelicoid.DyadicExpTrace
import Mathlib.Analysis.Real.Pi.Bounds

namespace TwoAxisHelicoid
open Complex

/-- Signed bounds for the sine at an exact rational point, using an
integer trace for the scaled complex exponential. -/
theorem dyadic_sine_bounds (cfg : BallConfig) (x : ℚ) (b : DyadicBall) (w : DyadicExpTrace)
    (point : b.toBall cfg.prec=ComplexBall.point ⟨0,x⟩) (valid : w.Valid cfg b) :
    let z := w.output.toBall cfg.prec
    ((z.center.im-z.radius:ℚ):ℝ)≤Real.sin (x:ℝ) ∧ Real.sin (x:ℝ)≤((z.center.im+z.radius:ℚ):ℝ) := by
  let z := w.output.toBall cfg.prec
  have h : (b.toBall cfg.prec).Contains (((x:ℝ):ℂ)*I) := by
    rw [point]
    have e : (⟨0,x⟩:QComplex).val=(((x:ℝ):ℂ)*I) := by
      apply Complex.ext <;> simp [QComplex.val]
    rw [← e]
    exact ComplexBall.point_contains _
  have hh := w.sound cfg h valid
  have im := (Complex.abs_im_le_norm (Complex.exp (((x:ℝ):ℂ)*I)-z.center.val)).trans hh
  rw [Complex.sub_im,Complex.exp_ofReal_mul_I] at im
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at im
  change |Real.sin (x:ℝ)-(z.center.im:ℝ)|≤(z.radius:ℝ) at im
  obtain ⟨lo,hi⟩ := abs_le.mp im
  change ((z.center.im-z.radius:ℚ):ℝ)≤_ ∧ _≤((z.center.im+z.radius:ℚ):ℝ)
  push_cast
  exact ⟨by linarith,by linarith⟩

/-- On [3,4] a strict sine sign on either side isolates π. -/
theorem pi_between_of_sine_signs {l u : ℝ} (hl : l≤4) (hu : 0≤u)
    (left : 0<Real.sin l) (right : Real.sin u<0) : l<Real.pi ∧ Real.pi<u := by
  constructor
  · by_contra h
    have lo := le_of_not_gt h
    have hn := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr lo) (by linarith [Real.pi_gt_three] : l-Real.pi≤Real.pi)
    rw [show l=(l-Real.pi)+Real.pi by ring,Real.sin_add_pi] at left
    linarith
  · by_contra h
    exact (not_lt_of_ge (Real.sin_nonneg_of_nonneg_of_le_pi hu (le_of_not_gt h))) right

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dyadic_sine_bounds
#print axioms TwoAxisHelicoid.pi_between_of_sine_signs
