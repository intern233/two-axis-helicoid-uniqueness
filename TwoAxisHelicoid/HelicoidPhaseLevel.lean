import TwoAxisHelicoid.HelicoidRelativeHorizontal
import TwoAxisHelicoid.AxisHelicoidGauge

namespace TwoAxisHelicoid
open Complex Set

/-- The zero imaginary direction of the rotating horizontal coordinate
is precisely the comparison helicoid. At height zero this condition
characterizes the horizontal axis when the ruling has its marked phase. -/
theorem relative_horizontal_im_eq_zero_iff (α b : ℝ) (p : Fin 3 → ℝ) :
    (helicoidRelativeHorizontal α b p).im=0 ↔ p∈range (axisRuledHelicoid I α b) := by
  have e := helicoid_side_relative_argument p 0 α b
  simp only [helicoidPhaseNormal,ofReal_zero,zero_mul,Complex.exp_zero,mul_one,neg_zero,one_mul] at e
  rw [← e,axisHelicoidSide_eq_zero_iff (by simp : normSq I=1)]

theorem aligned_relative_horizontal_at_height_zero {α b : ℝ}
    (aligned : range (axisRuledHelicoid I α b)=range (axisRuledHelicoid I α 0)) (p : Fin 3 → ℝ)
    (height : p 2=0) : (helicoidRelativeHorizontal α b p).im=0 ↔ p 1=0 := by
  rw [relative_horizontal_im_eq_zero_iff,aligned,← axisHelicoidSide_eq_zero_iff (by simp : normSq I=1)]
  change (I*exp (I*((α*(p 2-0):ℝ):ℂ))).re*p 0+(I*exp (I*((α*(p 2-0):ℝ):ℂ))).im*p 1=0 ↔ p 1=0
  simp [height]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.relative_horizontal_im_eq_zero_iff
#print axioms TwoAxisHelicoid.aligned_relative_horizontal_at_height_zero
