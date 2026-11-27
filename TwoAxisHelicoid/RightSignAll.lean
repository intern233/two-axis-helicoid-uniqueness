import TwoAxisHelicoid.RightEndParameterRange
import TwoAxisHelicoid.RightRectanglePartition
import TwoAxisHelicoid.RightSignBox000
import TwoAxisHelicoid.RightSignBox001
import TwoAxisHelicoid.RightSignBox002
import TwoAxisHelicoid.RightSignBox003
import TwoAxisHelicoid.RightSignBox004
import TwoAxisHelicoid.RightSignBox005
import TwoAxisHelicoid.RightSignBox006
import TwoAxisHelicoid.RightSignBox007
import TwoAxisHelicoid.RightSignBox008
import TwoAxisHelicoid.RightSignBox009
import TwoAxisHelicoid.RightSignBox010
import TwoAxisHelicoid.RightSignBox011
import TwoAxisHelicoid.RightSignBox012
import TwoAxisHelicoid.RightSignBox013
import TwoAxisHelicoid.RightSignBox014
import TwoAxisHelicoid.RightSignBox015
import TwoAxisHelicoid.RightSignBox016
import TwoAxisHelicoid.RightSignBox017
import TwoAxisHelicoid.RightSignBox018
import TwoAxisHelicoid.RightSignBox019
import TwoAxisHelicoid.RightSignBox020
import TwoAxisHelicoid.RightSignBox021
import TwoAxisHelicoid.RightSignBox022
import TwoAxisHelicoid.RightSignBox023
import TwoAxisHelicoid.RightSignBox024
import TwoAxisHelicoid.RightSignBox025
import TwoAxisHelicoid.RightSignBox026
import TwoAxisHelicoid.RightSignBox027
import TwoAxisHelicoid.RightSignBox028
import TwoAxisHelicoid.RightSignBox029
import TwoAxisHelicoid.RightSignBox030
import TwoAxisHelicoid.RightSignBox031
import TwoAxisHelicoid.RightSignBox032
import TwoAxisHelicoid.RightSignBox033
import TwoAxisHelicoid.RightSignBox034
import TwoAxisHelicoid.RightSignBox035
import TwoAxisHelicoid.RightSignBox036
import TwoAxisHelicoid.RightSignBox037
import TwoAxisHelicoid.RightSignBox038
import TwoAxisHelicoid.RightSignBox039

namespace TwoAxisHelicoid
set_option maxHeartbeats 0

theorem right_rectangle_horizontal_period_lt {t a : ℝ}
    (htl : (7/5 : ℝ) ≤ t) (htu : t ≤ (141/100 : ℝ))
    (hal : (9/10 : ℝ) ≤ a) (hau : a ≤ 1) :
    thetaHorizontalPeriod t a < -7/5 := by
  obtain ⟨i,j,hil,hiu,hjl,hju⟩ := right_rectangle_parameter_partition htl htu hal hau
  fin_cases i <;> fin_cases j
  · apply rightSignBox000_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox001_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox002_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox003_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox004_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox005_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox006_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox007_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox008_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox009_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox010_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox011_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox012_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox013_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox014_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox015_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox016_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox017_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox018_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox019_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox020_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox021_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox022_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox023_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox024_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox025_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox026_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox027_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox028_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox029_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox030_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox031_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox032_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox033_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox034_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox035_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox036_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox037_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox038_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith
  · apply rightSignBox039_period_lt
    · norm_num at hil ⊢
      linarith
    · norm_num at hiu ⊢
      linarith
    · norm_num at hjl ⊢
      linarith
    · norm_num at hju ⊢
      linarith

/-- The complete right-end assertion of manuscript Proposition 9.2, for the
actual horizontal period along the actual vertical branch. -/
theorem actualPeriodAlong_right_certificate {t : ℝ}
    (htl : (7/5 : ℝ) ≤ t) (htu : t < ellipticVerticalUpper) :
    actualPeriodAlong t < -7/5 := by
  have hp := actual_right_parameters_in_rectangle htl htu
  exact right_rectangle_horizontal_period_lt hp.1.1 hp.1.2 hp.2.1.le hp.2.2.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.right_rectangle_horizontal_period_lt
#print axioms TwoAxisHelicoid.actualPeriodAlong_right_certificate
