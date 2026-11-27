import TwoAxisHelicoid.NegativeSignBox000
import TwoAxisHelicoid.NegativeVerticalBox000
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem actualPeriodAlong_negative_box000 {t : ℝ}
    (htl : ((9/10) : ℝ) ≤ t) (htu : t ≤ ((1441/1600) : ℝ)) : actualPeriodAlong t < -1/25 := by
  have ha := negativeVerticalBox000_enclosure htl htu
  exact negativeSignBox000_period_lt htl htu ha.1.le ha.2.le
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actualPeriodAlong_negative_box000
