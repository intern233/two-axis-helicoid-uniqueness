import TwoAxisHelicoid.LeftComparisonLower
import TwoAxisHelicoid.LeftPeriodError

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000

/-- Uniform lower bound for the actual horizontal period along its actual vertical root. -/
theorem actualPeriodAlong_left_lower_bound {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    Real.pi/t < actualPeriodAlong t := by
  have h0 := leftComparisonPeriod_gt_seventy ht htu
  have he := (abs_lt.mp (leftPeriod_error_lt ht htu)).1
  linarith

/-- The manuscript's complete small-height positive-sign statement (Proposition 7.1). -/
theorem actualPeriodAlong_positive_left {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    0 < actualPeriodAlong t :=
  (div_pos Real.pi_pos ht).trans (actualPeriodAlong_left_lower_bound ht htu)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_positive_left
