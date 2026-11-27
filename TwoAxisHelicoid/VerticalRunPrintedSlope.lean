import TwoAxisHelicoid.RightEndpointTheorem

namespace TwoAxisHelicoid
open Set

/-- The one-sided derivative of the endpoint extension lies between the two
30-place rational endpoints printed in the attachment `vertical_run.log`. -/
theorem vertical_run_displayed_right_derivative :
    (133652317282437548238921248808 / 10^30 : ℝ) <
        derivWithin rightExtendedPeriod (Iio ellipticVerticalUpper) ellipticVerticalUpper ∧
      derivWithin rightExtendedPeriod (Iio ellipticVerticalUpper) ellipticVerticalUpper <
        (133653238307059875782433586357 / 10^30 : ℝ) := by
  have h := certified_rightSlope_bounds rightCoefficientConfig 8
    rightCoefficientTLower rightCoefficientTUpper (133652619/10^9) (133652910/10^9)
    right_coefficient_check ellipticVerticalUpper_in_coefficient_interval.1
    ellipticVerticalUpper_in_coefficient_interval.2
  rw [rightSlopeTheta_eq_period_slope ellipticVerticalUpper_pos] at h
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  rw [rightExtendedPeriod_hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio _)]
  constructor <;> linarith [h.1, h.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.vertical_run_displayed_right_derivative
