import TwoAxisHelicoid.RightCoefficientIdentity
import TwoAxisHelicoid.RightCoefficientCheck

namespace TwoAxisHelicoid

theorem ellipticVerticalUpper_in_coefficient_interval :
    (rightCoefficientTLower:ℝ) ≤ ellipticVerticalUpper ∧
      ellipticVerticalUpper ≤ (rightCoefficientTUpper:ℝ) := by
  constructor
  · have h := one_div_le_one_div_of_le ellipticCriticalT_pos ellipticCriticalT_location.2.le
    convert h using 1 <;> norm_num [rightCoefficientTLower,ellipticVerticalUpper]
  · have h := one_div_le_one_div_of_le
      (by norm_num : (0:ℝ) < 70945978/100000000) ellipticCriticalT_location.1.le
    convert h using 1 <;> norm_num [rightCoefficientTUpper,ellipticVerticalUpper]

theorem actual_right_slope_certificate :
    (1336523172824375/10^16:ℝ) <
      -deriv ellipticFReal ellipticVerticalUpper+ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi ∧
    -deriv ellipticFReal ellipticVerticalUpper+ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi <
      (1336532383070600/10^16:ℝ) := by
  have hb := certified_rightSlope_bounds rightCoefficientConfig 8 rightCoefficientTLower rightCoefficientTUpper
    (133652619/10^9) (133652910/10^9) right_coefficient_check
    ellipticVerticalUpper_in_coefficient_interval.1 ellipticVerticalUpper_in_coefficient_interval.2
  rw [rightSlopeTheta_eq_period_slope ellipticVerticalUpper_pos] at hb
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at hb
  constructor <;> linarith [hb.1,hb.2]

theorem actual_right_slope_pos :
    0 < -deriv ellipticFReal ellipticVerticalUpper+ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi :=
  lt_trans (by norm_num) actual_right_slope_certificate.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_right_slope_certificate
