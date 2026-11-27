import TwoAxisHelicoid.RightCoefficientEnclosure

namespace TwoAxisHelicoid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightCoefficientConfig : BallConfig := ⟨80,20,10⟩
def rightCoefficientTLower : ℚ := 100000000/70945980
def rightCoefficientTUpper : ℚ := 100000000/70945978

theorem right_coefficient_check : certifiesRightSlope rightCoefficientConfig 8
    rightCoefficientTLower rightCoefficientTUpper (133652619/10^9) (133652910/10^9) := by
  decide +kernel

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.right_coefficient_check
