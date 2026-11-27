import TwoAxisHelicoid.RootCommonPeriodBridge
import TwoAxisHelicoid.RootDyadicLeftIntegral
import TwoAxisHelicoid.RootDyadicRightIntegral

namespace TwoAxisHelicoid
open Set

/-- An actual simultaneous zero of the two theta period functions in the
reported rational rectangle. This is a local existence statement, and is
not the geometric uniqueness theorem or global period uniqueness. -/
theorem exists_root_common_period_zero :
    ∃ t a : ℝ, t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      a ∈ Ioo (rootALower : ℝ) rootAUpper ∧ thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 := by
  apply exists_common_period_zero_of_endpoint_signs
  · have h := root_left_horizontal_bounds root_left_branch_localize.1.le
      root_left_branch_localize.2.le
    have hp : (0 : ℝ) < 6/10^12 := by norm_num
    exact hp.trans_le h.1
  · have h := root_right_horizontal_bounds root_right_branch_localize.1.le
      root_right_branch_localize.2.le
    have hn : (-3/10^12 : ℝ) < 0 := by norm_num
    exact h.2.trans_lt hn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_root_common_period_zero
