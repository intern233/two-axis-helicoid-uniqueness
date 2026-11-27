import TwoAxisHelicoid.RootVerticalConstants

namespace TwoAxisHelicoid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem root_vertical_upper_check : certifiesVerticalBounds rootBallConfig 12
    rootTLower rootTUpper rootAUpper rootAUpper (-2/10^11) (-1/10^12) := by
  decide +kernel

theorem root_vertical_upper_negative {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    (thetaG t rootAUpper).re < 0 := by
  have hb := certified_vertical_bounds rootBallConfig 12 rootTLower rootTUpper
    rootAUpper rootAUpper (-2/10^11) (-1/10^12) root_vertical_upper_check htl htu le_rfl le_rfl
  have hp : ((-1/10^12 : ℚ) : ℝ) < 0 := by norm_num
  exact hb.2.trans_lt hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_vertical_upper_negative
