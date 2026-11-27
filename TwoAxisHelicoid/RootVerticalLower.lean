import TwoAxisHelicoid.RootVerticalConstants

namespace TwoAxisHelicoid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact computation of a fully proved enclosure algorithm, performed by the Lean kernel. -/
theorem root_vertical_lower_check : certifiesVerticalBounds rootBallConfig 12
    rootTLower rootTUpper rootALower rootALower (1/10^12) (2/10^11) := by
  decide +kernel

theorem root_vertical_lower_positive {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    0 < (thetaG t rootALower).re := by
  have hb := certified_vertical_bounds rootBallConfig 12 rootTLower rootTUpper
    rootALower rootALower (1/10^12) (2/10^11) root_vertical_lower_check htl htu le_rfl le_rfl
  have hp : (0 : ℝ) < ((1/10^12 : ℚ) : ℝ) := by norm_num
  exact hp.trans_le hb.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_vertical_lower_positive
