import TwoAxisHelicoid.VerticalDerivativeEnclosure
import TwoAxisHelicoid.RootVerticalConstants

namespace TwoAxisHelicoid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem root_vertical_denominator_check : certifiesVerticalDenominator rootBallConfig 12
    rootTLower rootTUpper rootALower rootAUpper := by
  decide +kernel

theorem root_vertical_derivative_check : certifiesVerticalDerivativeUpper rootBallConfig 12
    rootTLower rootTUpper rootALower rootAUpper (-13) := by
  decide +kernel

theorem root_vertical_denominator {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    thetaJet t 0 (Real.pi*a/2) ≠ 0 :=
  certified_vertical_denominator rootBallConfig 12 rootTLower rootTUpper
    rootALower rootAUpper root_vertical_denominator_check htl htu hal hau

theorem root_vertical_derivative_negative {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    (thetaGa t a).re < 0 := by
  have h := certified_vertical_derivative_upper rootBallConfig 12 rootTLower rootTUpper
    rootALower rootAUpper (-13) root_vertical_derivative_check htl htu hal hau
  norm_num at h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_vertical_derivative_negative
