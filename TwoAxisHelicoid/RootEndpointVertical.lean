import TwoAxisHelicoid.RootEndpointConstants
import TwoAxisHelicoid.RootVerticalBranch

namespace TwoAxisHelicoid
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem root_left_vertical_lower_check : certifiesVerticalBounds rootHorizontalConfig 12
    rootTLower rootTLower rootLeftALower rootLeftALower (1/10^18) (1/10^15) := by
  decide +kernel

theorem root_left_vertical_upper_check : certifiesVerticalBounds rootHorizontalConfig 12
    rootTLower rootTLower rootLeftAUpper rootLeftAUpper (-1/10^15) (-1/10^18) := by
  decide +kernel

theorem root_right_vertical_lower_check : certifiesVerticalBounds rootHorizontalConfig 12
    rootTUpper rootTUpper rootRightALower rootRightALower (1/10^18) (1/10^15) := by
  decide +kernel

theorem root_right_vertical_upper_check : certifiesVerticalBounds rootHorizontalConfig 12
    rootTUpper rootTUpper rootRightAUpper rootRightAUpper (-1/10^15) (-1/10^18) := by
  decide +kernel

theorem root_vertical_localize {t a l u : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (ha : a ∈ Icc (rootALower : ℝ) rootAUpper) (hz : thetaG t a = 0)
    (hl : l ∈ Icc (rootALower : ℝ) rootAUpper)
    (hu : u ∈ Icc (rootALower : ℝ) rootAUpper)
    (hp : 0 < (thetaG t l).re) (hn : (thetaG t u).re < 0) : a ∈ Ioo l u := by
  have hm := (root_vertical_strictAnti htl htu).antitoneOn
  constructor
  · by_contra h
    have hh := hm ha hl (le_of_not_gt h)
    dsimp only at hh
    rw [hz, Complex.zero_re] at hh
    linarith
  · by_contra h
    have hh := hm hu ha (le_of_not_gt h)
    dsimp only at hh
    rw [hz, Complex.zero_re] at hh
    linarith

theorem root_left_vertical_localize {a : ℝ}
    (ha : a ∈ Icc (rootALower : ℝ) rootAUpper) (hz : thetaG rootTLower a = 0) :
    a ∈ Ioo (rootLeftALower : ℝ) rootLeftAUpper := by
  have hp := certified_vertical_bounds rootHorizontalConfig 12 rootTLower rootTLower
    rootLeftALower rootLeftALower (1/10^18) (1/10^15)
    root_left_vertical_lower_check le_rfl le_rfl le_rfl le_rfl
  have hn := certified_vertical_bounds rootHorizontalConfig 12 rootTLower rootTLower
    rootLeftAUpper rootLeftAUpper (-1/10^15) (-1/10^18)
    root_left_vertical_upper_check le_rfl le_rfl le_rfl le_rfl
  apply root_vertical_localize le_rfl (by norm_num [rootTLower, rootTUpper]) ha hz
    (by norm_num [rootLeftALower, rootALower, rootAUpper])
    (by norm_num [rootLeftAUpper, rootALower, rootAUpper])
  · exact lt_of_lt_of_le (by norm_num) hp.1
  · exact lt_of_le_of_lt hn.2 (by norm_num)

theorem root_right_vertical_localize {a : ℝ}
    (ha : a ∈ Icc (rootALower : ℝ) rootAUpper) (hz : thetaG rootTUpper a = 0) :
    a ∈ Ioo (rootRightALower : ℝ) rootRightAUpper := by
  have hp := certified_vertical_bounds rootHorizontalConfig 12 rootTUpper rootTUpper
    rootRightALower rootRightALower (1/10^18) (1/10^15)
    root_right_vertical_lower_check le_rfl le_rfl le_rfl le_rfl
  have hn := certified_vertical_bounds rootHorizontalConfig 12 rootTUpper rootTUpper
    rootRightAUpper rootRightAUpper (-1/10^15) (-1/10^18)
    root_right_vertical_upper_check le_rfl le_rfl le_rfl le_rfl
  apply root_vertical_localize (by norm_num [rootTLower, rootTUpper]) le_rfl ha hz
    (by norm_num [rootRightALower, rootALower, rootAUpper])
    (by norm_num [rootRightAUpper, rootALower, rootAUpper])
  · exact lt_of_lt_of_le (by norm_num) hp.1
  · exact lt_of_le_of_lt hn.2 (by norm_num)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_left_vertical_localize
#print axioms TwoAxisHelicoid.root_right_vertical_localize
