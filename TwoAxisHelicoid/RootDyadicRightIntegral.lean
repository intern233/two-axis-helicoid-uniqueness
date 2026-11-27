import TwoAxisHelicoid.RootDyadicHalfComposite
import TwoAxisHelicoid.RootDyadicRightCell000
import TwoAxisHelicoid.RootDyadicRightCell001
import TwoAxisHelicoid.RootDyadicRightCell002
import TwoAxisHelicoid.RootDyadicRightCell003
import TwoAxisHelicoid.RootDyadicRightCell004
import TwoAxisHelicoid.RootDyadicRightCell005
import TwoAxisHelicoid.RootDyadicRightCell006
import TwoAxisHelicoid.RootDyadicRightCell007
import TwoAxisHelicoid.RootDyadicRightCell008
import TwoAxisHelicoid.RootDyadicRightCell009
import TwoAxisHelicoid.RootDyadicRightCell010
import TwoAxisHelicoid.RootDyadicRightCell011
import TwoAxisHelicoid.RootDyadicRightCell012
import TwoAxisHelicoid.RootDyadicRightCell013
import TwoAxisHelicoid.RootDyadicRightCell014
import TwoAxisHelicoid.RootDyadicRightCell015
import TwoAxisHelicoid.RootDyadicRightCell016
import TwoAxisHelicoid.RootDyadicRightCell017
import TwoAxisHelicoid.RootDyadicRightCell018
import TwoAxisHelicoid.RootDyadicRightCell019
import TwoAxisHelicoid.RootDyadicRightCell020
import TwoAxisHelicoid.RootDyadicRightCell021
import TwoAxisHelicoid.RootDyadicRightCell022
import TwoAxisHelicoid.RootDyadicRightCell023
import TwoAxisHelicoid.RootDyadicRightCell024
import TwoAxisHelicoid.RootDyadicRightCell025
import TwoAxisHelicoid.RootDyadicRightCell026
import TwoAxisHelicoid.RootDyadicRightCell027
import TwoAxisHelicoid.RootDyadicRightCell028
import TwoAxisHelicoid.RootDyadicRightCell029
import TwoAxisHelicoid.RootDyadicRightCell030
import TwoAxisHelicoid.RootDyadicRightCell031
import TwoAxisHelicoid.RootDyadicRightCell032
import TwoAxisHelicoid.RootDyadicRightCell033
import TwoAxisHelicoid.RootDyadicRightCell034
import TwoAxisHelicoid.RootDyadicRightCell035
import TwoAxisHelicoid.RootDyadicRightCell036
import TwoAxisHelicoid.RootDyadicRightCell037
import TwoAxisHelicoid.RootDyadicRightCell038
import TwoAxisHelicoid.RootDyadicRightCell039

namespace TwoAxisHelicoid
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def rootDyadicRightCells : Fin 40 → RootDyadicCell := ![rootDyadicRightCell000,rootDyadicRightCell001,rootDyadicRightCell002,rootDyadicRightCell003,rootDyadicRightCell004,rootDyadicRightCell005,rootDyadicRightCell006,rootDyadicRightCell007,rootDyadicRightCell008,rootDyadicRightCell009,rootDyadicRightCell010,rootDyadicRightCell011,rootDyadicRightCell012,rootDyadicRightCell013,rootDyadicRightCell014,rootDyadicRightCell015,rootDyadicRightCell016,rootDyadicRightCell017,rootDyadicRightCell018,rootDyadicRightCell019,rootDyadicRightCell020,rootDyadicRightCell021,rootDyadicRightCell022,rootDyadicRightCell023,rootDyadicRightCell024,rootDyadicRightCell025,rootDyadicRightCell026,rootDyadicRightCell027,rootDyadicRightCell028,rootDyadicRightCell029,rootDyadicRightCell030,rootDyadicRightCell031,rootDyadicRightCell032,rootDyadicRightCell033,rootDyadicRightCell034,rootDyadicRightCell035,rootDyadicRightCell036,rootDyadicRightCell037,rootDyadicRightCell038,rootDyadicRightCell039]
theorem rootDyadicRightCells_valid : ∀ i : Fin 40, (rootDyadicRightCells i).Valid rootDyadicRight (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact rootDyadicRightCell000_valid
  · exact rootDyadicRightCell001_valid
  · exact rootDyadicRightCell002_valid
  · exact rootDyadicRightCell003_valid
  · exact rootDyadicRightCell004_valid
  · exact rootDyadicRightCell005_valid
  · exact rootDyadicRightCell006_valid
  · exact rootDyadicRightCell007_valid
  · exact rootDyadicRightCell008_valid
  · exact rootDyadicRightCell009_valid
  · exact rootDyadicRightCell010_valid
  · exact rootDyadicRightCell011_valid
  · exact rootDyadicRightCell012_valid
  · exact rootDyadicRightCell013_valid
  · exact rootDyadicRightCell014_valid
  · exact rootDyadicRightCell015_valid
  · exact rootDyadicRightCell016_valid
  · exact rootDyadicRightCell017_valid
  · exact rootDyadicRightCell018_valid
  · exact rootDyadicRightCell019_valid
  · exact rootDyadicRightCell020_valid
  · exact rootDyadicRightCell021_valid
  · exact rootDyadicRightCell022_valid
  · exact rootDyadicRightCell023_valid
  · exact rootDyadicRightCell024_valid
  · exact rootDyadicRightCell025_valid
  · exact rootDyadicRightCell026_valid
  · exact rootDyadicRightCell027_valid
  · exact rootDyadicRightCell028_valid
  · exact rootDyadicRightCell029_valid
  · exact rootDyadicRightCell030_valid
  · exact rootDyadicRightCell031_valid
  · exact rootDyadicRightCell032_valid
  · exact rootDyadicRightCell033_valid
  · exact rootDyadicRightCell034_valid
  · exact rootDyadicRightCell035_valid
  · exact rootDyadicRightCell036_valid
  · exact rootDyadicRightCell037_valid
  · exact rootDyadicRightCell038_valid
  · exact rootDyadicRightCell039_valid
theorem root_right_horizontal_bounds {a : ℝ}
    (hal : (rootRightALower : ℝ) ≤ a) (hau : a ≤ (rootRightAUpper : ℝ)) :
    (-4/10^12 : ℝ) ≤ thetaHorizontalPeriod rootTUpper a ∧ thetaHorizontalPeriod rootTUpper a ≤ (-3/10^12 : ℝ) := by
  convert dyadic_horizontal_half_bounds (by decide : 0 < 40) rootDyadicRight rootDyadicRight_valid rootDyadicRightCells
    (1/20) (-4/10^12) (-3/10^12) rootDyadicRightCells_valid (by decide +kernel) (by decide +kernel)
    le_rfl le_rfl (by norm_num [rootTLower, rootTUpper]) (by norm_num [rootTLower, rootTUpper]) hal hau using 1 <;> norm_num
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.root_right_horizontal_bounds
