import TwoAxisHelicoid.RootDyadicHalfComposite
import TwoAxisHelicoid.RootDyadicLeftCell000
import TwoAxisHelicoid.RootDyadicLeftCell001
import TwoAxisHelicoid.RootDyadicLeftCell002
import TwoAxisHelicoid.RootDyadicLeftCell003
import TwoAxisHelicoid.RootDyadicLeftCell004
import TwoAxisHelicoid.RootDyadicLeftCell005
import TwoAxisHelicoid.RootDyadicLeftCell006
import TwoAxisHelicoid.RootDyadicLeftCell007
import TwoAxisHelicoid.RootDyadicLeftCell008
import TwoAxisHelicoid.RootDyadicLeftCell009
import TwoAxisHelicoid.RootDyadicLeftCell010
import TwoAxisHelicoid.RootDyadicLeftCell011
import TwoAxisHelicoid.RootDyadicLeftCell012
import TwoAxisHelicoid.RootDyadicLeftCell013
import TwoAxisHelicoid.RootDyadicLeftCell014
import TwoAxisHelicoid.RootDyadicLeftCell015
import TwoAxisHelicoid.RootDyadicLeftCell016
import TwoAxisHelicoid.RootDyadicLeftCell017
import TwoAxisHelicoid.RootDyadicLeftCell018
import TwoAxisHelicoid.RootDyadicLeftCell019
import TwoAxisHelicoid.RootDyadicLeftCell020
import TwoAxisHelicoid.RootDyadicLeftCell021
import TwoAxisHelicoid.RootDyadicLeftCell022
import TwoAxisHelicoid.RootDyadicLeftCell023
import TwoAxisHelicoid.RootDyadicLeftCell024
import TwoAxisHelicoid.RootDyadicLeftCell025
import TwoAxisHelicoid.RootDyadicLeftCell026
import TwoAxisHelicoid.RootDyadicLeftCell027
import TwoAxisHelicoid.RootDyadicLeftCell028
import TwoAxisHelicoid.RootDyadicLeftCell029
import TwoAxisHelicoid.RootDyadicLeftCell030
import TwoAxisHelicoid.RootDyadicLeftCell031
import TwoAxisHelicoid.RootDyadicLeftCell032
import TwoAxisHelicoid.RootDyadicLeftCell033
import TwoAxisHelicoid.RootDyadicLeftCell034
import TwoAxisHelicoid.RootDyadicLeftCell035
import TwoAxisHelicoid.RootDyadicLeftCell036
import TwoAxisHelicoid.RootDyadicLeftCell037
import TwoAxisHelicoid.RootDyadicLeftCell038
import TwoAxisHelicoid.RootDyadicLeftCell039

namespace TwoAxisHelicoid
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def rootDyadicLeftCells : Fin 40 → RootDyadicCell := ![rootDyadicLeftCell000,rootDyadicLeftCell001,rootDyadicLeftCell002,rootDyadicLeftCell003,rootDyadicLeftCell004,rootDyadicLeftCell005,rootDyadicLeftCell006,rootDyadicLeftCell007,rootDyadicLeftCell008,rootDyadicLeftCell009,rootDyadicLeftCell010,rootDyadicLeftCell011,rootDyadicLeftCell012,rootDyadicLeftCell013,rootDyadicLeftCell014,rootDyadicLeftCell015,rootDyadicLeftCell016,rootDyadicLeftCell017,rootDyadicLeftCell018,rootDyadicLeftCell019,rootDyadicLeftCell020,rootDyadicLeftCell021,rootDyadicLeftCell022,rootDyadicLeftCell023,rootDyadicLeftCell024,rootDyadicLeftCell025,rootDyadicLeftCell026,rootDyadicLeftCell027,rootDyadicLeftCell028,rootDyadicLeftCell029,rootDyadicLeftCell030,rootDyadicLeftCell031,rootDyadicLeftCell032,rootDyadicLeftCell033,rootDyadicLeftCell034,rootDyadicLeftCell035,rootDyadicLeftCell036,rootDyadicLeftCell037,rootDyadicLeftCell038,rootDyadicLeftCell039]
theorem rootDyadicLeftCells_valid : ∀ i : Fin 40, (rootDyadicLeftCells i).Valid rootDyadicLeft (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact rootDyadicLeftCell000_valid
  · exact rootDyadicLeftCell001_valid
  · exact rootDyadicLeftCell002_valid
  · exact rootDyadicLeftCell003_valid
  · exact rootDyadicLeftCell004_valid
  · exact rootDyadicLeftCell005_valid
  · exact rootDyadicLeftCell006_valid
  · exact rootDyadicLeftCell007_valid
  · exact rootDyadicLeftCell008_valid
  · exact rootDyadicLeftCell009_valid
  · exact rootDyadicLeftCell010_valid
  · exact rootDyadicLeftCell011_valid
  · exact rootDyadicLeftCell012_valid
  · exact rootDyadicLeftCell013_valid
  · exact rootDyadicLeftCell014_valid
  · exact rootDyadicLeftCell015_valid
  · exact rootDyadicLeftCell016_valid
  · exact rootDyadicLeftCell017_valid
  · exact rootDyadicLeftCell018_valid
  · exact rootDyadicLeftCell019_valid
  · exact rootDyadicLeftCell020_valid
  · exact rootDyadicLeftCell021_valid
  · exact rootDyadicLeftCell022_valid
  · exact rootDyadicLeftCell023_valid
  · exact rootDyadicLeftCell024_valid
  · exact rootDyadicLeftCell025_valid
  · exact rootDyadicLeftCell026_valid
  · exact rootDyadicLeftCell027_valid
  · exact rootDyadicLeftCell028_valid
  · exact rootDyadicLeftCell029_valid
  · exact rootDyadicLeftCell030_valid
  · exact rootDyadicLeftCell031_valid
  · exact rootDyadicLeftCell032_valid
  · exact rootDyadicLeftCell033_valid
  · exact rootDyadicLeftCell034_valid
  · exact rootDyadicLeftCell035_valid
  · exact rootDyadicLeftCell036_valid
  · exact rootDyadicLeftCell037_valid
  · exact rootDyadicLeftCell038_valid
  · exact rootDyadicLeftCell039_valid
theorem root_left_horizontal_bounds {a : ℝ}
    (hal : (rootLeftALower : ℝ) ≤ a) (hau : a ≤ (rootLeftAUpper : ℝ)) :
    (6/10^12 : ℝ) ≤ thetaHorizontalPeriod rootTLower a ∧ thetaHorizontalPeriod rootTLower a ≤ (7/10^12 : ℝ) := by
  convert dyadic_horizontal_half_bounds (by decide : 0 < 40) rootDyadicLeft rootDyadicLeft_valid rootDyadicLeftCells
    (1/20) (6/10^12) (7/10^12) rootDyadicLeftCells_valid (by decide +kernel) (by decide +kernel)
    le_rfl le_rfl (by norm_num [rootTLower, rootTUpper]) (by norm_num [rootTLower, rootTUpper]) hal hau using 1 <;> norm_num
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.root_left_horizontal_bounds
