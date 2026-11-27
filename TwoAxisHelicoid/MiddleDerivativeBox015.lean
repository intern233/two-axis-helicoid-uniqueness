import TwoAxisHelicoid.MiddleVerticalBox015
import TwoAxisHelicoid.MiddleDerivativeBox015Cell000
import TwoAxisHelicoid.MiddleDerivativeBox015Cell001
import TwoAxisHelicoid.MiddleDerivativeBox015Cell002
import TwoAxisHelicoid.MiddleDerivativeBox015Cell003
import TwoAxisHelicoid.MiddleDerivativeBox015Cell004
import TwoAxisHelicoid.MiddleDerivativeBox015Cell005
import TwoAxisHelicoid.MiddleDerivativeBox015Cell006
import TwoAxisHelicoid.MiddleDerivativeBox015Cell007
import TwoAxisHelicoid.MiddleDerivativeBox015Cell008
import TwoAxisHelicoid.MiddleDerivativeBox015Cell009
import TwoAxisHelicoid.MiddleDerivativeBox015Cell010
import TwoAxisHelicoid.MiddleDerivativeBox015Cell011
import TwoAxisHelicoid.MiddleDerivativeBox015Cell012
import TwoAxisHelicoid.MiddleDerivativeBox015Cell013
import TwoAxisHelicoid.MiddleDerivativeBox015Cell014
import TwoAxisHelicoid.MiddleDerivativeBox015Cell015
import TwoAxisHelicoid.MiddleDerivativeBox015Cell016
import TwoAxisHelicoid.MiddleDerivativeBox015Cell017
import TwoAxisHelicoid.MiddleDerivativeBox015Cell018
import TwoAxisHelicoid.MiddleDerivativeBox015Cell019
import TwoAxisHelicoid.MiddleDerivativeBox015Cell020
import TwoAxisHelicoid.MiddleDerivativeBox015Cell021
import TwoAxisHelicoid.MiddleDerivativeBox015Cell022
import TwoAxisHelicoid.MiddleDerivativeBox015Cell023
import TwoAxisHelicoid.MiddleDerivativeBox015Cell024
import TwoAxisHelicoid.MiddleDerivativeBox015Cell025
import TwoAxisHelicoid.MiddleDerivativeBox015Cell026
import TwoAxisHelicoid.MiddleDerivativeBox015Cell027
import TwoAxisHelicoid.MiddleDerivativeBox015Cell028
import TwoAxisHelicoid.MiddleDerivativeBox015Cell029
import TwoAxisHelicoid.MiddleDerivativeBox015Cell030
import TwoAxisHelicoid.MiddleDerivativeBox015Cell031
import TwoAxisHelicoid.MiddleDerivativeBox015Cell032
import TwoAxisHelicoid.MiddleDerivativeBox015Cell033
import TwoAxisHelicoid.MiddleDerivativeBox015Cell034
import TwoAxisHelicoid.MiddleDerivativeBox015Cell035
import TwoAxisHelicoid.MiddleDerivativeBox015Cell036
import TwoAxisHelicoid.MiddleDerivativeBox015Cell037
import TwoAxisHelicoid.MiddleDerivativeBox015Cell038
import TwoAxisHelicoid.MiddleDerivativeBox015Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox015Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox015Cell000,middleDerivativeBox015Cell001,middleDerivativeBox015Cell002,middleDerivativeBox015Cell003,middleDerivativeBox015Cell004,middleDerivativeBox015Cell005,middleDerivativeBox015Cell006,middleDerivativeBox015Cell007,middleDerivativeBox015Cell008,middleDerivativeBox015Cell009,middleDerivativeBox015Cell010,middleDerivativeBox015Cell011,middleDerivativeBox015Cell012,middleDerivativeBox015Cell013,middleDerivativeBox015Cell014,middleDerivativeBox015Cell015,middleDerivativeBox015Cell016,middleDerivativeBox015Cell017,middleDerivativeBox015Cell018,middleDerivativeBox015Cell019,middleDerivativeBox015Cell020,middleDerivativeBox015Cell021,middleDerivativeBox015Cell022,middleDerivativeBox015Cell023,middleDerivativeBox015Cell024,middleDerivativeBox015Cell025,middleDerivativeBox015Cell026,middleDerivativeBox015Cell027,middleDerivativeBox015Cell028,middleDerivativeBox015Cell029,middleDerivativeBox015Cell030,middleDerivativeBox015Cell031,middleDerivativeBox015Cell032,middleDerivativeBox015Cell033,middleDerivativeBox015Cell034,middleDerivativeBox015Cell035,middleDerivativeBox015Cell036,middleDerivativeBox015Cell037,middleDerivativeBox015Cell038,middleDerivativeBox015Cell039]
theorem middleDerivativeBox015Cells_valid : ∀ i : Fin 40, (middleDerivativeBox015Cells i).Valid middleRangeSetup middleDerivativeParameters015 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox015Cell000_valid
  · exact middleDerivativeBox015Cell001_valid
  · exact middleDerivativeBox015Cell002_valid
  · exact middleDerivativeBox015Cell003_valid
  · exact middleDerivativeBox015Cell004_valid
  · exact middleDerivativeBox015Cell005_valid
  · exact middleDerivativeBox015Cell006_valid
  · exact middleDerivativeBox015Cell007_valid
  · exact middleDerivativeBox015Cell008_valid
  · exact middleDerivativeBox015Cell009_valid
  · exact middleDerivativeBox015Cell010_valid
  · exact middleDerivativeBox015Cell011_valid
  · exact middleDerivativeBox015Cell012_valid
  · exact middleDerivativeBox015Cell013_valid
  · exact middleDerivativeBox015Cell014_valid
  · exact middleDerivativeBox015Cell015_valid
  · exact middleDerivativeBox015Cell016_valid
  · exact middleDerivativeBox015Cell017_valid
  · exact middleDerivativeBox015Cell018_valid
  · exact middleDerivativeBox015Cell019_valid
  · exact middleDerivativeBox015Cell020_valid
  · exact middleDerivativeBox015Cell021_valid
  · exact middleDerivativeBox015Cell022_valid
  · exact middleDerivativeBox015Cell023_valid
  · exact middleDerivativeBox015Cell024_valid
  · exact middleDerivativeBox015Cell025_valid
  · exact middleDerivativeBox015Cell026_valid
  · exact middleDerivativeBox015Cell027_valid
  · exact middleDerivativeBox015Cell028_valid
  · exact middleDerivativeBox015Cell029_valid
  · exact middleDerivativeBox015Cell030_valid
  · exact middleDerivativeBox015Cell031_valid
  · exact middleDerivativeBox015Cell032_valid
  · exact middleDerivativeBox015Cell033_valid
  · exact middleDerivativeBox015Cell034_valid
  · exact middleDerivativeBox015Cell035_valid
  · exact middleDerivativeBox015Cell036_valid
  · exact middleDerivativeBox015Cell037_valid
  · exact middleDerivativeBox015Cell038_valid
  · exact middleDerivativeBox015Cell039_valid
theorem middleDerivativeBox015_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox015Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox015Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox015_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox015Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox015Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox015_partial_bounds {t a : ℝ} (htl : ((173/200) : ℝ) ≤ t) (htu : t ≤ ((433/500) : ℝ))
    (hal : ((977954771073013/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((979565383809013/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters015 middleDerivativeParameters015_valid middleDerivativeBox015Cells (1/20) middleDerivativeBox015Cells_valid middleDerivativeBox015_upperA middleDerivativeBox015_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox015_derivative {t : ℝ} (htl : ((173/200) : ℝ) ≤ t) (htu : t ≤ ((433/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox015_enclosure htl htu
  have hp := middleDerivativeParameters015.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters015_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox015_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((433/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox015_derivative
