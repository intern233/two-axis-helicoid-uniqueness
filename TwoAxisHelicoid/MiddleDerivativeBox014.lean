import TwoAxisHelicoid.MiddleVerticalBox014
import TwoAxisHelicoid.MiddleDerivativeBox014Cell000
import TwoAxisHelicoid.MiddleDerivativeBox014Cell001
import TwoAxisHelicoid.MiddleDerivativeBox014Cell002
import TwoAxisHelicoid.MiddleDerivativeBox014Cell003
import TwoAxisHelicoid.MiddleDerivativeBox014Cell004
import TwoAxisHelicoid.MiddleDerivativeBox014Cell005
import TwoAxisHelicoid.MiddleDerivativeBox014Cell006
import TwoAxisHelicoid.MiddleDerivativeBox014Cell007
import TwoAxisHelicoid.MiddleDerivativeBox014Cell008
import TwoAxisHelicoid.MiddleDerivativeBox014Cell009
import TwoAxisHelicoid.MiddleDerivativeBox014Cell010
import TwoAxisHelicoid.MiddleDerivativeBox014Cell011
import TwoAxisHelicoid.MiddleDerivativeBox014Cell012
import TwoAxisHelicoid.MiddleDerivativeBox014Cell013
import TwoAxisHelicoid.MiddleDerivativeBox014Cell014
import TwoAxisHelicoid.MiddleDerivativeBox014Cell015
import TwoAxisHelicoid.MiddleDerivativeBox014Cell016
import TwoAxisHelicoid.MiddleDerivativeBox014Cell017
import TwoAxisHelicoid.MiddleDerivativeBox014Cell018
import TwoAxisHelicoid.MiddleDerivativeBox014Cell019
import TwoAxisHelicoid.MiddleDerivativeBox014Cell020
import TwoAxisHelicoid.MiddleDerivativeBox014Cell021
import TwoAxisHelicoid.MiddleDerivativeBox014Cell022
import TwoAxisHelicoid.MiddleDerivativeBox014Cell023
import TwoAxisHelicoid.MiddleDerivativeBox014Cell024
import TwoAxisHelicoid.MiddleDerivativeBox014Cell025
import TwoAxisHelicoid.MiddleDerivativeBox014Cell026
import TwoAxisHelicoid.MiddleDerivativeBox014Cell027
import TwoAxisHelicoid.MiddleDerivativeBox014Cell028
import TwoAxisHelicoid.MiddleDerivativeBox014Cell029
import TwoAxisHelicoid.MiddleDerivativeBox014Cell030
import TwoAxisHelicoid.MiddleDerivativeBox014Cell031
import TwoAxisHelicoid.MiddleDerivativeBox014Cell032
import TwoAxisHelicoid.MiddleDerivativeBox014Cell033
import TwoAxisHelicoid.MiddleDerivativeBox014Cell034
import TwoAxisHelicoid.MiddleDerivativeBox014Cell035
import TwoAxisHelicoid.MiddleDerivativeBox014Cell036
import TwoAxisHelicoid.MiddleDerivativeBox014Cell037
import TwoAxisHelicoid.MiddleDerivativeBox014Cell038
import TwoAxisHelicoid.MiddleDerivativeBox014Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox014Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox014Cell000,middleDerivativeBox014Cell001,middleDerivativeBox014Cell002,middleDerivativeBox014Cell003,middleDerivativeBox014Cell004,middleDerivativeBox014Cell005,middleDerivativeBox014Cell006,middleDerivativeBox014Cell007,middleDerivativeBox014Cell008,middleDerivativeBox014Cell009,middleDerivativeBox014Cell010,middleDerivativeBox014Cell011,middleDerivativeBox014Cell012,middleDerivativeBox014Cell013,middleDerivativeBox014Cell014,middleDerivativeBox014Cell015,middleDerivativeBox014Cell016,middleDerivativeBox014Cell017,middleDerivativeBox014Cell018,middleDerivativeBox014Cell019,middleDerivativeBox014Cell020,middleDerivativeBox014Cell021,middleDerivativeBox014Cell022,middleDerivativeBox014Cell023,middleDerivativeBox014Cell024,middleDerivativeBox014Cell025,middleDerivativeBox014Cell026,middleDerivativeBox014Cell027,middleDerivativeBox014Cell028,middleDerivativeBox014Cell029,middleDerivativeBox014Cell030,middleDerivativeBox014Cell031,middleDerivativeBox014Cell032,middleDerivativeBox014Cell033,middleDerivativeBox014Cell034,middleDerivativeBox014Cell035,middleDerivativeBox014Cell036,middleDerivativeBox014Cell037,middleDerivativeBox014Cell038,middleDerivativeBox014Cell039]
theorem middleDerivativeBox014Cells_valid : ∀ i : Fin 40, (middleDerivativeBox014Cells i).Valid middleRangeSetup middleDerivativeParameters014 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox014Cell000_valid
  · exact middleDerivativeBox014Cell001_valid
  · exact middleDerivativeBox014Cell002_valid
  · exact middleDerivativeBox014Cell003_valid
  · exact middleDerivativeBox014Cell004_valid
  · exact middleDerivativeBox014Cell005_valid
  · exact middleDerivativeBox014Cell006_valid
  · exact middleDerivativeBox014Cell007_valid
  · exact middleDerivativeBox014Cell008_valid
  · exact middleDerivativeBox014Cell009_valid
  · exact middleDerivativeBox014Cell010_valid
  · exact middleDerivativeBox014Cell011_valid
  · exact middleDerivativeBox014Cell012_valid
  · exact middleDerivativeBox014Cell013_valid
  · exact middleDerivativeBox014Cell014_valid
  · exact middleDerivativeBox014Cell015_valid
  · exact middleDerivativeBox014Cell016_valid
  · exact middleDerivativeBox014Cell017_valid
  · exact middleDerivativeBox014Cell018_valid
  · exact middleDerivativeBox014Cell019_valid
  · exact middleDerivativeBox014Cell020_valid
  · exact middleDerivativeBox014Cell021_valid
  · exact middleDerivativeBox014Cell022_valid
  · exact middleDerivativeBox014Cell023_valid
  · exact middleDerivativeBox014Cell024_valid
  · exact middleDerivativeBox014Cell025_valid
  · exact middleDerivativeBox014Cell026_valid
  · exact middleDerivativeBox014Cell027_valid
  · exact middleDerivativeBox014Cell028_valid
  · exact middleDerivativeBox014Cell029_valid
  · exact middleDerivativeBox014Cell030_valid
  · exact middleDerivativeBox014Cell031_valid
  · exact middleDerivativeBox014Cell032_valid
  · exact middleDerivativeBox014Cell033_valid
  · exact middleDerivativeBox014Cell034_valid
  · exact middleDerivativeBox014Cell035_valid
  · exact middleDerivativeBox014Cell036_valid
  · exact middleDerivativeBox014Cell037_valid
  · exact middleDerivativeBox014Cell038_valid
  · exact middleDerivativeBox014Cell039_valid
theorem middleDerivativeBox014_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox014Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox014Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox014_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox014Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox014Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox014_partial_bounds {t a : ℝ} (htl : ((108/125) : ℝ) ≤ t) (htu : t ≤ ((173/200) : ℝ))
    (hal : ((977423700124141/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((979034312860141/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters014 middleDerivativeParameters014_valid middleDerivativeBox014Cells (1/20) middleDerivativeBox014Cells_valid middleDerivativeBox014_upperA middleDerivativeBox014_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox014_derivative {t : ℝ} (htl : ((108/125) : ℝ) ≤ t) (htu : t ≤ ((173/200) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox014_enclosure htl htu
  have hp := middleDerivativeParameters014.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters014_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox014_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((173/200) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox014_derivative
