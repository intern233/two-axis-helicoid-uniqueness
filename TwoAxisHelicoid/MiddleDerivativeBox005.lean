import TwoAxisHelicoid.MiddleVerticalBox005
import TwoAxisHelicoid.MiddleDerivativeBox005Cell000
import TwoAxisHelicoid.MiddleDerivativeBox005Cell001
import TwoAxisHelicoid.MiddleDerivativeBox005Cell002
import TwoAxisHelicoid.MiddleDerivativeBox005Cell003
import TwoAxisHelicoid.MiddleDerivativeBox005Cell004
import TwoAxisHelicoid.MiddleDerivativeBox005Cell005
import TwoAxisHelicoid.MiddleDerivativeBox005Cell006
import TwoAxisHelicoid.MiddleDerivativeBox005Cell007
import TwoAxisHelicoid.MiddleDerivativeBox005Cell008
import TwoAxisHelicoid.MiddleDerivativeBox005Cell009
import TwoAxisHelicoid.MiddleDerivativeBox005Cell010
import TwoAxisHelicoid.MiddleDerivativeBox005Cell011
import TwoAxisHelicoid.MiddleDerivativeBox005Cell012
import TwoAxisHelicoid.MiddleDerivativeBox005Cell013
import TwoAxisHelicoid.MiddleDerivativeBox005Cell014
import TwoAxisHelicoid.MiddleDerivativeBox005Cell015
import TwoAxisHelicoid.MiddleDerivativeBox005Cell016
import TwoAxisHelicoid.MiddleDerivativeBox005Cell017
import TwoAxisHelicoid.MiddleDerivativeBox005Cell018
import TwoAxisHelicoid.MiddleDerivativeBox005Cell019
import TwoAxisHelicoid.MiddleDerivativeBox005Cell020
import TwoAxisHelicoid.MiddleDerivativeBox005Cell021
import TwoAxisHelicoid.MiddleDerivativeBox005Cell022
import TwoAxisHelicoid.MiddleDerivativeBox005Cell023
import TwoAxisHelicoid.MiddleDerivativeBox005Cell024
import TwoAxisHelicoid.MiddleDerivativeBox005Cell025
import TwoAxisHelicoid.MiddleDerivativeBox005Cell026
import TwoAxisHelicoid.MiddleDerivativeBox005Cell027
import TwoAxisHelicoid.MiddleDerivativeBox005Cell028
import TwoAxisHelicoid.MiddleDerivativeBox005Cell029
import TwoAxisHelicoid.MiddleDerivativeBox005Cell030
import TwoAxisHelicoid.MiddleDerivativeBox005Cell031
import TwoAxisHelicoid.MiddleDerivativeBox005Cell032
import TwoAxisHelicoid.MiddleDerivativeBox005Cell033
import TwoAxisHelicoid.MiddleDerivativeBox005Cell034
import TwoAxisHelicoid.MiddleDerivativeBox005Cell035
import TwoAxisHelicoid.MiddleDerivativeBox005Cell036
import TwoAxisHelicoid.MiddleDerivativeBox005Cell037
import TwoAxisHelicoid.MiddleDerivativeBox005Cell038
import TwoAxisHelicoid.MiddleDerivativeBox005Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox005Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox005Cell000,middleDerivativeBox005Cell001,middleDerivativeBox005Cell002,middleDerivativeBox005Cell003,middleDerivativeBox005Cell004,middleDerivativeBox005Cell005,middleDerivativeBox005Cell006,middleDerivativeBox005Cell007,middleDerivativeBox005Cell008,middleDerivativeBox005Cell009,middleDerivativeBox005Cell010,middleDerivativeBox005Cell011,middleDerivativeBox005Cell012,middleDerivativeBox005Cell013,middleDerivativeBox005Cell014,middleDerivativeBox005Cell015,middleDerivativeBox005Cell016,middleDerivativeBox005Cell017,middleDerivativeBox005Cell018,middleDerivativeBox005Cell019,middleDerivativeBox005Cell020,middleDerivativeBox005Cell021,middleDerivativeBox005Cell022,middleDerivativeBox005Cell023,middleDerivativeBox005Cell024,middleDerivativeBox005Cell025,middleDerivativeBox005Cell026,middleDerivativeBox005Cell027,middleDerivativeBox005Cell028,middleDerivativeBox005Cell029,middleDerivativeBox005Cell030,middleDerivativeBox005Cell031,middleDerivativeBox005Cell032,middleDerivativeBox005Cell033,middleDerivativeBox005Cell034,middleDerivativeBox005Cell035,middleDerivativeBox005Cell036,middleDerivativeBox005Cell037,middleDerivativeBox005Cell038,middleDerivativeBox005Cell039]
theorem middleDerivativeBox005Cells_valid : ∀ i : Fin 40, (middleDerivativeBox005Cells i).Valid middleRangeSetup middleDerivativeParameters005 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox005Cell000_valid
  · exact middleDerivativeBox005Cell001_valid
  · exact middleDerivativeBox005Cell002_valid
  · exact middleDerivativeBox005Cell003_valid
  · exact middleDerivativeBox005Cell004_valid
  · exact middleDerivativeBox005Cell005_valid
  · exact middleDerivativeBox005Cell006_valid
  · exact middleDerivativeBox005Cell007_valid
  · exact middleDerivativeBox005Cell008_valid
  · exact middleDerivativeBox005Cell009_valid
  · exact middleDerivativeBox005Cell010_valid
  · exact middleDerivativeBox005Cell011_valid
  · exact middleDerivativeBox005Cell012_valid
  · exact middleDerivativeBox005Cell013_valid
  · exact middleDerivativeBox005Cell014_valid
  · exact middleDerivativeBox005Cell015_valid
  · exact middleDerivativeBox005Cell016_valid
  · exact middleDerivativeBox005Cell017_valid
  · exact middleDerivativeBox005Cell018_valid
  · exact middleDerivativeBox005Cell019_valid
  · exact middleDerivativeBox005Cell020_valid
  · exact middleDerivativeBox005Cell021_valid
  · exact middleDerivativeBox005Cell022_valid
  · exact middleDerivativeBox005Cell023_valid
  · exact middleDerivativeBox005Cell024_valid
  · exact middleDerivativeBox005Cell025_valid
  · exact middleDerivativeBox005Cell026_valid
  · exact middleDerivativeBox005Cell027_valid
  · exact middleDerivativeBox005Cell028_valid
  · exact middleDerivativeBox005Cell029_valid
  · exact middleDerivativeBox005Cell030_valid
  · exact middleDerivativeBox005Cell031_valid
  · exact middleDerivativeBox005Cell032_valid
  · exact middleDerivativeBox005Cell033_valid
  · exact middleDerivativeBox005Cell034_valid
  · exact middleDerivativeBox005Cell035_valid
  · exact middleDerivativeBox005Cell036_valid
  · exact middleDerivativeBox005Cell037_valid
  · exact middleDerivativeBox005Cell038_valid
  · exact middleDerivativeBox005Cell039_valid
theorem middleDerivativeBox005_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox005Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox005Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox005_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox005Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox005Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox005_partial_bounds {t a : ℝ} (htl : ((171/200) : ℝ) ≤ t) (htu : t ≤ ((107/125) : ℝ))
    (hal : ((972687950715697/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((974298563451697/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters005 middleDerivativeParameters005_valid middleDerivativeBox005Cells (1/20) middleDerivativeBox005Cells_valid middleDerivativeBox005_upperA middleDerivativeBox005_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox005_derivative {t : ℝ} (htl : ((171/200) : ℝ) ≤ t) (htu : t ≤ ((107/125) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox005_enclosure htl htu
  have hp := middleDerivativeParameters005.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters005_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox005_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((107/125) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox005_derivative
