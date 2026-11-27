import TwoAxisHelicoid.MiddleVerticalBox024
import TwoAxisHelicoid.MiddleDerivativeBox024Cell000
import TwoAxisHelicoid.MiddleDerivativeBox024Cell001
import TwoAxisHelicoid.MiddleDerivativeBox024Cell002
import TwoAxisHelicoid.MiddleDerivativeBox024Cell003
import TwoAxisHelicoid.MiddleDerivativeBox024Cell004
import TwoAxisHelicoid.MiddleDerivativeBox024Cell005
import TwoAxisHelicoid.MiddleDerivativeBox024Cell006
import TwoAxisHelicoid.MiddleDerivativeBox024Cell007
import TwoAxisHelicoid.MiddleDerivativeBox024Cell008
import TwoAxisHelicoid.MiddleDerivativeBox024Cell009
import TwoAxisHelicoid.MiddleDerivativeBox024Cell010
import TwoAxisHelicoid.MiddleDerivativeBox024Cell011
import TwoAxisHelicoid.MiddleDerivativeBox024Cell012
import TwoAxisHelicoid.MiddleDerivativeBox024Cell013
import TwoAxisHelicoid.MiddleDerivativeBox024Cell014
import TwoAxisHelicoid.MiddleDerivativeBox024Cell015
import TwoAxisHelicoid.MiddleDerivativeBox024Cell016
import TwoAxisHelicoid.MiddleDerivativeBox024Cell017
import TwoAxisHelicoid.MiddleDerivativeBox024Cell018
import TwoAxisHelicoid.MiddleDerivativeBox024Cell019
import TwoAxisHelicoid.MiddleDerivativeBox024Cell020
import TwoAxisHelicoid.MiddleDerivativeBox024Cell021
import TwoAxisHelicoid.MiddleDerivativeBox024Cell022
import TwoAxisHelicoid.MiddleDerivativeBox024Cell023
import TwoAxisHelicoid.MiddleDerivativeBox024Cell024
import TwoAxisHelicoid.MiddleDerivativeBox024Cell025
import TwoAxisHelicoid.MiddleDerivativeBox024Cell026
import TwoAxisHelicoid.MiddleDerivativeBox024Cell027
import TwoAxisHelicoid.MiddleDerivativeBox024Cell028
import TwoAxisHelicoid.MiddleDerivativeBox024Cell029
import TwoAxisHelicoid.MiddleDerivativeBox024Cell030
import TwoAxisHelicoid.MiddleDerivativeBox024Cell031
import TwoAxisHelicoid.MiddleDerivativeBox024Cell032
import TwoAxisHelicoid.MiddleDerivativeBox024Cell033
import TwoAxisHelicoid.MiddleDerivativeBox024Cell034
import TwoAxisHelicoid.MiddleDerivativeBox024Cell035
import TwoAxisHelicoid.MiddleDerivativeBox024Cell036
import TwoAxisHelicoid.MiddleDerivativeBox024Cell037
import TwoAxisHelicoid.MiddleDerivativeBox024Cell038
import TwoAxisHelicoid.MiddleDerivativeBox024Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox024Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox024Cell000,middleDerivativeBox024Cell001,middleDerivativeBox024Cell002,middleDerivativeBox024Cell003,middleDerivativeBox024Cell004,middleDerivativeBox024Cell005,middleDerivativeBox024Cell006,middleDerivativeBox024Cell007,middleDerivativeBox024Cell008,middleDerivativeBox024Cell009,middleDerivativeBox024Cell010,middleDerivativeBox024Cell011,middleDerivativeBox024Cell012,middleDerivativeBox024Cell013,middleDerivativeBox024Cell014,middleDerivativeBox024Cell015,middleDerivativeBox024Cell016,middleDerivativeBox024Cell017,middleDerivativeBox024Cell018,middleDerivativeBox024Cell019,middleDerivativeBox024Cell020,middleDerivativeBox024Cell021,middleDerivativeBox024Cell022,middleDerivativeBox024Cell023,middleDerivativeBox024Cell024,middleDerivativeBox024Cell025,middleDerivativeBox024Cell026,middleDerivativeBox024Cell027,middleDerivativeBox024Cell028,middleDerivativeBox024Cell029,middleDerivativeBox024Cell030,middleDerivativeBox024Cell031,middleDerivativeBox024Cell032,middleDerivativeBox024Cell033,middleDerivativeBox024Cell034,middleDerivativeBox024Cell035,middleDerivativeBox024Cell036,middleDerivativeBox024Cell037,middleDerivativeBox024Cell038,middleDerivativeBox024Cell039]
theorem middleDerivativeBox024Cells_valid : ∀ i : Fin 40, (middleDerivativeBox024Cells i).Valid middleRangeSetup middleDerivativeParameters024 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox024Cell000_valid
  · exact middleDerivativeBox024Cell001_valid
  · exact middleDerivativeBox024Cell002_valid
  · exact middleDerivativeBox024Cell003_valid
  · exact middleDerivativeBox024Cell004_valid
  · exact middleDerivativeBox024Cell005_valid
  · exact middleDerivativeBox024Cell006_valid
  · exact middleDerivativeBox024Cell007_valid
  · exact middleDerivativeBox024Cell008_valid
  · exact middleDerivativeBox024Cell009_valid
  · exact middleDerivativeBox024Cell010_valid
  · exact middleDerivativeBox024Cell011_valid
  · exact middleDerivativeBox024Cell012_valid
  · exact middleDerivativeBox024Cell013_valid
  · exact middleDerivativeBox024Cell014_valid
  · exact middleDerivativeBox024Cell015_valid
  · exact middleDerivativeBox024Cell016_valid
  · exact middleDerivativeBox024Cell017_valid
  · exact middleDerivativeBox024Cell018_valid
  · exact middleDerivativeBox024Cell019_valid
  · exact middleDerivativeBox024Cell020_valid
  · exact middleDerivativeBox024Cell021_valid
  · exact middleDerivativeBox024Cell022_valid
  · exact middleDerivativeBox024Cell023_valid
  · exact middleDerivativeBox024Cell024_valid
  · exact middleDerivativeBox024Cell025_valid
  · exact middleDerivativeBox024Cell026_valid
  · exact middleDerivativeBox024Cell027_valid
  · exact middleDerivativeBox024Cell028_valid
  · exact middleDerivativeBox024Cell029_valid
  · exact middleDerivativeBox024Cell030_valid
  · exact middleDerivativeBox024Cell031_valid
  · exact middleDerivativeBox024Cell032_valid
  · exact middleDerivativeBox024Cell033_valid
  · exact middleDerivativeBox024Cell034_valid
  · exact middleDerivativeBox024Cell035_valid
  · exact middleDerivativeBox024Cell036_valid
  · exact middleDerivativeBox024Cell037_valid
  · exact middleDerivativeBox024Cell038_valid
  · exact middleDerivativeBox024Cell039_valid
theorem middleDerivativeBox024_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox024Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox024Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox024_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox024Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox024Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox024_partial_bounds {t a : ℝ} (htl : ((437/500) : ℝ) ≤ t) (htu : t ≤ ((7/8) : ℝ))
    (hal : ((982778514048823/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((984389126784823/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters024 middleDerivativeParameters024_valid middleDerivativeBox024Cells (1/20) middleDerivativeBox024Cells_valid middleDerivativeBox024_upperA middleDerivativeBox024_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox024_derivative {t : ℝ} (htl : ((437/500) : ℝ) ≤ t) (htu : t ≤ ((7/8) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox024_enclosure htl htu
  have hp := middleDerivativeParameters024.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters024_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox024_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((7/8) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox024_derivative
