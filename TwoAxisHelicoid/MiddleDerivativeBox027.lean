import TwoAxisHelicoid.MiddleVerticalBox027
import TwoAxisHelicoid.MiddleDerivativeBox027Cell000
import TwoAxisHelicoid.MiddleDerivativeBox027Cell001
import TwoAxisHelicoid.MiddleDerivativeBox027Cell002
import TwoAxisHelicoid.MiddleDerivativeBox027Cell003
import TwoAxisHelicoid.MiddleDerivativeBox027Cell004
import TwoAxisHelicoid.MiddleDerivativeBox027Cell005
import TwoAxisHelicoid.MiddleDerivativeBox027Cell006
import TwoAxisHelicoid.MiddleDerivativeBox027Cell007
import TwoAxisHelicoid.MiddleDerivativeBox027Cell008
import TwoAxisHelicoid.MiddleDerivativeBox027Cell009
import TwoAxisHelicoid.MiddleDerivativeBox027Cell010
import TwoAxisHelicoid.MiddleDerivativeBox027Cell011
import TwoAxisHelicoid.MiddleDerivativeBox027Cell012
import TwoAxisHelicoid.MiddleDerivativeBox027Cell013
import TwoAxisHelicoid.MiddleDerivativeBox027Cell014
import TwoAxisHelicoid.MiddleDerivativeBox027Cell015
import TwoAxisHelicoid.MiddleDerivativeBox027Cell016
import TwoAxisHelicoid.MiddleDerivativeBox027Cell017
import TwoAxisHelicoid.MiddleDerivativeBox027Cell018
import TwoAxisHelicoid.MiddleDerivativeBox027Cell019
import TwoAxisHelicoid.MiddleDerivativeBox027Cell020
import TwoAxisHelicoid.MiddleDerivativeBox027Cell021
import TwoAxisHelicoid.MiddleDerivativeBox027Cell022
import TwoAxisHelicoid.MiddleDerivativeBox027Cell023
import TwoAxisHelicoid.MiddleDerivativeBox027Cell024
import TwoAxisHelicoid.MiddleDerivativeBox027Cell025
import TwoAxisHelicoid.MiddleDerivativeBox027Cell026
import TwoAxisHelicoid.MiddleDerivativeBox027Cell027
import TwoAxisHelicoid.MiddleDerivativeBox027Cell028
import TwoAxisHelicoid.MiddleDerivativeBox027Cell029
import TwoAxisHelicoid.MiddleDerivativeBox027Cell030
import TwoAxisHelicoid.MiddleDerivativeBox027Cell031
import TwoAxisHelicoid.MiddleDerivativeBox027Cell032
import TwoAxisHelicoid.MiddleDerivativeBox027Cell033
import TwoAxisHelicoid.MiddleDerivativeBox027Cell034
import TwoAxisHelicoid.MiddleDerivativeBox027Cell035
import TwoAxisHelicoid.MiddleDerivativeBox027Cell036
import TwoAxisHelicoid.MiddleDerivativeBox027Cell037
import TwoAxisHelicoid.MiddleDerivativeBox027Cell038
import TwoAxisHelicoid.MiddleDerivativeBox027Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox027Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox027Cell000,middleDerivativeBox027Cell001,middleDerivativeBox027Cell002,middleDerivativeBox027Cell003,middleDerivativeBox027Cell004,middleDerivativeBox027Cell005,middleDerivativeBox027Cell006,middleDerivativeBox027Cell007,middleDerivativeBox027Cell008,middleDerivativeBox027Cell009,middleDerivativeBox027Cell010,middleDerivativeBox027Cell011,middleDerivativeBox027Cell012,middleDerivativeBox027Cell013,middleDerivativeBox027Cell014,middleDerivativeBox027Cell015,middleDerivativeBox027Cell016,middleDerivativeBox027Cell017,middleDerivativeBox027Cell018,middleDerivativeBox027Cell019,middleDerivativeBox027Cell020,middleDerivativeBox027Cell021,middleDerivativeBox027Cell022,middleDerivativeBox027Cell023,middleDerivativeBox027Cell024,middleDerivativeBox027Cell025,middleDerivativeBox027Cell026,middleDerivativeBox027Cell027,middleDerivativeBox027Cell028,middleDerivativeBox027Cell029,middleDerivativeBox027Cell030,middleDerivativeBox027Cell031,middleDerivativeBox027Cell032,middleDerivativeBox027Cell033,middleDerivativeBox027Cell034,middleDerivativeBox027Cell035,middleDerivativeBox027Cell036,middleDerivativeBox027Cell037,middleDerivativeBox027Cell038,middleDerivativeBox027Cell039]
theorem middleDerivativeBox027Cells_valid : ∀ i : Fin 40, (middleDerivativeBox027Cells i).Valid middleRangeSetup middleDerivativeParameters027 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox027Cell000_valid
  · exact middleDerivativeBox027Cell001_valid
  · exact middleDerivativeBox027Cell002_valid
  · exact middleDerivativeBox027Cell003_valid
  · exact middleDerivativeBox027Cell004_valid
  · exact middleDerivativeBox027Cell005_valid
  · exact middleDerivativeBox027Cell006_valid
  · exact middleDerivativeBox027Cell007_valid
  · exact middleDerivativeBox027Cell008_valid
  · exact middleDerivativeBox027Cell009_valid
  · exact middleDerivativeBox027Cell010_valid
  · exact middleDerivativeBox027Cell011_valid
  · exact middleDerivativeBox027Cell012_valid
  · exact middleDerivativeBox027Cell013_valid
  · exact middleDerivativeBox027Cell014_valid
  · exact middleDerivativeBox027Cell015_valid
  · exact middleDerivativeBox027Cell016_valid
  · exact middleDerivativeBox027Cell017_valid
  · exact middleDerivativeBox027Cell018_valid
  · exact middleDerivativeBox027Cell019_valid
  · exact middleDerivativeBox027Cell020_valid
  · exact middleDerivativeBox027Cell021_valid
  · exact middleDerivativeBox027Cell022_valid
  · exact middleDerivativeBox027Cell023_valid
  · exact middleDerivativeBox027Cell024_valid
  · exact middleDerivativeBox027Cell025_valid
  · exact middleDerivativeBox027Cell026_valid
  · exact middleDerivativeBox027Cell027_valid
  · exact middleDerivativeBox027Cell028_valid
  · exact middleDerivativeBox027Cell029_valid
  · exact middleDerivativeBox027Cell030_valid
  · exact middleDerivativeBox027Cell031_valid
  · exact middleDerivativeBox027Cell032_valid
  · exact middleDerivativeBox027Cell033_valid
  · exact middleDerivativeBox027Cell034_valid
  · exact middleDerivativeBox027Cell035_valid
  · exact middleDerivativeBox027Cell036_valid
  · exact middleDerivativeBox027Cell037_valid
  · exact middleDerivativeBox027Cell038_valid
  · exact middleDerivativeBox027Cell039_valid
theorem middleDerivativeBox027_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox027Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox027Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox027_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox027Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox027Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox027_partial_bounds {t a : ℝ} (htl : ((877/1000) : ℝ) ≤ t) (htu : t ≤ ((439/500) : ℝ))
    (hal : ((984404132502007/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((986014745238007/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters027 middleDerivativeParameters027_valid middleDerivativeBox027Cells (1/20) middleDerivativeBox027Cells_valid middleDerivativeBox027_upperA middleDerivativeBox027_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox027_derivative {t : ℝ} (htl : ((877/1000) : ℝ) ≤ t) (htu : t ≤ ((439/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox027_enclosure htl htu
  have hp := middleDerivativeParameters027.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters027_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox027_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((439/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox027_derivative
