import TwoAxisHelicoid.MiddleVerticalBox031
import TwoAxisHelicoid.MiddleDerivativeBox031Cell000
import TwoAxisHelicoid.MiddleDerivativeBox031Cell001
import TwoAxisHelicoid.MiddleDerivativeBox031Cell002
import TwoAxisHelicoid.MiddleDerivativeBox031Cell003
import TwoAxisHelicoid.MiddleDerivativeBox031Cell004
import TwoAxisHelicoid.MiddleDerivativeBox031Cell005
import TwoAxisHelicoid.MiddleDerivativeBox031Cell006
import TwoAxisHelicoid.MiddleDerivativeBox031Cell007
import TwoAxisHelicoid.MiddleDerivativeBox031Cell008
import TwoAxisHelicoid.MiddleDerivativeBox031Cell009
import TwoAxisHelicoid.MiddleDerivativeBox031Cell010
import TwoAxisHelicoid.MiddleDerivativeBox031Cell011
import TwoAxisHelicoid.MiddleDerivativeBox031Cell012
import TwoAxisHelicoid.MiddleDerivativeBox031Cell013
import TwoAxisHelicoid.MiddleDerivativeBox031Cell014
import TwoAxisHelicoid.MiddleDerivativeBox031Cell015
import TwoAxisHelicoid.MiddleDerivativeBox031Cell016
import TwoAxisHelicoid.MiddleDerivativeBox031Cell017
import TwoAxisHelicoid.MiddleDerivativeBox031Cell018
import TwoAxisHelicoid.MiddleDerivativeBox031Cell019
import TwoAxisHelicoid.MiddleDerivativeBox031Cell020
import TwoAxisHelicoid.MiddleDerivativeBox031Cell021
import TwoAxisHelicoid.MiddleDerivativeBox031Cell022
import TwoAxisHelicoid.MiddleDerivativeBox031Cell023
import TwoAxisHelicoid.MiddleDerivativeBox031Cell024
import TwoAxisHelicoid.MiddleDerivativeBox031Cell025
import TwoAxisHelicoid.MiddleDerivativeBox031Cell026
import TwoAxisHelicoid.MiddleDerivativeBox031Cell027
import TwoAxisHelicoid.MiddleDerivativeBox031Cell028
import TwoAxisHelicoid.MiddleDerivativeBox031Cell029
import TwoAxisHelicoid.MiddleDerivativeBox031Cell030
import TwoAxisHelicoid.MiddleDerivativeBox031Cell031
import TwoAxisHelicoid.MiddleDerivativeBox031Cell032
import TwoAxisHelicoid.MiddleDerivativeBox031Cell033
import TwoAxisHelicoid.MiddleDerivativeBox031Cell034
import TwoAxisHelicoid.MiddleDerivativeBox031Cell035
import TwoAxisHelicoid.MiddleDerivativeBox031Cell036
import TwoAxisHelicoid.MiddleDerivativeBox031Cell037
import TwoAxisHelicoid.MiddleDerivativeBox031Cell038
import TwoAxisHelicoid.MiddleDerivativeBox031Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox031Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox031Cell000,middleDerivativeBox031Cell001,middleDerivativeBox031Cell002,middleDerivativeBox031Cell003,middleDerivativeBox031Cell004,middleDerivativeBox031Cell005,middleDerivativeBox031Cell006,middleDerivativeBox031Cell007,middleDerivativeBox031Cell008,middleDerivativeBox031Cell009,middleDerivativeBox031Cell010,middleDerivativeBox031Cell011,middleDerivativeBox031Cell012,middleDerivativeBox031Cell013,middleDerivativeBox031Cell014,middleDerivativeBox031Cell015,middleDerivativeBox031Cell016,middleDerivativeBox031Cell017,middleDerivativeBox031Cell018,middleDerivativeBox031Cell019,middleDerivativeBox031Cell020,middleDerivativeBox031Cell021,middleDerivativeBox031Cell022,middleDerivativeBox031Cell023,middleDerivativeBox031Cell024,middleDerivativeBox031Cell025,middleDerivativeBox031Cell026,middleDerivativeBox031Cell027,middleDerivativeBox031Cell028,middleDerivativeBox031Cell029,middleDerivativeBox031Cell030,middleDerivativeBox031Cell031,middleDerivativeBox031Cell032,middleDerivativeBox031Cell033,middleDerivativeBox031Cell034,middleDerivativeBox031Cell035,middleDerivativeBox031Cell036,middleDerivativeBox031Cell037,middleDerivativeBox031Cell038,middleDerivativeBox031Cell039]
theorem middleDerivativeBox031Cells_valid : ∀ i : Fin 40, (middleDerivativeBox031Cells i).Valid middleRangeSetup middleDerivativeParameters031 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox031Cell000_valid
  · exact middleDerivativeBox031Cell001_valid
  · exact middleDerivativeBox031Cell002_valid
  · exact middleDerivativeBox031Cell003_valid
  · exact middleDerivativeBox031Cell004_valid
  · exact middleDerivativeBox031Cell005_valid
  · exact middleDerivativeBox031Cell006_valid
  · exact middleDerivativeBox031Cell007_valid
  · exact middleDerivativeBox031Cell008_valid
  · exact middleDerivativeBox031Cell009_valid
  · exact middleDerivativeBox031Cell010_valid
  · exact middleDerivativeBox031Cell011_valid
  · exact middleDerivativeBox031Cell012_valid
  · exact middleDerivativeBox031Cell013_valid
  · exact middleDerivativeBox031Cell014_valid
  · exact middleDerivativeBox031Cell015_valid
  · exact middleDerivativeBox031Cell016_valid
  · exact middleDerivativeBox031Cell017_valid
  · exact middleDerivativeBox031Cell018_valid
  · exact middleDerivativeBox031Cell019_valid
  · exact middleDerivativeBox031Cell020_valid
  · exact middleDerivativeBox031Cell021_valid
  · exact middleDerivativeBox031Cell022_valid
  · exact middleDerivativeBox031Cell023_valid
  · exact middleDerivativeBox031Cell024_valid
  · exact middleDerivativeBox031Cell025_valid
  · exact middleDerivativeBox031Cell026_valid
  · exact middleDerivativeBox031Cell027_valid
  · exact middleDerivativeBox031Cell028_valid
  · exact middleDerivativeBox031Cell029_valid
  · exact middleDerivativeBox031Cell030_valid
  · exact middleDerivativeBox031Cell031_valid
  · exact middleDerivativeBox031Cell032_valid
  · exact middleDerivativeBox031Cell033_valid
  · exact middleDerivativeBox031Cell034_valid
  · exact middleDerivativeBox031Cell035_valid
  · exact middleDerivativeBox031Cell036_valid
  · exact middleDerivativeBox031Cell037_valid
  · exact middleDerivativeBox031Cell038_valid
  · exact middleDerivativeBox031Cell039_valid
theorem middleDerivativeBox031_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox031Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox031Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox031_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox031Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox031Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox031_partial_bounds {t a : ℝ} (htl : ((881/1000) : ℝ) ≤ t) (htu : t ≤ ((441/500) : ℝ))
    (hal : ((197317091189897/329853488332800) : ℝ) ≤ a) (hau : a ≤ ((197639213737097/329853488332800) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters031 middleDerivativeParameters031_valid middleDerivativeBox031Cells (1/20) middleDerivativeBox031Cells_valid middleDerivativeBox031_upperA middleDerivativeBox031_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox031_derivative {t : ℝ} (htl : ((881/1000) : ℝ) ≤ t) (htu : t ≤ ((441/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox031_enclosure htl htu
  have hp := middleDerivativeParameters031.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters031_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox031_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((441/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox031_derivative
