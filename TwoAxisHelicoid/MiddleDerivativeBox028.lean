import TwoAxisHelicoid.MiddleVerticalBox028
import TwoAxisHelicoid.MiddleDerivativeBox028Cell000
import TwoAxisHelicoid.MiddleDerivativeBox028Cell001
import TwoAxisHelicoid.MiddleDerivativeBox028Cell002
import TwoAxisHelicoid.MiddleDerivativeBox028Cell003
import TwoAxisHelicoid.MiddleDerivativeBox028Cell004
import TwoAxisHelicoid.MiddleDerivativeBox028Cell005
import TwoAxisHelicoid.MiddleDerivativeBox028Cell006
import TwoAxisHelicoid.MiddleDerivativeBox028Cell007
import TwoAxisHelicoid.MiddleDerivativeBox028Cell008
import TwoAxisHelicoid.MiddleDerivativeBox028Cell009
import TwoAxisHelicoid.MiddleDerivativeBox028Cell010
import TwoAxisHelicoid.MiddleDerivativeBox028Cell011
import TwoAxisHelicoid.MiddleDerivativeBox028Cell012
import TwoAxisHelicoid.MiddleDerivativeBox028Cell013
import TwoAxisHelicoid.MiddleDerivativeBox028Cell014
import TwoAxisHelicoid.MiddleDerivativeBox028Cell015
import TwoAxisHelicoid.MiddleDerivativeBox028Cell016
import TwoAxisHelicoid.MiddleDerivativeBox028Cell017
import TwoAxisHelicoid.MiddleDerivativeBox028Cell018
import TwoAxisHelicoid.MiddleDerivativeBox028Cell019
import TwoAxisHelicoid.MiddleDerivativeBox028Cell020
import TwoAxisHelicoid.MiddleDerivativeBox028Cell021
import TwoAxisHelicoid.MiddleDerivativeBox028Cell022
import TwoAxisHelicoid.MiddleDerivativeBox028Cell023
import TwoAxisHelicoid.MiddleDerivativeBox028Cell024
import TwoAxisHelicoid.MiddleDerivativeBox028Cell025
import TwoAxisHelicoid.MiddleDerivativeBox028Cell026
import TwoAxisHelicoid.MiddleDerivativeBox028Cell027
import TwoAxisHelicoid.MiddleDerivativeBox028Cell028
import TwoAxisHelicoid.MiddleDerivativeBox028Cell029
import TwoAxisHelicoid.MiddleDerivativeBox028Cell030
import TwoAxisHelicoid.MiddleDerivativeBox028Cell031
import TwoAxisHelicoid.MiddleDerivativeBox028Cell032
import TwoAxisHelicoid.MiddleDerivativeBox028Cell033
import TwoAxisHelicoid.MiddleDerivativeBox028Cell034
import TwoAxisHelicoid.MiddleDerivativeBox028Cell035
import TwoAxisHelicoid.MiddleDerivativeBox028Cell036
import TwoAxisHelicoid.MiddleDerivativeBox028Cell037
import TwoAxisHelicoid.MiddleDerivativeBox028Cell038
import TwoAxisHelicoid.MiddleDerivativeBox028Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox028Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox028Cell000,middleDerivativeBox028Cell001,middleDerivativeBox028Cell002,middleDerivativeBox028Cell003,middleDerivativeBox028Cell004,middleDerivativeBox028Cell005,middleDerivativeBox028Cell006,middleDerivativeBox028Cell007,middleDerivativeBox028Cell008,middleDerivativeBox028Cell009,middleDerivativeBox028Cell010,middleDerivativeBox028Cell011,middleDerivativeBox028Cell012,middleDerivativeBox028Cell013,middleDerivativeBox028Cell014,middleDerivativeBox028Cell015,middleDerivativeBox028Cell016,middleDerivativeBox028Cell017,middleDerivativeBox028Cell018,middleDerivativeBox028Cell019,middleDerivativeBox028Cell020,middleDerivativeBox028Cell021,middleDerivativeBox028Cell022,middleDerivativeBox028Cell023,middleDerivativeBox028Cell024,middleDerivativeBox028Cell025,middleDerivativeBox028Cell026,middleDerivativeBox028Cell027,middleDerivativeBox028Cell028,middleDerivativeBox028Cell029,middleDerivativeBox028Cell030,middleDerivativeBox028Cell031,middleDerivativeBox028Cell032,middleDerivativeBox028Cell033,middleDerivativeBox028Cell034,middleDerivativeBox028Cell035,middleDerivativeBox028Cell036,middleDerivativeBox028Cell037,middleDerivativeBox028Cell038,middleDerivativeBox028Cell039]
theorem middleDerivativeBox028Cells_valid : ∀ i : Fin 40, (middleDerivativeBox028Cells i).Valid middleRangeSetup middleDerivativeParameters028 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox028Cell000_valid
  · exact middleDerivativeBox028Cell001_valid
  · exact middleDerivativeBox028Cell002_valid
  · exact middleDerivativeBox028Cell003_valid
  · exact middleDerivativeBox028Cell004_valid
  · exact middleDerivativeBox028Cell005_valid
  · exact middleDerivativeBox028Cell006_valid
  · exact middleDerivativeBox028Cell007_valid
  · exact middleDerivativeBox028Cell008_valid
  · exact middleDerivativeBox028Cell009_valid
  · exact middleDerivativeBox028Cell010_valid
  · exact middleDerivativeBox028Cell011_valid
  · exact middleDerivativeBox028Cell012_valid
  · exact middleDerivativeBox028Cell013_valid
  · exact middleDerivativeBox028Cell014_valid
  · exact middleDerivativeBox028Cell015_valid
  · exact middleDerivativeBox028Cell016_valid
  · exact middleDerivativeBox028Cell017_valid
  · exact middleDerivativeBox028Cell018_valid
  · exact middleDerivativeBox028Cell019_valid
  · exact middleDerivativeBox028Cell020_valid
  · exact middleDerivativeBox028Cell021_valid
  · exact middleDerivativeBox028Cell022_valid
  · exact middleDerivativeBox028Cell023_valid
  · exact middleDerivativeBox028Cell024_valid
  · exact middleDerivativeBox028Cell025_valid
  · exact middleDerivativeBox028Cell026_valid
  · exact middleDerivativeBox028Cell027_valid
  · exact middleDerivativeBox028Cell028_valid
  · exact middleDerivativeBox028Cell029_valid
  · exact middleDerivativeBox028Cell030_valid
  · exact middleDerivativeBox028Cell031_valid
  · exact middleDerivativeBox028Cell032_valid
  · exact middleDerivativeBox028Cell033_valid
  · exact middleDerivativeBox028Cell034_valid
  · exact middleDerivativeBox028Cell035_valid
  · exact middleDerivativeBox028Cell036_valid
  · exact middleDerivativeBox028Cell037_valid
  · exact middleDerivativeBox028Cell038_valid
  · exact middleDerivativeBox028Cell039_valid
theorem middleDerivativeBox028_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox028Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox028Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox028_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox028Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox028Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox028_partial_bounds {t a : ℝ} (htl : ((439/500) : ℝ) ≤ t) (htu : t ≤ ((879/1000) : ℝ))
    (hal : ((984947979621833/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((986558592357833/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters028 middleDerivativeParameters028_valid middleDerivativeBox028Cells (1/20) middleDerivativeBox028Cells_valid middleDerivativeBox028_upperA middleDerivativeBox028_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox028_derivative {t : ℝ} (htl : ((439/500) : ℝ) ≤ t) (htu : t ≤ ((879/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox028_enclosure htl htu
  have hp := middleDerivativeParameters028.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters028_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox028_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((879/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox028_derivative
