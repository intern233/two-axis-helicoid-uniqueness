import TwoAxisHelicoid.MiddleVerticalBox006
import TwoAxisHelicoid.MiddleDerivativeBox006Cell000
import TwoAxisHelicoid.MiddleDerivativeBox006Cell001
import TwoAxisHelicoid.MiddleDerivativeBox006Cell002
import TwoAxisHelicoid.MiddleDerivativeBox006Cell003
import TwoAxisHelicoid.MiddleDerivativeBox006Cell004
import TwoAxisHelicoid.MiddleDerivativeBox006Cell005
import TwoAxisHelicoid.MiddleDerivativeBox006Cell006
import TwoAxisHelicoid.MiddleDerivativeBox006Cell007
import TwoAxisHelicoid.MiddleDerivativeBox006Cell008
import TwoAxisHelicoid.MiddleDerivativeBox006Cell009
import TwoAxisHelicoid.MiddleDerivativeBox006Cell010
import TwoAxisHelicoid.MiddleDerivativeBox006Cell011
import TwoAxisHelicoid.MiddleDerivativeBox006Cell012
import TwoAxisHelicoid.MiddleDerivativeBox006Cell013
import TwoAxisHelicoid.MiddleDerivativeBox006Cell014
import TwoAxisHelicoid.MiddleDerivativeBox006Cell015
import TwoAxisHelicoid.MiddleDerivativeBox006Cell016
import TwoAxisHelicoid.MiddleDerivativeBox006Cell017
import TwoAxisHelicoid.MiddleDerivativeBox006Cell018
import TwoAxisHelicoid.MiddleDerivativeBox006Cell019
import TwoAxisHelicoid.MiddleDerivativeBox006Cell020
import TwoAxisHelicoid.MiddleDerivativeBox006Cell021
import TwoAxisHelicoid.MiddleDerivativeBox006Cell022
import TwoAxisHelicoid.MiddleDerivativeBox006Cell023
import TwoAxisHelicoid.MiddleDerivativeBox006Cell024
import TwoAxisHelicoid.MiddleDerivativeBox006Cell025
import TwoAxisHelicoid.MiddleDerivativeBox006Cell026
import TwoAxisHelicoid.MiddleDerivativeBox006Cell027
import TwoAxisHelicoid.MiddleDerivativeBox006Cell028
import TwoAxisHelicoid.MiddleDerivativeBox006Cell029
import TwoAxisHelicoid.MiddleDerivativeBox006Cell030
import TwoAxisHelicoid.MiddleDerivativeBox006Cell031
import TwoAxisHelicoid.MiddleDerivativeBox006Cell032
import TwoAxisHelicoid.MiddleDerivativeBox006Cell033
import TwoAxisHelicoid.MiddleDerivativeBox006Cell034
import TwoAxisHelicoid.MiddleDerivativeBox006Cell035
import TwoAxisHelicoid.MiddleDerivativeBox006Cell036
import TwoAxisHelicoid.MiddleDerivativeBox006Cell037
import TwoAxisHelicoid.MiddleDerivativeBox006Cell038
import TwoAxisHelicoid.MiddleDerivativeBox006Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox006Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox006Cell000,middleDerivativeBox006Cell001,middleDerivativeBox006Cell002,middleDerivativeBox006Cell003,middleDerivativeBox006Cell004,middleDerivativeBox006Cell005,middleDerivativeBox006Cell006,middleDerivativeBox006Cell007,middleDerivativeBox006Cell008,middleDerivativeBox006Cell009,middleDerivativeBox006Cell010,middleDerivativeBox006Cell011,middleDerivativeBox006Cell012,middleDerivativeBox006Cell013,middleDerivativeBox006Cell014,middleDerivativeBox006Cell015,middleDerivativeBox006Cell016,middleDerivativeBox006Cell017,middleDerivativeBox006Cell018,middleDerivativeBox006Cell019,middleDerivativeBox006Cell020,middleDerivativeBox006Cell021,middleDerivativeBox006Cell022,middleDerivativeBox006Cell023,middleDerivativeBox006Cell024,middleDerivativeBox006Cell025,middleDerivativeBox006Cell026,middleDerivativeBox006Cell027,middleDerivativeBox006Cell028,middleDerivativeBox006Cell029,middleDerivativeBox006Cell030,middleDerivativeBox006Cell031,middleDerivativeBox006Cell032,middleDerivativeBox006Cell033,middleDerivativeBox006Cell034,middleDerivativeBox006Cell035,middleDerivativeBox006Cell036,middleDerivativeBox006Cell037,middleDerivativeBox006Cell038,middleDerivativeBox006Cell039]
theorem middleDerivativeBox006Cells_valid : ∀ i : Fin 40, (middleDerivativeBox006Cells i).Valid middleRangeSetup middleDerivativeParameters006 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox006Cell000_valid
  · exact middleDerivativeBox006Cell001_valid
  · exact middleDerivativeBox006Cell002_valid
  · exact middleDerivativeBox006Cell003_valid
  · exact middleDerivativeBox006Cell004_valid
  · exact middleDerivativeBox006Cell005_valid
  · exact middleDerivativeBox006Cell006_valid
  · exact middleDerivativeBox006Cell007_valid
  · exact middleDerivativeBox006Cell008_valid
  · exact middleDerivativeBox006Cell009_valid
  · exact middleDerivativeBox006Cell010_valid
  · exact middleDerivativeBox006Cell011_valid
  · exact middleDerivativeBox006Cell012_valid
  · exact middleDerivativeBox006Cell013_valid
  · exact middleDerivativeBox006Cell014_valid
  · exact middleDerivativeBox006Cell015_valid
  · exact middleDerivativeBox006Cell016_valid
  · exact middleDerivativeBox006Cell017_valid
  · exact middleDerivativeBox006Cell018_valid
  · exact middleDerivativeBox006Cell019_valid
  · exact middleDerivativeBox006Cell020_valid
  · exact middleDerivativeBox006Cell021_valid
  · exact middleDerivativeBox006Cell022_valid
  · exact middleDerivativeBox006Cell023_valid
  · exact middleDerivativeBox006Cell024_valid
  · exact middleDerivativeBox006Cell025_valid
  · exact middleDerivativeBox006Cell026_valid
  · exact middleDerivativeBox006Cell027_valid
  · exact middleDerivativeBox006Cell028_valid
  · exact middleDerivativeBox006Cell029_valid
  · exact middleDerivativeBox006Cell030_valid
  · exact middleDerivativeBox006Cell031_valid
  · exact middleDerivativeBox006Cell032_valid
  · exact middleDerivativeBox006Cell033_valid
  · exact middleDerivativeBox006Cell034_valid
  · exact middleDerivativeBox006Cell035_valid
  · exact middleDerivativeBox006Cell036_valid
  · exact middleDerivativeBox006Cell037_valid
  · exact middleDerivativeBox006Cell038_valid
  · exact middleDerivativeBox006Cell039_valid
theorem middleDerivativeBox006_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox006Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox006Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox006_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox006Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox006Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox006_partial_bounds {t a : ℝ} (htl : ((107/125) : ℝ) ≤ t) (htu : t ≤ ((857/1000) : ℝ))
    (hal : ((973210252482103/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((974820865218103/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters006 middleDerivativeParameters006_valid middleDerivativeBox006Cells (1/20) middleDerivativeBox006Cells_valid middleDerivativeBox006_upperA middleDerivativeBox006_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox006_derivative {t : ℝ} (htl : ((107/125) : ℝ) ≤ t) (htu : t ≤ ((857/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox006_enclosure htl htu
  have hp := middleDerivativeParameters006.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters006_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox006_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((857/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox006_derivative
