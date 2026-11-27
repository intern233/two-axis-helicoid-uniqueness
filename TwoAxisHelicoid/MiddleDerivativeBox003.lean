import TwoAxisHelicoid.MiddleVerticalBox003
import TwoAxisHelicoid.MiddleDerivativeBox003Cell000
import TwoAxisHelicoid.MiddleDerivativeBox003Cell001
import TwoAxisHelicoid.MiddleDerivativeBox003Cell002
import TwoAxisHelicoid.MiddleDerivativeBox003Cell003
import TwoAxisHelicoid.MiddleDerivativeBox003Cell004
import TwoAxisHelicoid.MiddleDerivativeBox003Cell005
import TwoAxisHelicoid.MiddleDerivativeBox003Cell006
import TwoAxisHelicoid.MiddleDerivativeBox003Cell007
import TwoAxisHelicoid.MiddleDerivativeBox003Cell008
import TwoAxisHelicoid.MiddleDerivativeBox003Cell009
import TwoAxisHelicoid.MiddleDerivativeBox003Cell010
import TwoAxisHelicoid.MiddleDerivativeBox003Cell011
import TwoAxisHelicoid.MiddleDerivativeBox003Cell012
import TwoAxisHelicoid.MiddleDerivativeBox003Cell013
import TwoAxisHelicoid.MiddleDerivativeBox003Cell014
import TwoAxisHelicoid.MiddleDerivativeBox003Cell015
import TwoAxisHelicoid.MiddleDerivativeBox003Cell016
import TwoAxisHelicoid.MiddleDerivativeBox003Cell017
import TwoAxisHelicoid.MiddleDerivativeBox003Cell018
import TwoAxisHelicoid.MiddleDerivativeBox003Cell019
import TwoAxisHelicoid.MiddleDerivativeBox003Cell020
import TwoAxisHelicoid.MiddleDerivativeBox003Cell021
import TwoAxisHelicoid.MiddleDerivativeBox003Cell022
import TwoAxisHelicoid.MiddleDerivativeBox003Cell023
import TwoAxisHelicoid.MiddleDerivativeBox003Cell024
import TwoAxisHelicoid.MiddleDerivativeBox003Cell025
import TwoAxisHelicoid.MiddleDerivativeBox003Cell026
import TwoAxisHelicoid.MiddleDerivativeBox003Cell027
import TwoAxisHelicoid.MiddleDerivativeBox003Cell028
import TwoAxisHelicoid.MiddleDerivativeBox003Cell029
import TwoAxisHelicoid.MiddleDerivativeBox003Cell030
import TwoAxisHelicoid.MiddleDerivativeBox003Cell031
import TwoAxisHelicoid.MiddleDerivativeBox003Cell032
import TwoAxisHelicoid.MiddleDerivativeBox003Cell033
import TwoAxisHelicoid.MiddleDerivativeBox003Cell034
import TwoAxisHelicoid.MiddleDerivativeBox003Cell035
import TwoAxisHelicoid.MiddleDerivativeBox003Cell036
import TwoAxisHelicoid.MiddleDerivativeBox003Cell037
import TwoAxisHelicoid.MiddleDerivativeBox003Cell038
import TwoAxisHelicoid.MiddleDerivativeBox003Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox003Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox003Cell000,middleDerivativeBox003Cell001,middleDerivativeBox003Cell002,middleDerivativeBox003Cell003,middleDerivativeBox003Cell004,middleDerivativeBox003Cell005,middleDerivativeBox003Cell006,middleDerivativeBox003Cell007,middleDerivativeBox003Cell008,middleDerivativeBox003Cell009,middleDerivativeBox003Cell010,middleDerivativeBox003Cell011,middleDerivativeBox003Cell012,middleDerivativeBox003Cell013,middleDerivativeBox003Cell014,middleDerivativeBox003Cell015,middleDerivativeBox003Cell016,middleDerivativeBox003Cell017,middleDerivativeBox003Cell018,middleDerivativeBox003Cell019,middleDerivativeBox003Cell020,middleDerivativeBox003Cell021,middleDerivativeBox003Cell022,middleDerivativeBox003Cell023,middleDerivativeBox003Cell024,middleDerivativeBox003Cell025,middleDerivativeBox003Cell026,middleDerivativeBox003Cell027,middleDerivativeBox003Cell028,middleDerivativeBox003Cell029,middleDerivativeBox003Cell030,middleDerivativeBox003Cell031,middleDerivativeBox003Cell032,middleDerivativeBox003Cell033,middleDerivativeBox003Cell034,middleDerivativeBox003Cell035,middleDerivativeBox003Cell036,middleDerivativeBox003Cell037,middleDerivativeBox003Cell038,middleDerivativeBox003Cell039]
theorem middleDerivativeBox003Cells_valid : ∀ i : Fin 40, (middleDerivativeBox003Cells i).Valid middleRangeSetup middleDerivativeParameters003 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox003Cell000_valid
  · exact middleDerivativeBox003Cell001_valid
  · exact middleDerivativeBox003Cell002_valid
  · exact middleDerivativeBox003Cell003_valid
  · exact middleDerivativeBox003Cell004_valid
  · exact middleDerivativeBox003Cell005_valid
  · exact middleDerivativeBox003Cell006_valid
  · exact middleDerivativeBox003Cell007_valid
  · exact middleDerivativeBox003Cell008_valid
  · exact middleDerivativeBox003Cell009_valid
  · exact middleDerivativeBox003Cell010_valid
  · exact middleDerivativeBox003Cell011_valid
  · exact middleDerivativeBox003Cell012_valid
  · exact middleDerivativeBox003Cell013_valid
  · exact middleDerivativeBox003Cell014_valid
  · exact middleDerivativeBox003Cell015_valid
  · exact middleDerivativeBox003Cell016_valid
  · exact middleDerivativeBox003Cell017_valid
  · exact middleDerivativeBox003Cell018_valid
  · exact middleDerivativeBox003Cell019_valid
  · exact middleDerivativeBox003Cell020_valid
  · exact middleDerivativeBox003Cell021_valid
  · exact middleDerivativeBox003Cell022_valid
  · exact middleDerivativeBox003Cell023_valid
  · exact middleDerivativeBox003Cell024_valid
  · exact middleDerivativeBox003Cell025_valid
  · exact middleDerivativeBox003Cell026_valid
  · exact middleDerivativeBox003Cell027_valid
  · exact middleDerivativeBox003Cell028_valid
  · exact middleDerivativeBox003Cell029_valid
  · exact middleDerivativeBox003Cell030_valid
  · exact middleDerivativeBox003Cell031_valid
  · exact middleDerivativeBox003Cell032_valid
  · exact middleDerivativeBox003Cell033_valid
  · exact middleDerivativeBox003Cell034_valid
  · exact middleDerivativeBox003Cell035_valid
  · exact middleDerivativeBox003Cell036_valid
  · exact middleDerivativeBox003Cell037_valid
  · exact middleDerivativeBox003Cell038_valid
  · exact middleDerivativeBox003Cell039_valid
theorem middleDerivativeBox003_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox003Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox003Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox003_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox003Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox003Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox003_partial_bounds {t a : ℝ} (htl : ((853/1000) : ℝ) ≤ t) (htu : t ≤ ((427/500) : ℝ))
    (hal : ((971646258964651/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((973256871700651/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters003 middleDerivativeParameters003_valid middleDerivativeBox003Cells (1/20) middleDerivativeBox003Cells_valid middleDerivativeBox003_upperA middleDerivativeBox003_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox003_derivative {t : ℝ} (htl : ((853/1000) : ℝ) ≤ t) (htu : t ≤ ((427/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox003_enclosure htl htu
  have hp := middleDerivativeParameters003.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters003_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox003_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((427/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox003_derivative
