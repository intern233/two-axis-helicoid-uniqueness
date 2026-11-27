import TwoAxisHelicoid.MiddleVerticalBox017
import TwoAxisHelicoid.MiddleDerivativeBox017Cell000
import TwoAxisHelicoid.MiddleDerivativeBox017Cell001
import TwoAxisHelicoid.MiddleDerivativeBox017Cell002
import TwoAxisHelicoid.MiddleDerivativeBox017Cell003
import TwoAxisHelicoid.MiddleDerivativeBox017Cell004
import TwoAxisHelicoid.MiddleDerivativeBox017Cell005
import TwoAxisHelicoid.MiddleDerivativeBox017Cell006
import TwoAxisHelicoid.MiddleDerivativeBox017Cell007
import TwoAxisHelicoid.MiddleDerivativeBox017Cell008
import TwoAxisHelicoid.MiddleDerivativeBox017Cell009
import TwoAxisHelicoid.MiddleDerivativeBox017Cell010
import TwoAxisHelicoid.MiddleDerivativeBox017Cell011
import TwoAxisHelicoid.MiddleDerivativeBox017Cell012
import TwoAxisHelicoid.MiddleDerivativeBox017Cell013
import TwoAxisHelicoid.MiddleDerivativeBox017Cell014
import TwoAxisHelicoid.MiddleDerivativeBox017Cell015
import TwoAxisHelicoid.MiddleDerivativeBox017Cell016
import TwoAxisHelicoid.MiddleDerivativeBox017Cell017
import TwoAxisHelicoid.MiddleDerivativeBox017Cell018
import TwoAxisHelicoid.MiddleDerivativeBox017Cell019
import TwoAxisHelicoid.MiddleDerivativeBox017Cell020
import TwoAxisHelicoid.MiddleDerivativeBox017Cell021
import TwoAxisHelicoid.MiddleDerivativeBox017Cell022
import TwoAxisHelicoid.MiddleDerivativeBox017Cell023
import TwoAxisHelicoid.MiddleDerivativeBox017Cell024
import TwoAxisHelicoid.MiddleDerivativeBox017Cell025
import TwoAxisHelicoid.MiddleDerivativeBox017Cell026
import TwoAxisHelicoid.MiddleDerivativeBox017Cell027
import TwoAxisHelicoid.MiddleDerivativeBox017Cell028
import TwoAxisHelicoid.MiddleDerivativeBox017Cell029
import TwoAxisHelicoid.MiddleDerivativeBox017Cell030
import TwoAxisHelicoid.MiddleDerivativeBox017Cell031
import TwoAxisHelicoid.MiddleDerivativeBox017Cell032
import TwoAxisHelicoid.MiddleDerivativeBox017Cell033
import TwoAxisHelicoid.MiddleDerivativeBox017Cell034
import TwoAxisHelicoid.MiddleDerivativeBox017Cell035
import TwoAxisHelicoid.MiddleDerivativeBox017Cell036
import TwoAxisHelicoid.MiddleDerivativeBox017Cell037
import TwoAxisHelicoid.MiddleDerivativeBox017Cell038
import TwoAxisHelicoid.MiddleDerivativeBox017Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox017Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox017Cell000,middleDerivativeBox017Cell001,middleDerivativeBox017Cell002,middleDerivativeBox017Cell003,middleDerivativeBox017Cell004,middleDerivativeBox017Cell005,middleDerivativeBox017Cell006,middleDerivativeBox017Cell007,middleDerivativeBox017Cell008,middleDerivativeBox017Cell009,middleDerivativeBox017Cell010,middleDerivativeBox017Cell011,middleDerivativeBox017Cell012,middleDerivativeBox017Cell013,middleDerivativeBox017Cell014,middleDerivativeBox017Cell015,middleDerivativeBox017Cell016,middleDerivativeBox017Cell017,middleDerivativeBox017Cell018,middleDerivativeBox017Cell019,middleDerivativeBox017Cell020,middleDerivativeBox017Cell021,middleDerivativeBox017Cell022,middleDerivativeBox017Cell023,middleDerivativeBox017Cell024,middleDerivativeBox017Cell025,middleDerivativeBox017Cell026,middleDerivativeBox017Cell027,middleDerivativeBox017Cell028,middleDerivativeBox017Cell029,middleDerivativeBox017Cell030,middleDerivativeBox017Cell031,middleDerivativeBox017Cell032,middleDerivativeBox017Cell033,middleDerivativeBox017Cell034,middleDerivativeBox017Cell035,middleDerivativeBox017Cell036,middleDerivativeBox017Cell037,middleDerivativeBox017Cell038,middleDerivativeBox017Cell039]
theorem middleDerivativeBox017Cells_valid : ∀ i : Fin 40, (middleDerivativeBox017Cells i).Valid middleRangeSetup middleDerivativeParameters017 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox017Cell000_valid
  · exact middleDerivativeBox017Cell001_valid
  · exact middleDerivativeBox017Cell002_valid
  · exact middleDerivativeBox017Cell003_valid
  · exact middleDerivativeBox017Cell004_valid
  · exact middleDerivativeBox017Cell005_valid
  · exact middleDerivativeBox017Cell006_valid
  · exact middleDerivativeBox017Cell007_valid
  · exact middleDerivativeBox017Cell008_valid
  · exact middleDerivativeBox017Cell009_valid
  · exact middleDerivativeBox017Cell010_valid
  · exact middleDerivativeBox017Cell011_valid
  · exact middleDerivativeBox017Cell012_valid
  · exact middleDerivativeBox017Cell013_valid
  · exact middleDerivativeBox017Cell014_valid
  · exact middleDerivativeBox017Cell015_valid
  · exact middleDerivativeBox017Cell016_valid
  · exact middleDerivativeBox017Cell017_valid
  · exact middleDerivativeBox017Cell018_valid
  · exact middleDerivativeBox017Cell019_valid
  · exact middleDerivativeBox017Cell020_valid
  · exact middleDerivativeBox017Cell021_valid
  · exact middleDerivativeBox017Cell022_valid
  · exact middleDerivativeBox017Cell023_valid
  · exact middleDerivativeBox017Cell024_valid
  · exact middleDerivativeBox017Cell025_valid
  · exact middleDerivativeBox017Cell026_valid
  · exact middleDerivativeBox017Cell027_valid
  · exact middleDerivativeBox017Cell028_valid
  · exact middleDerivativeBox017Cell029_valid
  · exact middleDerivativeBox017Cell030_valid
  · exact middleDerivativeBox017Cell031_valid
  · exact middleDerivativeBox017Cell032_valid
  · exact middleDerivativeBox017Cell033_valid
  · exact middleDerivativeBox017Cell034_valid
  · exact middleDerivativeBox017Cell035_valid
  · exact middleDerivativeBox017Cell036_valid
  · exact middleDerivativeBox017Cell037_valid
  · exact middleDerivativeBox017Cell038_valid
  · exact middleDerivativeBox017Cell039_valid
theorem middleDerivativeBox017_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox017Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox017Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox017_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox017Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox017Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox017_partial_bounds {t a : ℝ} (htl : ((867/1000) : ℝ) ≤ t) (htu : t ≤ ((217/250) : ℝ))
    (hal : ((326339949271293/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((326876820183293/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters017 middleDerivativeParameters017_valid middleDerivativeBox017Cells (1/20) middleDerivativeBox017Cells_valid middleDerivativeBox017_upperA middleDerivativeBox017_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox017_derivative {t : ℝ} (htl : ((867/1000) : ℝ) ≤ t) (htu : t ≤ ((217/250) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox017_enclosure htl htu
  have hp := middleDerivativeParameters017.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters017_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox017_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((217/250) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox017_derivative
