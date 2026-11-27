import TwoAxisHelicoid.MiddleVerticalBox030
import TwoAxisHelicoid.MiddleDerivativeBox030Cell000
import TwoAxisHelicoid.MiddleDerivativeBox030Cell001
import TwoAxisHelicoid.MiddleDerivativeBox030Cell002
import TwoAxisHelicoid.MiddleDerivativeBox030Cell003
import TwoAxisHelicoid.MiddleDerivativeBox030Cell004
import TwoAxisHelicoid.MiddleDerivativeBox030Cell005
import TwoAxisHelicoid.MiddleDerivativeBox030Cell006
import TwoAxisHelicoid.MiddleDerivativeBox030Cell007
import TwoAxisHelicoid.MiddleDerivativeBox030Cell008
import TwoAxisHelicoid.MiddleDerivativeBox030Cell009
import TwoAxisHelicoid.MiddleDerivativeBox030Cell010
import TwoAxisHelicoid.MiddleDerivativeBox030Cell011
import TwoAxisHelicoid.MiddleDerivativeBox030Cell012
import TwoAxisHelicoid.MiddleDerivativeBox030Cell013
import TwoAxisHelicoid.MiddleDerivativeBox030Cell014
import TwoAxisHelicoid.MiddleDerivativeBox030Cell015
import TwoAxisHelicoid.MiddleDerivativeBox030Cell016
import TwoAxisHelicoid.MiddleDerivativeBox030Cell017
import TwoAxisHelicoid.MiddleDerivativeBox030Cell018
import TwoAxisHelicoid.MiddleDerivativeBox030Cell019
import TwoAxisHelicoid.MiddleDerivativeBox030Cell020
import TwoAxisHelicoid.MiddleDerivativeBox030Cell021
import TwoAxisHelicoid.MiddleDerivativeBox030Cell022
import TwoAxisHelicoid.MiddleDerivativeBox030Cell023
import TwoAxisHelicoid.MiddleDerivativeBox030Cell024
import TwoAxisHelicoid.MiddleDerivativeBox030Cell025
import TwoAxisHelicoid.MiddleDerivativeBox030Cell026
import TwoAxisHelicoid.MiddleDerivativeBox030Cell027
import TwoAxisHelicoid.MiddleDerivativeBox030Cell028
import TwoAxisHelicoid.MiddleDerivativeBox030Cell029
import TwoAxisHelicoid.MiddleDerivativeBox030Cell030
import TwoAxisHelicoid.MiddleDerivativeBox030Cell031
import TwoAxisHelicoid.MiddleDerivativeBox030Cell032
import TwoAxisHelicoid.MiddleDerivativeBox030Cell033
import TwoAxisHelicoid.MiddleDerivativeBox030Cell034
import TwoAxisHelicoid.MiddleDerivativeBox030Cell035
import TwoAxisHelicoid.MiddleDerivativeBox030Cell036
import TwoAxisHelicoid.MiddleDerivativeBox030Cell037
import TwoAxisHelicoid.MiddleDerivativeBox030Cell038
import TwoAxisHelicoid.MiddleDerivativeBox030Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox030Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox030Cell000,middleDerivativeBox030Cell001,middleDerivativeBox030Cell002,middleDerivativeBox030Cell003,middleDerivativeBox030Cell004,middleDerivativeBox030Cell005,middleDerivativeBox030Cell006,middleDerivativeBox030Cell007,middleDerivativeBox030Cell008,middleDerivativeBox030Cell009,middleDerivativeBox030Cell010,middleDerivativeBox030Cell011,middleDerivativeBox030Cell012,middleDerivativeBox030Cell013,middleDerivativeBox030Cell014,middleDerivativeBox030Cell015,middleDerivativeBox030Cell016,middleDerivativeBox030Cell017,middleDerivativeBox030Cell018,middleDerivativeBox030Cell019,middleDerivativeBox030Cell020,middleDerivativeBox030Cell021,middleDerivativeBox030Cell022,middleDerivativeBox030Cell023,middleDerivativeBox030Cell024,middleDerivativeBox030Cell025,middleDerivativeBox030Cell026,middleDerivativeBox030Cell027,middleDerivativeBox030Cell028,middleDerivativeBox030Cell029,middleDerivativeBox030Cell030,middleDerivativeBox030Cell031,middleDerivativeBox030Cell032,middleDerivativeBox030Cell033,middleDerivativeBox030Cell034,middleDerivativeBox030Cell035,middleDerivativeBox030Cell036,middleDerivativeBox030Cell037,middleDerivativeBox030Cell038,middleDerivativeBox030Cell039]
theorem middleDerivativeBox030Cells_valid : ∀ i : Fin 40, (middleDerivativeBox030Cells i).Valid middleRangeSetup middleDerivativeParameters030 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox030Cell000_valid
  · exact middleDerivativeBox030Cell001_valid
  · exact middleDerivativeBox030Cell002_valid
  · exact middleDerivativeBox030Cell003_valid
  · exact middleDerivativeBox030Cell004_valid
  · exact middleDerivativeBox030Cell005_valid
  · exact middleDerivativeBox030Cell006_valid
  · exact middleDerivativeBox030Cell007_valid
  · exact middleDerivativeBox030Cell008_valid
  · exact middleDerivativeBox030Cell009_valid
  · exact middleDerivativeBox030Cell010_valid
  · exact middleDerivativeBox030Cell011_valid
  · exact middleDerivativeBox030Cell012_valid
  · exact middleDerivativeBox030Cell013_valid
  · exact middleDerivativeBox030Cell014_valid
  · exact middleDerivativeBox030Cell015_valid
  · exact middleDerivativeBox030Cell016_valid
  · exact middleDerivativeBox030Cell017_valid
  · exact middleDerivativeBox030Cell018_valid
  · exact middleDerivativeBox030Cell019_valid
  · exact middleDerivativeBox030Cell020_valid
  · exact middleDerivativeBox030Cell021_valid
  · exact middleDerivativeBox030Cell022_valid
  · exact middleDerivativeBox030Cell023_valid
  · exact middleDerivativeBox030Cell024_valid
  · exact middleDerivativeBox030Cell025_valid
  · exact middleDerivativeBox030Cell026_valid
  · exact middleDerivativeBox030Cell027_valid
  · exact middleDerivativeBox030Cell028_valid
  · exact middleDerivativeBox030Cell029_valid
  · exact middleDerivativeBox030Cell030_valid
  · exact middleDerivativeBox030Cell031_valid
  · exact middleDerivativeBox030Cell032_valid
  · exact middleDerivativeBox030Cell033_valid
  · exact middleDerivativeBox030Cell034_valid
  · exact middleDerivativeBox030Cell035_valid
  · exact middleDerivativeBox030Cell036_valid
  · exact middleDerivativeBox030Cell037_valid
  · exact middleDerivativeBox030Cell038_valid
  · exact middleDerivativeBox030Cell039_valid
theorem middleDerivativeBox030_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox030Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox030Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox030_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox030Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox030Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox030_partial_bounds {t a : ℝ} (htl : ((22/25) : ℝ) ≤ t) (htu : t ≤ ((881/1000) : ℝ))
    (hal : ((328679546822963/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((329216417734963/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters030 middleDerivativeParameters030_valid middleDerivativeBox030Cells (1/20) middleDerivativeBox030Cells_valid middleDerivativeBox030_upperA middleDerivativeBox030_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox030_derivative {t : ℝ} (htl : ((22/25) : ℝ) ≤ t) (htu : t ≤ ((881/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox030_enclosure htl htu
  have hp := middleDerivativeParameters030.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters030_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox030_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((881/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox030_derivative
