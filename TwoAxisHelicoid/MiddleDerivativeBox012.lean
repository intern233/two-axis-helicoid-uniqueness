import TwoAxisHelicoid.MiddleVerticalBox012
import TwoAxisHelicoid.MiddleDerivativeBox012Cell000
import TwoAxisHelicoid.MiddleDerivativeBox012Cell001
import TwoAxisHelicoid.MiddleDerivativeBox012Cell002
import TwoAxisHelicoid.MiddleDerivativeBox012Cell003
import TwoAxisHelicoid.MiddleDerivativeBox012Cell004
import TwoAxisHelicoid.MiddleDerivativeBox012Cell005
import TwoAxisHelicoid.MiddleDerivativeBox012Cell006
import TwoAxisHelicoid.MiddleDerivativeBox012Cell007
import TwoAxisHelicoid.MiddleDerivativeBox012Cell008
import TwoAxisHelicoid.MiddleDerivativeBox012Cell009
import TwoAxisHelicoid.MiddleDerivativeBox012Cell010
import TwoAxisHelicoid.MiddleDerivativeBox012Cell011
import TwoAxisHelicoid.MiddleDerivativeBox012Cell012
import TwoAxisHelicoid.MiddleDerivativeBox012Cell013
import TwoAxisHelicoid.MiddleDerivativeBox012Cell014
import TwoAxisHelicoid.MiddleDerivativeBox012Cell015
import TwoAxisHelicoid.MiddleDerivativeBox012Cell016
import TwoAxisHelicoid.MiddleDerivativeBox012Cell017
import TwoAxisHelicoid.MiddleDerivativeBox012Cell018
import TwoAxisHelicoid.MiddleDerivativeBox012Cell019
import TwoAxisHelicoid.MiddleDerivativeBox012Cell020
import TwoAxisHelicoid.MiddleDerivativeBox012Cell021
import TwoAxisHelicoid.MiddleDerivativeBox012Cell022
import TwoAxisHelicoid.MiddleDerivativeBox012Cell023
import TwoAxisHelicoid.MiddleDerivativeBox012Cell024
import TwoAxisHelicoid.MiddleDerivativeBox012Cell025
import TwoAxisHelicoid.MiddleDerivativeBox012Cell026
import TwoAxisHelicoid.MiddleDerivativeBox012Cell027
import TwoAxisHelicoid.MiddleDerivativeBox012Cell028
import TwoAxisHelicoid.MiddleDerivativeBox012Cell029
import TwoAxisHelicoid.MiddleDerivativeBox012Cell030
import TwoAxisHelicoid.MiddleDerivativeBox012Cell031
import TwoAxisHelicoid.MiddleDerivativeBox012Cell032
import TwoAxisHelicoid.MiddleDerivativeBox012Cell033
import TwoAxisHelicoid.MiddleDerivativeBox012Cell034
import TwoAxisHelicoid.MiddleDerivativeBox012Cell035
import TwoAxisHelicoid.MiddleDerivativeBox012Cell036
import TwoAxisHelicoid.MiddleDerivativeBox012Cell037
import TwoAxisHelicoid.MiddleDerivativeBox012Cell038
import TwoAxisHelicoid.MiddleDerivativeBox012Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox012Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox012Cell000,middleDerivativeBox012Cell001,middleDerivativeBox012Cell002,middleDerivativeBox012Cell003,middleDerivativeBox012Cell004,middleDerivativeBox012Cell005,middleDerivativeBox012Cell006,middleDerivativeBox012Cell007,middleDerivativeBox012Cell008,middleDerivativeBox012Cell009,middleDerivativeBox012Cell010,middleDerivativeBox012Cell011,middleDerivativeBox012Cell012,middleDerivativeBox012Cell013,middleDerivativeBox012Cell014,middleDerivativeBox012Cell015,middleDerivativeBox012Cell016,middleDerivativeBox012Cell017,middleDerivativeBox012Cell018,middleDerivativeBox012Cell019,middleDerivativeBox012Cell020,middleDerivativeBox012Cell021,middleDerivativeBox012Cell022,middleDerivativeBox012Cell023,middleDerivativeBox012Cell024,middleDerivativeBox012Cell025,middleDerivativeBox012Cell026,middleDerivativeBox012Cell027,middleDerivativeBox012Cell028,middleDerivativeBox012Cell029,middleDerivativeBox012Cell030,middleDerivativeBox012Cell031,middleDerivativeBox012Cell032,middleDerivativeBox012Cell033,middleDerivativeBox012Cell034,middleDerivativeBox012Cell035,middleDerivativeBox012Cell036,middleDerivativeBox012Cell037,middleDerivativeBox012Cell038,middleDerivativeBox012Cell039]
theorem middleDerivativeBox012Cells_valid : ∀ i : Fin 40, (middleDerivativeBox012Cells i).Valid middleRangeSetup middleDerivativeParameters012 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox012Cell000_valid
  · exact middleDerivativeBox012Cell001_valid
  · exact middleDerivativeBox012Cell002_valid
  · exact middleDerivativeBox012Cell003_valid
  · exact middleDerivativeBox012Cell004_valid
  · exact middleDerivativeBox012Cell005_valid
  · exact middleDerivativeBox012Cell006_valid
  · exact middleDerivativeBox012Cell007_valid
  · exact middleDerivativeBox012Cell008_valid
  · exact middleDerivativeBox012Cell009_valid
  · exact middleDerivativeBox012Cell010_valid
  · exact middleDerivativeBox012Cell011_valid
  · exact middleDerivativeBox012Cell012_valid
  · exact middleDerivativeBox012Cell013_valid
  · exact middleDerivativeBox012Cell014_valid
  · exact middleDerivativeBox012Cell015_valid
  · exact middleDerivativeBox012Cell016_valid
  · exact middleDerivativeBox012Cell017_valid
  · exact middleDerivativeBox012Cell018_valid
  · exact middleDerivativeBox012Cell019_valid
  · exact middleDerivativeBox012Cell020_valid
  · exact middleDerivativeBox012Cell021_valid
  · exact middleDerivativeBox012Cell022_valid
  · exact middleDerivativeBox012Cell023_valid
  · exact middleDerivativeBox012Cell024_valid
  · exact middleDerivativeBox012Cell025_valid
  · exact middleDerivativeBox012Cell026_valid
  · exact middleDerivativeBox012Cell027_valid
  · exact middleDerivativeBox012Cell028_valid
  · exact middleDerivativeBox012Cell029_valid
  · exact middleDerivativeBox012Cell030_valid
  · exact middleDerivativeBox012Cell031_valid
  · exact middleDerivativeBox012Cell032_valid
  · exact middleDerivativeBox012Cell033_valid
  · exact middleDerivativeBox012Cell034_valid
  · exact middleDerivativeBox012Cell035_valid
  · exact middleDerivativeBox012Cell036_valid
  · exact middleDerivativeBox012Cell037_valid
  · exact middleDerivativeBox012Cell038_valid
  · exact middleDerivativeBox012Cell039_valid
theorem middleDerivativeBox012_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox012Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox012Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox012_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox012Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox012Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox012_partial_bounds {t a : ℝ} (htl : ((431/500) : ℝ) ≤ t) (htu : t ≤ ((863/1000) : ℝ))
    (hal : ((195272897858239/329853488332800) : ℝ) ≤ a) (hau : a ≤ ((195595020405439/329853488332800) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters012 middleDerivativeParameters012_valid middleDerivativeBox012Cells (1/20) middleDerivativeBox012Cells_valid middleDerivativeBox012_upperA middleDerivativeBox012_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox012_derivative {t : ℝ} (htl : ((431/500) : ℝ) ≤ t) (htu : t ≤ ((863/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox012_enclosure htl htu
  have hp := middleDerivativeParameters012.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters012_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox012_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((863/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox012_derivative
