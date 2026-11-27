import TwoAxisHelicoid.MiddleVerticalBox029
import TwoAxisHelicoid.MiddleDerivativeBox029Cell000
import TwoAxisHelicoid.MiddleDerivativeBox029Cell001
import TwoAxisHelicoid.MiddleDerivativeBox029Cell002
import TwoAxisHelicoid.MiddleDerivativeBox029Cell003
import TwoAxisHelicoid.MiddleDerivativeBox029Cell004
import TwoAxisHelicoid.MiddleDerivativeBox029Cell005
import TwoAxisHelicoid.MiddleDerivativeBox029Cell006
import TwoAxisHelicoid.MiddleDerivativeBox029Cell007
import TwoAxisHelicoid.MiddleDerivativeBox029Cell008
import TwoAxisHelicoid.MiddleDerivativeBox029Cell009
import TwoAxisHelicoid.MiddleDerivativeBox029Cell010
import TwoAxisHelicoid.MiddleDerivativeBox029Cell011
import TwoAxisHelicoid.MiddleDerivativeBox029Cell012
import TwoAxisHelicoid.MiddleDerivativeBox029Cell013
import TwoAxisHelicoid.MiddleDerivativeBox029Cell014
import TwoAxisHelicoid.MiddleDerivativeBox029Cell015
import TwoAxisHelicoid.MiddleDerivativeBox029Cell016
import TwoAxisHelicoid.MiddleDerivativeBox029Cell017
import TwoAxisHelicoid.MiddleDerivativeBox029Cell018
import TwoAxisHelicoid.MiddleDerivativeBox029Cell019
import TwoAxisHelicoid.MiddleDerivativeBox029Cell020
import TwoAxisHelicoid.MiddleDerivativeBox029Cell021
import TwoAxisHelicoid.MiddleDerivativeBox029Cell022
import TwoAxisHelicoid.MiddleDerivativeBox029Cell023
import TwoAxisHelicoid.MiddleDerivativeBox029Cell024
import TwoAxisHelicoid.MiddleDerivativeBox029Cell025
import TwoAxisHelicoid.MiddleDerivativeBox029Cell026
import TwoAxisHelicoid.MiddleDerivativeBox029Cell027
import TwoAxisHelicoid.MiddleDerivativeBox029Cell028
import TwoAxisHelicoid.MiddleDerivativeBox029Cell029
import TwoAxisHelicoid.MiddleDerivativeBox029Cell030
import TwoAxisHelicoid.MiddleDerivativeBox029Cell031
import TwoAxisHelicoid.MiddleDerivativeBox029Cell032
import TwoAxisHelicoid.MiddleDerivativeBox029Cell033
import TwoAxisHelicoid.MiddleDerivativeBox029Cell034
import TwoAxisHelicoid.MiddleDerivativeBox029Cell035
import TwoAxisHelicoid.MiddleDerivativeBox029Cell036
import TwoAxisHelicoid.MiddleDerivativeBox029Cell037
import TwoAxisHelicoid.MiddleDerivativeBox029Cell038
import TwoAxisHelicoid.MiddleDerivativeBox029Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox029Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox029Cell000,middleDerivativeBox029Cell001,middleDerivativeBox029Cell002,middleDerivativeBox029Cell003,middleDerivativeBox029Cell004,middleDerivativeBox029Cell005,middleDerivativeBox029Cell006,middleDerivativeBox029Cell007,middleDerivativeBox029Cell008,middleDerivativeBox029Cell009,middleDerivativeBox029Cell010,middleDerivativeBox029Cell011,middleDerivativeBox029Cell012,middleDerivativeBox029Cell013,middleDerivativeBox029Cell014,middleDerivativeBox029Cell015,middleDerivativeBox029Cell016,middleDerivativeBox029Cell017,middleDerivativeBox029Cell018,middleDerivativeBox029Cell019,middleDerivativeBox029Cell020,middleDerivativeBox029Cell021,middleDerivativeBox029Cell022,middleDerivativeBox029Cell023,middleDerivativeBox029Cell024,middleDerivativeBox029Cell025,middleDerivativeBox029Cell026,middleDerivativeBox029Cell027,middleDerivativeBox029Cell028,middleDerivativeBox029Cell029,middleDerivativeBox029Cell030,middleDerivativeBox029Cell031,middleDerivativeBox029Cell032,middleDerivativeBox029Cell033,middleDerivativeBox029Cell034,middleDerivativeBox029Cell035,middleDerivativeBox029Cell036,middleDerivativeBox029Cell037,middleDerivativeBox029Cell038,middleDerivativeBox029Cell039]
theorem middleDerivativeBox029Cells_valid : ∀ i : Fin 40, (middleDerivativeBox029Cells i).Valid middleRangeSetup middleDerivativeParameters029 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox029Cell000_valid
  · exact middleDerivativeBox029Cell001_valid
  · exact middleDerivativeBox029Cell002_valid
  · exact middleDerivativeBox029Cell003_valid
  · exact middleDerivativeBox029Cell004_valid
  · exact middleDerivativeBox029Cell005_valid
  · exact middleDerivativeBox029Cell006_valid
  · exact middleDerivativeBox029Cell007_valid
  · exact middleDerivativeBox029Cell008_valid
  · exact middleDerivativeBox029Cell009_valid
  · exact middleDerivativeBox029Cell010_valid
  · exact middleDerivativeBox029Cell011_valid
  · exact middleDerivativeBox029Cell012_valid
  · exact middleDerivativeBox029Cell013_valid
  · exact middleDerivativeBox029Cell014_valid
  · exact middleDerivativeBox029Cell015_valid
  · exact middleDerivativeBox029Cell016_valid
  · exact middleDerivativeBox029Cell017_valid
  · exact middleDerivativeBox029Cell018_valid
  · exact middleDerivativeBox029Cell019_valid
  · exact middleDerivativeBox029Cell020_valid
  · exact middleDerivativeBox029Cell021_valid
  · exact middleDerivativeBox029Cell022_valid
  · exact middleDerivativeBox029Cell023_valid
  · exact middleDerivativeBox029Cell024_valid
  · exact middleDerivativeBox029Cell025_valid
  · exact middleDerivativeBox029Cell026_valid
  · exact middleDerivativeBox029Cell027_valid
  · exact middleDerivativeBox029Cell028_valid
  · exact middleDerivativeBox029Cell029_valid
  · exact middleDerivativeBox029Cell030_valid
  · exact middleDerivativeBox029Cell031_valid
  · exact middleDerivativeBox029Cell032_valid
  · exact middleDerivativeBox029Cell033_valid
  · exact middleDerivativeBox029Cell034_valid
  · exact middleDerivativeBox029Cell035_valid
  · exact middleDerivativeBox029Cell036_valid
  · exact middleDerivativeBox029Cell037_valid
  · exact middleDerivativeBox029Cell038_valid
  · exact middleDerivativeBox029Cell039_valid
theorem middleDerivativeBox029_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox029Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox029Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox029_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox029Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox029Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox029_partial_bounds {t a : ℝ} (htl : ((879/1000) : ℝ) ≤ t) (htu : t ≤ ((22/25) : ℝ))
    (hal : ((985492815320563/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((987103428056563/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters029 middleDerivativeParameters029_valid middleDerivativeBox029Cells (1/20) middleDerivativeBox029Cells_valid middleDerivativeBox029_upperA middleDerivativeBox029_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox029_derivative {t : ℝ} (htl : ((879/1000) : ℝ) ≤ t) (htu : t ≤ ((22/25) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox029_enclosure htl htu
  have hp := middleDerivativeParameters029.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters029_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox029_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((22/25) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox029_derivative
