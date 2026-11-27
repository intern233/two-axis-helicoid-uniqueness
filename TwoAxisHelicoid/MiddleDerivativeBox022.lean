import TwoAxisHelicoid.MiddleVerticalBox022
import TwoAxisHelicoid.MiddleDerivativeBox022Cell000
import TwoAxisHelicoid.MiddleDerivativeBox022Cell001
import TwoAxisHelicoid.MiddleDerivativeBox022Cell002
import TwoAxisHelicoid.MiddleDerivativeBox022Cell003
import TwoAxisHelicoid.MiddleDerivativeBox022Cell004
import TwoAxisHelicoid.MiddleDerivativeBox022Cell005
import TwoAxisHelicoid.MiddleDerivativeBox022Cell006
import TwoAxisHelicoid.MiddleDerivativeBox022Cell007
import TwoAxisHelicoid.MiddleDerivativeBox022Cell008
import TwoAxisHelicoid.MiddleDerivativeBox022Cell009
import TwoAxisHelicoid.MiddleDerivativeBox022Cell010
import TwoAxisHelicoid.MiddleDerivativeBox022Cell011
import TwoAxisHelicoid.MiddleDerivativeBox022Cell012
import TwoAxisHelicoid.MiddleDerivativeBox022Cell013
import TwoAxisHelicoid.MiddleDerivativeBox022Cell014
import TwoAxisHelicoid.MiddleDerivativeBox022Cell015
import TwoAxisHelicoid.MiddleDerivativeBox022Cell016
import TwoAxisHelicoid.MiddleDerivativeBox022Cell017
import TwoAxisHelicoid.MiddleDerivativeBox022Cell018
import TwoAxisHelicoid.MiddleDerivativeBox022Cell019
import TwoAxisHelicoid.MiddleDerivativeBox022Cell020
import TwoAxisHelicoid.MiddleDerivativeBox022Cell021
import TwoAxisHelicoid.MiddleDerivativeBox022Cell022
import TwoAxisHelicoid.MiddleDerivativeBox022Cell023
import TwoAxisHelicoid.MiddleDerivativeBox022Cell024
import TwoAxisHelicoid.MiddleDerivativeBox022Cell025
import TwoAxisHelicoid.MiddleDerivativeBox022Cell026
import TwoAxisHelicoid.MiddleDerivativeBox022Cell027
import TwoAxisHelicoid.MiddleDerivativeBox022Cell028
import TwoAxisHelicoid.MiddleDerivativeBox022Cell029
import TwoAxisHelicoid.MiddleDerivativeBox022Cell030
import TwoAxisHelicoid.MiddleDerivativeBox022Cell031
import TwoAxisHelicoid.MiddleDerivativeBox022Cell032
import TwoAxisHelicoid.MiddleDerivativeBox022Cell033
import TwoAxisHelicoid.MiddleDerivativeBox022Cell034
import TwoAxisHelicoid.MiddleDerivativeBox022Cell035
import TwoAxisHelicoid.MiddleDerivativeBox022Cell036
import TwoAxisHelicoid.MiddleDerivativeBox022Cell037
import TwoAxisHelicoid.MiddleDerivativeBox022Cell038
import TwoAxisHelicoid.MiddleDerivativeBox022Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox022Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox022Cell000,middleDerivativeBox022Cell001,middleDerivativeBox022Cell002,middleDerivativeBox022Cell003,middleDerivativeBox022Cell004,middleDerivativeBox022Cell005,middleDerivativeBox022Cell006,middleDerivativeBox022Cell007,middleDerivativeBox022Cell008,middleDerivativeBox022Cell009,middleDerivativeBox022Cell010,middleDerivativeBox022Cell011,middleDerivativeBox022Cell012,middleDerivativeBox022Cell013,middleDerivativeBox022Cell014,middleDerivativeBox022Cell015,middleDerivativeBox022Cell016,middleDerivativeBox022Cell017,middleDerivativeBox022Cell018,middleDerivativeBox022Cell019,middleDerivativeBox022Cell020,middleDerivativeBox022Cell021,middleDerivativeBox022Cell022,middleDerivativeBox022Cell023,middleDerivativeBox022Cell024,middleDerivativeBox022Cell025,middleDerivativeBox022Cell026,middleDerivativeBox022Cell027,middleDerivativeBox022Cell028,middleDerivativeBox022Cell029,middleDerivativeBox022Cell030,middleDerivativeBox022Cell031,middleDerivativeBox022Cell032,middleDerivativeBox022Cell033,middleDerivativeBox022Cell034,middleDerivativeBox022Cell035,middleDerivativeBox022Cell036,middleDerivativeBox022Cell037,middleDerivativeBox022Cell038,middleDerivativeBox022Cell039]
theorem middleDerivativeBox022Cells_valid : ∀ i : Fin 40, (middleDerivativeBox022Cells i).Valid middleRangeSetup middleDerivativeParameters022 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox022Cell000_valid
  · exact middleDerivativeBox022Cell001_valid
  · exact middleDerivativeBox022Cell002_valid
  · exact middleDerivativeBox022Cell003_valid
  · exact middleDerivativeBox022Cell004_valid
  · exact middleDerivativeBox022Cell005_valid
  · exact middleDerivativeBox022Cell006_valid
  · exact middleDerivativeBox022Cell007_valid
  · exact middleDerivativeBox022Cell008_valid
  · exact middleDerivativeBox022Cell009_valid
  · exact middleDerivativeBox022Cell010_valid
  · exact middleDerivativeBox022Cell011_valid
  · exact middleDerivativeBox022Cell012_valid
  · exact middleDerivativeBox022Cell013_valid
  · exact middleDerivativeBox022Cell014_valid
  · exact middleDerivativeBox022Cell015_valid
  · exact middleDerivativeBox022Cell016_valid
  · exact middleDerivativeBox022Cell017_valid
  · exact middleDerivativeBox022Cell018_valid
  · exact middleDerivativeBox022Cell019_valid
  · exact middleDerivativeBox022Cell020_valid
  · exact middleDerivativeBox022Cell021_valid
  · exact middleDerivativeBox022Cell022_valid
  · exact middleDerivativeBox022Cell023_valid
  · exact middleDerivativeBox022Cell024_valid
  · exact middleDerivativeBox022Cell025_valid
  · exact middleDerivativeBox022Cell026_valid
  · exact middleDerivativeBox022Cell027_valid
  · exact middleDerivativeBox022Cell028_valid
  · exact middleDerivativeBox022Cell029_valid
  · exact middleDerivativeBox022Cell030_valid
  · exact middleDerivativeBox022Cell031_valid
  · exact middleDerivativeBox022Cell032_valid
  · exact middleDerivativeBox022Cell033_valid
  · exact middleDerivativeBox022Cell034_valid
  · exact middleDerivativeBox022Cell035_valid
  · exact middleDerivativeBox022Cell036_valid
  · exact middleDerivativeBox022Cell037_valid
  · exact middleDerivativeBox022Cell038_valid
  · exact middleDerivativeBox022Cell039_valid
theorem middleDerivativeBox022_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox022Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox022Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox022_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox022Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox022Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox022_partial_bounds {t a : ℝ} (htl : ((109/125) : ℝ) ≤ t) (htu : t ≤ ((873/1000) : ℝ))
    (hal : ((981699695747263/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((983310308483263/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters022 middleDerivativeParameters022_valid middleDerivativeBox022Cells (1/20) middleDerivativeBox022Cells_valid middleDerivativeBox022_upperA middleDerivativeBox022_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox022_derivative {t : ℝ} (htl : ((109/125) : ℝ) ≤ t) (htu : t ≤ ((873/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox022_enclosure htl htu
  have hp := middleDerivativeParameters022.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters022_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox022_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((873/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox022_derivative
