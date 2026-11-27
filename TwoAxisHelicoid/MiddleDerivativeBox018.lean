import TwoAxisHelicoid.MiddleVerticalBox018
import TwoAxisHelicoid.MiddleDerivativeBox018Cell000
import TwoAxisHelicoid.MiddleDerivativeBox018Cell001
import TwoAxisHelicoid.MiddleDerivativeBox018Cell002
import TwoAxisHelicoid.MiddleDerivativeBox018Cell003
import TwoAxisHelicoid.MiddleDerivativeBox018Cell004
import TwoAxisHelicoid.MiddleDerivativeBox018Cell005
import TwoAxisHelicoid.MiddleDerivativeBox018Cell006
import TwoAxisHelicoid.MiddleDerivativeBox018Cell007
import TwoAxisHelicoid.MiddleDerivativeBox018Cell008
import TwoAxisHelicoid.MiddleDerivativeBox018Cell009
import TwoAxisHelicoid.MiddleDerivativeBox018Cell010
import TwoAxisHelicoid.MiddleDerivativeBox018Cell011
import TwoAxisHelicoid.MiddleDerivativeBox018Cell012
import TwoAxisHelicoid.MiddleDerivativeBox018Cell013
import TwoAxisHelicoid.MiddleDerivativeBox018Cell014
import TwoAxisHelicoid.MiddleDerivativeBox018Cell015
import TwoAxisHelicoid.MiddleDerivativeBox018Cell016
import TwoAxisHelicoid.MiddleDerivativeBox018Cell017
import TwoAxisHelicoid.MiddleDerivativeBox018Cell018
import TwoAxisHelicoid.MiddleDerivativeBox018Cell019
import TwoAxisHelicoid.MiddleDerivativeBox018Cell020
import TwoAxisHelicoid.MiddleDerivativeBox018Cell021
import TwoAxisHelicoid.MiddleDerivativeBox018Cell022
import TwoAxisHelicoid.MiddleDerivativeBox018Cell023
import TwoAxisHelicoid.MiddleDerivativeBox018Cell024
import TwoAxisHelicoid.MiddleDerivativeBox018Cell025
import TwoAxisHelicoid.MiddleDerivativeBox018Cell026
import TwoAxisHelicoid.MiddleDerivativeBox018Cell027
import TwoAxisHelicoid.MiddleDerivativeBox018Cell028
import TwoAxisHelicoid.MiddleDerivativeBox018Cell029
import TwoAxisHelicoid.MiddleDerivativeBox018Cell030
import TwoAxisHelicoid.MiddleDerivativeBox018Cell031
import TwoAxisHelicoid.MiddleDerivativeBox018Cell032
import TwoAxisHelicoid.MiddleDerivativeBox018Cell033
import TwoAxisHelicoid.MiddleDerivativeBox018Cell034
import TwoAxisHelicoid.MiddleDerivativeBox018Cell035
import TwoAxisHelicoid.MiddleDerivativeBox018Cell036
import TwoAxisHelicoid.MiddleDerivativeBox018Cell037
import TwoAxisHelicoid.MiddleDerivativeBox018Cell038
import TwoAxisHelicoid.MiddleDerivativeBox018Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox018Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox018Cell000,middleDerivativeBox018Cell001,middleDerivativeBox018Cell002,middleDerivativeBox018Cell003,middleDerivativeBox018Cell004,middleDerivativeBox018Cell005,middleDerivativeBox018Cell006,middleDerivativeBox018Cell007,middleDerivativeBox018Cell008,middleDerivativeBox018Cell009,middleDerivativeBox018Cell010,middleDerivativeBox018Cell011,middleDerivativeBox018Cell012,middleDerivativeBox018Cell013,middleDerivativeBox018Cell014,middleDerivativeBox018Cell015,middleDerivativeBox018Cell016,middleDerivativeBox018Cell017,middleDerivativeBox018Cell018,middleDerivativeBox018Cell019,middleDerivativeBox018Cell020,middleDerivativeBox018Cell021,middleDerivativeBox018Cell022,middleDerivativeBox018Cell023,middleDerivativeBox018Cell024,middleDerivativeBox018Cell025,middleDerivativeBox018Cell026,middleDerivativeBox018Cell027,middleDerivativeBox018Cell028,middleDerivativeBox018Cell029,middleDerivativeBox018Cell030,middleDerivativeBox018Cell031,middleDerivativeBox018Cell032,middleDerivativeBox018Cell033,middleDerivativeBox018Cell034,middleDerivativeBox018Cell035,middleDerivativeBox018Cell036,middleDerivativeBox018Cell037,middleDerivativeBox018Cell038,middleDerivativeBox018Cell039]
theorem middleDerivativeBox018Cells_valid : ∀ i : Fin 40, (middleDerivativeBox018Cells i).Valid middleRangeSetup middleDerivativeParameters018 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox018Cell000_valid
  · exact middleDerivativeBox018Cell001_valid
  · exact middleDerivativeBox018Cell002_valid
  · exact middleDerivativeBox018Cell003_valid
  · exact middleDerivativeBox018Cell004_valid
  · exact middleDerivativeBox018Cell005_valid
  · exact middleDerivativeBox018Cell006_valid
  · exact middleDerivativeBox018Cell007_valid
  · exact middleDerivativeBox018Cell008_valid
  · exact middleDerivativeBox018Cell009_valid
  · exact middleDerivativeBox018Cell010_valid
  · exact middleDerivativeBox018Cell011_valid
  · exact middleDerivativeBox018Cell012_valid
  · exact middleDerivativeBox018Cell013_valid
  · exact middleDerivativeBox018Cell014_valid
  · exact middleDerivativeBox018Cell015_valid
  · exact middleDerivativeBox018Cell016_valid
  · exact middleDerivativeBox018Cell017_valid
  · exact middleDerivativeBox018Cell018_valid
  · exact middleDerivativeBox018Cell019_valid
  · exact middleDerivativeBox018Cell020_valid
  · exact middleDerivativeBox018Cell021_valid
  · exact middleDerivativeBox018Cell022_valid
  · exact middleDerivativeBox018Cell023_valid
  · exact middleDerivativeBox018Cell024_valid
  · exact middleDerivativeBox018Cell025_valid
  · exact middleDerivativeBox018Cell026_valid
  · exact middleDerivativeBox018Cell027_valid
  · exact middleDerivativeBox018Cell028_valid
  · exact middleDerivativeBox018Cell029_valid
  · exact middleDerivativeBox018Cell030_valid
  · exact middleDerivativeBox018Cell031_valid
  · exact middleDerivativeBox018Cell032_valid
  · exact middleDerivativeBox018Cell033_valid
  · exact middleDerivativeBox018Cell034_valid
  · exact middleDerivativeBox018Cell035_valid
  · exact middleDerivativeBox018Cell036_valid
  · exact middleDerivativeBox018Cell037_valid
  · exact middleDerivativeBox018Cell038_valid
  · exact middleDerivativeBox018Cell039_valid
theorem middleDerivativeBox018_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox018Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox018Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox018_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox018Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox018Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox018_partial_bounds {t a : ℝ} (htl : ((217/250) : ℝ) ≤ t) (htu : t ≤ ((869/1000) : ℝ))
    (hal : ((979553855139569/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((981164467875569/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters018 middleDerivativeParameters018_valid middleDerivativeBox018Cells (1/20) middleDerivativeBox018Cells_valid middleDerivativeBox018_upperA middleDerivativeBox018_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox018_derivative {t : ℝ} (htl : ((217/250) : ℝ) ≤ t) (htu : t ≤ ((869/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox018_enclosure htl htu
  have hp := middleDerivativeParameters018.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters018_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox018_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((869/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox018_derivative
