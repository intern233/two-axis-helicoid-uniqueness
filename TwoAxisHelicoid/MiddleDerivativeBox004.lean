import TwoAxisHelicoid.MiddleVerticalBox004
import TwoAxisHelicoid.MiddleDerivativeBox004Cell000
import TwoAxisHelicoid.MiddleDerivativeBox004Cell001
import TwoAxisHelicoid.MiddleDerivativeBox004Cell002
import TwoAxisHelicoid.MiddleDerivativeBox004Cell003
import TwoAxisHelicoid.MiddleDerivativeBox004Cell004
import TwoAxisHelicoid.MiddleDerivativeBox004Cell005
import TwoAxisHelicoid.MiddleDerivativeBox004Cell006
import TwoAxisHelicoid.MiddleDerivativeBox004Cell007
import TwoAxisHelicoid.MiddleDerivativeBox004Cell008
import TwoAxisHelicoid.MiddleDerivativeBox004Cell009
import TwoAxisHelicoid.MiddleDerivativeBox004Cell010
import TwoAxisHelicoid.MiddleDerivativeBox004Cell011
import TwoAxisHelicoid.MiddleDerivativeBox004Cell012
import TwoAxisHelicoid.MiddleDerivativeBox004Cell013
import TwoAxisHelicoid.MiddleDerivativeBox004Cell014
import TwoAxisHelicoid.MiddleDerivativeBox004Cell015
import TwoAxisHelicoid.MiddleDerivativeBox004Cell016
import TwoAxisHelicoid.MiddleDerivativeBox004Cell017
import TwoAxisHelicoid.MiddleDerivativeBox004Cell018
import TwoAxisHelicoid.MiddleDerivativeBox004Cell019
import TwoAxisHelicoid.MiddleDerivativeBox004Cell020
import TwoAxisHelicoid.MiddleDerivativeBox004Cell021
import TwoAxisHelicoid.MiddleDerivativeBox004Cell022
import TwoAxisHelicoid.MiddleDerivativeBox004Cell023
import TwoAxisHelicoid.MiddleDerivativeBox004Cell024
import TwoAxisHelicoid.MiddleDerivativeBox004Cell025
import TwoAxisHelicoid.MiddleDerivativeBox004Cell026
import TwoAxisHelicoid.MiddleDerivativeBox004Cell027
import TwoAxisHelicoid.MiddleDerivativeBox004Cell028
import TwoAxisHelicoid.MiddleDerivativeBox004Cell029
import TwoAxisHelicoid.MiddleDerivativeBox004Cell030
import TwoAxisHelicoid.MiddleDerivativeBox004Cell031
import TwoAxisHelicoid.MiddleDerivativeBox004Cell032
import TwoAxisHelicoid.MiddleDerivativeBox004Cell033
import TwoAxisHelicoid.MiddleDerivativeBox004Cell034
import TwoAxisHelicoid.MiddleDerivativeBox004Cell035
import TwoAxisHelicoid.MiddleDerivativeBox004Cell036
import TwoAxisHelicoid.MiddleDerivativeBox004Cell037
import TwoAxisHelicoid.MiddleDerivativeBox004Cell038
import TwoAxisHelicoid.MiddleDerivativeBox004Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox004Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox004Cell000,middleDerivativeBox004Cell001,middleDerivativeBox004Cell002,middleDerivativeBox004Cell003,middleDerivativeBox004Cell004,middleDerivativeBox004Cell005,middleDerivativeBox004Cell006,middleDerivativeBox004Cell007,middleDerivativeBox004Cell008,middleDerivativeBox004Cell009,middleDerivativeBox004Cell010,middleDerivativeBox004Cell011,middleDerivativeBox004Cell012,middleDerivativeBox004Cell013,middleDerivativeBox004Cell014,middleDerivativeBox004Cell015,middleDerivativeBox004Cell016,middleDerivativeBox004Cell017,middleDerivativeBox004Cell018,middleDerivativeBox004Cell019,middleDerivativeBox004Cell020,middleDerivativeBox004Cell021,middleDerivativeBox004Cell022,middleDerivativeBox004Cell023,middleDerivativeBox004Cell024,middleDerivativeBox004Cell025,middleDerivativeBox004Cell026,middleDerivativeBox004Cell027,middleDerivativeBox004Cell028,middleDerivativeBox004Cell029,middleDerivativeBox004Cell030,middleDerivativeBox004Cell031,middleDerivativeBox004Cell032,middleDerivativeBox004Cell033,middleDerivativeBox004Cell034,middleDerivativeBox004Cell035,middleDerivativeBox004Cell036,middleDerivativeBox004Cell037,middleDerivativeBox004Cell038,middleDerivativeBox004Cell039]
theorem middleDerivativeBox004Cells_valid : ∀ i : Fin 40, (middleDerivativeBox004Cells i).Valid middleRangeSetup middleDerivativeParameters004 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox004Cell000_valid
  · exact middleDerivativeBox004Cell001_valid
  · exact middleDerivativeBox004Cell002_valid
  · exact middleDerivativeBox004Cell003_valid
  · exact middleDerivativeBox004Cell004_valid
  · exact middleDerivativeBox004Cell005_valid
  · exact middleDerivativeBox004Cell006_valid
  · exact middleDerivativeBox004Cell007_valid
  · exact middleDerivativeBox004Cell008_valid
  · exact middleDerivativeBox004Cell009_valid
  · exact middleDerivativeBox004Cell010_valid
  · exact middleDerivativeBox004Cell011_valid
  · exact middleDerivativeBox004Cell012_valid
  · exact middleDerivativeBox004Cell013_valid
  · exact middleDerivativeBox004Cell014_valid
  · exact middleDerivativeBox004Cell015_valid
  · exact middleDerivativeBox004Cell016_valid
  · exact middleDerivativeBox004Cell017_valid
  · exact middleDerivativeBox004Cell018_valid
  · exact middleDerivativeBox004Cell019_valid
  · exact middleDerivativeBox004Cell020_valid
  · exact middleDerivativeBox004Cell021_valid
  · exact middleDerivativeBox004Cell022_valid
  · exact middleDerivativeBox004Cell023_valid
  · exact middleDerivativeBox004Cell024_valid
  · exact middleDerivativeBox004Cell025_valid
  · exact middleDerivativeBox004Cell026_valid
  · exact middleDerivativeBox004Cell027_valid
  · exact middleDerivativeBox004Cell028_valid
  · exact middleDerivativeBox004Cell029_valid
  · exact middleDerivativeBox004Cell030_valid
  · exact middleDerivativeBox004Cell031_valid
  · exact middleDerivativeBox004Cell032_valid
  · exact middleDerivativeBox004Cell033_valid
  · exact middleDerivativeBox004Cell034_valid
  · exact middleDerivativeBox004Cell035_valid
  · exact middleDerivativeBox004Cell036_valid
  · exact middleDerivativeBox004Cell037_valid
  · exact middleDerivativeBox004Cell038_valid
  · exact middleDerivativeBox004Cell039_valid
theorem middleDerivativeBox004_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox004Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox004Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox004_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox004Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox004Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox004_partial_bounds {t a : ℝ} (htl : ((427/500) : ℝ) ≤ t) (htu : t ≤ ((171/200) : ℝ))
    (hal : ((972166619770871/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((973777232506871/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters004 middleDerivativeParameters004_valid middleDerivativeBox004Cells (1/20) middleDerivativeBox004Cells_valid middleDerivativeBox004_upperA middleDerivativeBox004_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox004_derivative {t : ℝ} (htl : ((427/500) : ℝ) ≤ t) (htu : t ≤ ((171/200) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox004_enclosure htl htu
  have hp := middleDerivativeParameters004.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters004_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox004_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((171/200) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox004_derivative
