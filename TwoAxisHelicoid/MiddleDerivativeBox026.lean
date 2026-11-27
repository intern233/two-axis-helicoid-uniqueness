import TwoAxisHelicoid.MiddleVerticalBox026
import TwoAxisHelicoid.MiddleDerivativeBox026Cell000
import TwoAxisHelicoid.MiddleDerivativeBox026Cell001
import TwoAxisHelicoid.MiddleDerivativeBox026Cell002
import TwoAxisHelicoid.MiddleDerivativeBox026Cell003
import TwoAxisHelicoid.MiddleDerivativeBox026Cell004
import TwoAxisHelicoid.MiddleDerivativeBox026Cell005
import TwoAxisHelicoid.MiddleDerivativeBox026Cell006
import TwoAxisHelicoid.MiddleDerivativeBox026Cell007
import TwoAxisHelicoid.MiddleDerivativeBox026Cell008
import TwoAxisHelicoid.MiddleDerivativeBox026Cell009
import TwoAxisHelicoid.MiddleDerivativeBox026Cell010
import TwoAxisHelicoid.MiddleDerivativeBox026Cell011
import TwoAxisHelicoid.MiddleDerivativeBox026Cell012
import TwoAxisHelicoid.MiddleDerivativeBox026Cell013
import TwoAxisHelicoid.MiddleDerivativeBox026Cell014
import TwoAxisHelicoid.MiddleDerivativeBox026Cell015
import TwoAxisHelicoid.MiddleDerivativeBox026Cell016
import TwoAxisHelicoid.MiddleDerivativeBox026Cell017
import TwoAxisHelicoid.MiddleDerivativeBox026Cell018
import TwoAxisHelicoid.MiddleDerivativeBox026Cell019
import TwoAxisHelicoid.MiddleDerivativeBox026Cell020
import TwoAxisHelicoid.MiddleDerivativeBox026Cell021
import TwoAxisHelicoid.MiddleDerivativeBox026Cell022
import TwoAxisHelicoid.MiddleDerivativeBox026Cell023
import TwoAxisHelicoid.MiddleDerivativeBox026Cell024
import TwoAxisHelicoid.MiddleDerivativeBox026Cell025
import TwoAxisHelicoid.MiddleDerivativeBox026Cell026
import TwoAxisHelicoid.MiddleDerivativeBox026Cell027
import TwoAxisHelicoid.MiddleDerivativeBox026Cell028
import TwoAxisHelicoid.MiddleDerivativeBox026Cell029
import TwoAxisHelicoid.MiddleDerivativeBox026Cell030
import TwoAxisHelicoid.MiddleDerivativeBox026Cell031
import TwoAxisHelicoid.MiddleDerivativeBox026Cell032
import TwoAxisHelicoid.MiddleDerivativeBox026Cell033
import TwoAxisHelicoid.MiddleDerivativeBox026Cell034
import TwoAxisHelicoid.MiddleDerivativeBox026Cell035
import TwoAxisHelicoid.MiddleDerivativeBox026Cell036
import TwoAxisHelicoid.MiddleDerivativeBox026Cell037
import TwoAxisHelicoid.MiddleDerivativeBox026Cell038
import TwoAxisHelicoid.MiddleDerivativeBox026Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox026Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox026Cell000,middleDerivativeBox026Cell001,middleDerivativeBox026Cell002,middleDerivativeBox026Cell003,middleDerivativeBox026Cell004,middleDerivativeBox026Cell005,middleDerivativeBox026Cell006,middleDerivativeBox026Cell007,middleDerivativeBox026Cell008,middleDerivativeBox026Cell009,middleDerivativeBox026Cell010,middleDerivativeBox026Cell011,middleDerivativeBox026Cell012,middleDerivativeBox026Cell013,middleDerivativeBox026Cell014,middleDerivativeBox026Cell015,middleDerivativeBox026Cell016,middleDerivativeBox026Cell017,middleDerivativeBox026Cell018,middleDerivativeBox026Cell019,middleDerivativeBox026Cell020,middleDerivativeBox026Cell021,middleDerivativeBox026Cell022,middleDerivativeBox026Cell023,middleDerivativeBox026Cell024,middleDerivativeBox026Cell025,middleDerivativeBox026Cell026,middleDerivativeBox026Cell027,middleDerivativeBox026Cell028,middleDerivativeBox026Cell029,middleDerivativeBox026Cell030,middleDerivativeBox026Cell031,middleDerivativeBox026Cell032,middleDerivativeBox026Cell033,middleDerivativeBox026Cell034,middleDerivativeBox026Cell035,middleDerivativeBox026Cell036,middleDerivativeBox026Cell037,middleDerivativeBox026Cell038,middleDerivativeBox026Cell039]
theorem middleDerivativeBox026Cells_valid : ∀ i : Fin 40, (middleDerivativeBox026Cells i).Valid middleRangeSetup middleDerivativeParameters026 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox026Cell000_valid
  · exact middleDerivativeBox026Cell001_valid
  · exact middleDerivativeBox026Cell002_valid
  · exact middleDerivativeBox026Cell003_valid
  · exact middleDerivativeBox026Cell004_valid
  · exact middleDerivativeBox026Cell005_valid
  · exact middleDerivativeBox026Cell006_valid
  · exact middleDerivativeBox026Cell007_valid
  · exact middleDerivativeBox026Cell008_valid
  · exact middleDerivativeBox026Cell009_valid
  · exact middleDerivativeBox026Cell010_valid
  · exact middleDerivativeBox026Cell011_valid
  · exact middleDerivativeBox026Cell012_valid
  · exact middleDerivativeBox026Cell013_valid
  · exact middleDerivativeBox026Cell014_valid
  · exact middleDerivativeBox026Cell015_valid
  · exact middleDerivativeBox026Cell016_valid
  · exact middleDerivativeBox026Cell017_valid
  · exact middleDerivativeBox026Cell018_valid
  · exact middleDerivativeBox026Cell019_valid
  · exact middleDerivativeBox026Cell020_valid
  · exact middleDerivativeBox026Cell021_valid
  · exact middleDerivativeBox026Cell022_valid
  · exact middleDerivativeBox026Cell023_valid
  · exact middleDerivativeBox026Cell024_valid
  · exact middleDerivativeBox026Cell025_valid
  · exact middleDerivativeBox026Cell026_valid
  · exact middleDerivativeBox026Cell027_valid
  · exact middleDerivativeBox026Cell028_valid
  · exact middleDerivativeBox026Cell029_valid
  · exact middleDerivativeBox026Cell030_valid
  · exact middleDerivativeBox026Cell031_valid
  · exact middleDerivativeBox026Cell032_valid
  · exact middleDerivativeBox026Cell033_valid
  · exact middleDerivativeBox026Cell034_valid
  · exact middleDerivativeBox026Cell035_valid
  · exact middleDerivativeBox026Cell036_valid
  · exact middleDerivativeBox026Cell037_valid
  · exact middleDerivativeBox026Cell038_valid
  · exact middleDerivativeBox026Cell039_valid
theorem middleDerivativeBox026_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox026Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox026Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox026_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox026Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox026Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox026_partial_bounds {t a : ℝ} (htl : ((219/250) : ℝ) ≤ t) (htu : t ≤ ((877/1000) : ℝ))
    (hal : ((983861273098381/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((985471885834381/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters026 middleDerivativeParameters026_valid middleDerivativeBox026Cells (1/20) middleDerivativeBox026Cells_valid middleDerivativeBox026_upperA middleDerivativeBox026_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox026_derivative {t : ℝ} (htl : ((219/250) : ℝ) ≤ t) (htu : t ≤ ((877/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox026_enclosure htl htu
  have hp := middleDerivativeParameters026.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters026_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox026_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((877/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox026_derivative
