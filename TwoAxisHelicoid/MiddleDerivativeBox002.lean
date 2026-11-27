import TwoAxisHelicoid.MiddleVerticalBox002
import TwoAxisHelicoid.MiddleDerivativeBox002Cell000
import TwoAxisHelicoid.MiddleDerivativeBox002Cell001
import TwoAxisHelicoid.MiddleDerivativeBox002Cell002
import TwoAxisHelicoid.MiddleDerivativeBox002Cell003
import TwoAxisHelicoid.MiddleDerivativeBox002Cell004
import TwoAxisHelicoid.MiddleDerivativeBox002Cell005
import TwoAxisHelicoid.MiddleDerivativeBox002Cell006
import TwoAxisHelicoid.MiddleDerivativeBox002Cell007
import TwoAxisHelicoid.MiddleDerivativeBox002Cell008
import TwoAxisHelicoid.MiddleDerivativeBox002Cell009
import TwoAxisHelicoid.MiddleDerivativeBox002Cell010
import TwoAxisHelicoid.MiddleDerivativeBox002Cell011
import TwoAxisHelicoid.MiddleDerivativeBox002Cell012
import TwoAxisHelicoid.MiddleDerivativeBox002Cell013
import TwoAxisHelicoid.MiddleDerivativeBox002Cell014
import TwoAxisHelicoid.MiddleDerivativeBox002Cell015
import TwoAxisHelicoid.MiddleDerivativeBox002Cell016
import TwoAxisHelicoid.MiddleDerivativeBox002Cell017
import TwoAxisHelicoid.MiddleDerivativeBox002Cell018
import TwoAxisHelicoid.MiddleDerivativeBox002Cell019
import TwoAxisHelicoid.MiddleDerivativeBox002Cell020
import TwoAxisHelicoid.MiddleDerivativeBox002Cell021
import TwoAxisHelicoid.MiddleDerivativeBox002Cell022
import TwoAxisHelicoid.MiddleDerivativeBox002Cell023
import TwoAxisHelicoid.MiddleDerivativeBox002Cell024
import TwoAxisHelicoid.MiddleDerivativeBox002Cell025
import TwoAxisHelicoid.MiddleDerivativeBox002Cell026
import TwoAxisHelicoid.MiddleDerivativeBox002Cell027
import TwoAxisHelicoid.MiddleDerivativeBox002Cell028
import TwoAxisHelicoid.MiddleDerivativeBox002Cell029
import TwoAxisHelicoid.MiddleDerivativeBox002Cell030
import TwoAxisHelicoid.MiddleDerivativeBox002Cell031
import TwoAxisHelicoid.MiddleDerivativeBox002Cell032
import TwoAxisHelicoid.MiddleDerivativeBox002Cell033
import TwoAxisHelicoid.MiddleDerivativeBox002Cell034
import TwoAxisHelicoid.MiddleDerivativeBox002Cell035
import TwoAxisHelicoid.MiddleDerivativeBox002Cell036
import TwoAxisHelicoid.MiddleDerivativeBox002Cell037
import TwoAxisHelicoid.MiddleDerivativeBox002Cell038
import TwoAxisHelicoid.MiddleDerivativeBox002Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox002Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox002Cell000,middleDerivativeBox002Cell001,middleDerivativeBox002Cell002,middleDerivativeBox002Cell003,middleDerivativeBox002Cell004,middleDerivativeBox002Cell005,middleDerivativeBox002Cell006,middleDerivativeBox002Cell007,middleDerivativeBox002Cell008,middleDerivativeBox002Cell009,middleDerivativeBox002Cell010,middleDerivativeBox002Cell011,middleDerivativeBox002Cell012,middleDerivativeBox002Cell013,middleDerivativeBox002Cell014,middleDerivativeBox002Cell015,middleDerivativeBox002Cell016,middleDerivativeBox002Cell017,middleDerivativeBox002Cell018,middleDerivativeBox002Cell019,middleDerivativeBox002Cell020,middleDerivativeBox002Cell021,middleDerivativeBox002Cell022,middleDerivativeBox002Cell023,middleDerivativeBox002Cell024,middleDerivativeBox002Cell025,middleDerivativeBox002Cell026,middleDerivativeBox002Cell027,middleDerivativeBox002Cell028,middleDerivativeBox002Cell029,middleDerivativeBox002Cell030,middleDerivativeBox002Cell031,middleDerivativeBox002Cell032,middleDerivativeBox002Cell033,middleDerivativeBox002Cell034,middleDerivativeBox002Cell035,middleDerivativeBox002Cell036,middleDerivativeBox002Cell037,middleDerivativeBox002Cell038,middleDerivativeBox002Cell039]
theorem middleDerivativeBox002Cells_valid : ∀ i : Fin 40, (middleDerivativeBox002Cells i).Valid middleRangeSetup middleDerivativeParameters002 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox002Cell000_valid
  · exact middleDerivativeBox002Cell001_valid
  · exact middleDerivativeBox002Cell002_valid
  · exact middleDerivativeBox002Cell003_valid
  · exact middleDerivativeBox002Cell004_valid
  · exact middleDerivativeBox002Cell005_valid
  · exact middleDerivativeBox002Cell006_valid
  · exact middleDerivativeBox002Cell007_valid
  · exact middleDerivativeBox002Cell008_valid
  · exact middleDerivativeBox002Cell009_valid
  · exact middleDerivativeBox002Cell010_valid
  · exact middleDerivativeBox002Cell011_valid
  · exact middleDerivativeBox002Cell012_valid
  · exact middleDerivativeBox002Cell013_valid
  · exact middleDerivativeBox002Cell014_valid
  · exact middleDerivativeBox002Cell015_valid
  · exact middleDerivativeBox002Cell016_valid
  · exact middleDerivativeBox002Cell017_valid
  · exact middleDerivativeBox002Cell018_valid
  · exact middleDerivativeBox002Cell019_valid
  · exact middleDerivativeBox002Cell020_valid
  · exact middleDerivativeBox002Cell021_valid
  · exact middleDerivativeBox002Cell022_valid
  · exact middleDerivativeBox002Cell023_valid
  · exact middleDerivativeBox002Cell024_valid
  · exact middleDerivativeBox002Cell025_valid
  · exact middleDerivativeBox002Cell026_valid
  · exact middleDerivativeBox002Cell027_valid
  · exact middleDerivativeBox002Cell028_valid
  · exact middleDerivativeBox002Cell029_valid
  · exact middleDerivativeBox002Cell030_valid
  · exact middleDerivativeBox002Cell031_valid
  · exact middleDerivativeBox002Cell032_valid
  · exact middleDerivativeBox002Cell033_valid
  · exact middleDerivativeBox002Cell034_valid
  · exact middleDerivativeBox002Cell035_valid
  · exact middleDerivativeBox002Cell036_valid
  · exact middleDerivativeBox002Cell037_valid
  · exact middleDerivativeBox002Cell038_valid
  · exact middleDerivativeBox002Cell039_valid
theorem middleDerivativeBox002_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox002Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox002Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox002_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox002Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox002Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox002_partial_bounds {t a : ℝ} (htl : ((213/250) : ℝ) ≤ t) (htu : t ≤ ((853/1000) : ℝ))
    (hal : ((323708955878011/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((324245826790011/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters002 middleDerivativeParameters002_valid middleDerivativeBox002Cells (1/20) middleDerivativeBox002Cells_valid middleDerivativeBox002_upperA middleDerivativeBox002_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox002_derivative {t : ℝ} (htl : ((213/250) : ℝ) ≤ t) (htu : t ≤ ((853/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox002_enclosure htl htu
  have hp := middleDerivativeParameters002.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters002_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox002_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((853/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox002_derivative
