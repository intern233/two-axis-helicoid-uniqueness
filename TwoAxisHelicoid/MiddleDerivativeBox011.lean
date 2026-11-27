import TwoAxisHelicoid.MiddleVerticalBox011
import TwoAxisHelicoid.MiddleDerivativeBox011Cell000
import TwoAxisHelicoid.MiddleDerivativeBox011Cell001
import TwoAxisHelicoid.MiddleDerivativeBox011Cell002
import TwoAxisHelicoid.MiddleDerivativeBox011Cell003
import TwoAxisHelicoid.MiddleDerivativeBox011Cell004
import TwoAxisHelicoid.MiddleDerivativeBox011Cell005
import TwoAxisHelicoid.MiddleDerivativeBox011Cell006
import TwoAxisHelicoid.MiddleDerivativeBox011Cell007
import TwoAxisHelicoid.MiddleDerivativeBox011Cell008
import TwoAxisHelicoid.MiddleDerivativeBox011Cell009
import TwoAxisHelicoid.MiddleDerivativeBox011Cell010
import TwoAxisHelicoid.MiddleDerivativeBox011Cell011
import TwoAxisHelicoid.MiddleDerivativeBox011Cell012
import TwoAxisHelicoid.MiddleDerivativeBox011Cell013
import TwoAxisHelicoid.MiddleDerivativeBox011Cell014
import TwoAxisHelicoid.MiddleDerivativeBox011Cell015
import TwoAxisHelicoid.MiddleDerivativeBox011Cell016
import TwoAxisHelicoid.MiddleDerivativeBox011Cell017
import TwoAxisHelicoid.MiddleDerivativeBox011Cell018
import TwoAxisHelicoid.MiddleDerivativeBox011Cell019
import TwoAxisHelicoid.MiddleDerivativeBox011Cell020
import TwoAxisHelicoid.MiddleDerivativeBox011Cell021
import TwoAxisHelicoid.MiddleDerivativeBox011Cell022
import TwoAxisHelicoid.MiddleDerivativeBox011Cell023
import TwoAxisHelicoid.MiddleDerivativeBox011Cell024
import TwoAxisHelicoid.MiddleDerivativeBox011Cell025
import TwoAxisHelicoid.MiddleDerivativeBox011Cell026
import TwoAxisHelicoid.MiddleDerivativeBox011Cell027
import TwoAxisHelicoid.MiddleDerivativeBox011Cell028
import TwoAxisHelicoid.MiddleDerivativeBox011Cell029
import TwoAxisHelicoid.MiddleDerivativeBox011Cell030
import TwoAxisHelicoid.MiddleDerivativeBox011Cell031
import TwoAxisHelicoid.MiddleDerivativeBox011Cell032
import TwoAxisHelicoid.MiddleDerivativeBox011Cell033
import TwoAxisHelicoid.MiddleDerivativeBox011Cell034
import TwoAxisHelicoid.MiddleDerivativeBox011Cell035
import TwoAxisHelicoid.MiddleDerivativeBox011Cell036
import TwoAxisHelicoid.MiddleDerivativeBox011Cell037
import TwoAxisHelicoid.MiddleDerivativeBox011Cell038
import TwoAxisHelicoid.MiddleDerivativeBox011Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox011Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox011Cell000,middleDerivativeBox011Cell001,middleDerivativeBox011Cell002,middleDerivativeBox011Cell003,middleDerivativeBox011Cell004,middleDerivativeBox011Cell005,middleDerivativeBox011Cell006,middleDerivativeBox011Cell007,middleDerivativeBox011Cell008,middleDerivativeBox011Cell009,middleDerivativeBox011Cell010,middleDerivativeBox011Cell011,middleDerivativeBox011Cell012,middleDerivativeBox011Cell013,middleDerivativeBox011Cell014,middleDerivativeBox011Cell015,middleDerivativeBox011Cell016,middleDerivativeBox011Cell017,middleDerivativeBox011Cell018,middleDerivativeBox011Cell019,middleDerivativeBox011Cell020,middleDerivativeBox011Cell021,middleDerivativeBox011Cell022,middleDerivativeBox011Cell023,middleDerivativeBox011Cell024,middleDerivativeBox011Cell025,middleDerivativeBox011Cell026,middleDerivativeBox011Cell027,middleDerivativeBox011Cell028,middleDerivativeBox011Cell029,middleDerivativeBox011Cell030,middleDerivativeBox011Cell031,middleDerivativeBox011Cell032,middleDerivativeBox011Cell033,middleDerivativeBox011Cell034,middleDerivativeBox011Cell035,middleDerivativeBox011Cell036,middleDerivativeBox011Cell037,middleDerivativeBox011Cell038,middleDerivativeBox011Cell039]
theorem middleDerivativeBox011Cells_valid : ∀ i : Fin 40, (middleDerivativeBox011Cells i).Valid middleRangeSetup middleDerivativeParameters011 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox011Cell000_valid
  · exact middleDerivativeBox011Cell001_valid
  · exact middleDerivativeBox011Cell002_valid
  · exact middleDerivativeBox011Cell003_valid
  · exact middleDerivativeBox011Cell004_valid
  · exact middleDerivativeBox011Cell005_valid
  · exact middleDerivativeBox011Cell006_valid
  · exact middleDerivativeBox011Cell007_valid
  · exact middleDerivativeBox011Cell008_valid
  · exact middleDerivativeBox011Cell009_valid
  · exact middleDerivativeBox011Cell010_valid
  · exact middleDerivativeBox011Cell011_valid
  · exact middleDerivativeBox011Cell012_valid
  · exact middleDerivativeBox011Cell013_valid
  · exact middleDerivativeBox011Cell014_valid
  · exact middleDerivativeBox011Cell015_valid
  · exact middleDerivativeBox011Cell016_valid
  · exact middleDerivativeBox011Cell017_valid
  · exact middleDerivativeBox011Cell018_valid
  · exact middleDerivativeBox011Cell019_valid
  · exact middleDerivativeBox011Cell020_valid
  · exact middleDerivativeBox011Cell021_valid
  · exact middleDerivativeBox011Cell022_valid
  · exact middleDerivativeBox011Cell023_valid
  · exact middleDerivativeBox011Cell024_valid
  · exact middleDerivativeBox011Cell025_valid
  · exact middleDerivativeBox011Cell026_valid
  · exact middleDerivativeBox011Cell027_valid
  · exact middleDerivativeBox011Cell028_valid
  · exact middleDerivativeBox011Cell029_valid
  · exact middleDerivativeBox011Cell030_valid
  · exact middleDerivativeBox011Cell031_valid
  · exact middleDerivativeBox011Cell032_valid
  · exact middleDerivativeBox011Cell033_valid
  · exact middleDerivativeBox011Cell034_valid
  · exact middleDerivativeBox011Cell035_valid
  · exact middleDerivativeBox011Cell036_valid
  · exact middleDerivativeBox011Cell037_valid
  · exact middleDerivativeBox011Cell038_valid
  · exact middleDerivativeBox011Cell039_valid
theorem middleDerivativeBox011_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox011Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox011Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox011_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox011Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox011Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox011_partial_bounds {t a : ℝ} (htl : ((861/1000) : ℝ) ≤ t) (htu : t ≤ ((431/500) : ℝ))
    (hal : ((325278782640451/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((325815653552451/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters011 middleDerivativeParameters011_valid middleDerivativeBox011Cells (1/20) middleDerivativeBox011Cells_valid middleDerivativeBox011_upperA middleDerivativeBox011_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox011_derivative {t : ℝ} (htl : ((861/1000) : ℝ) ≤ t) (htu : t ≤ ((431/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox011_enclosure htl htu
  have hp := middleDerivativeParameters011.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters011_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox011_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((431/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox011_derivative
