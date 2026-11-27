import TwoAxisHelicoid.MiddleVerticalBox001
import TwoAxisHelicoid.MiddleDerivativeBox001Cell000
import TwoAxisHelicoid.MiddleDerivativeBox001Cell001
import TwoAxisHelicoid.MiddleDerivativeBox001Cell002
import TwoAxisHelicoid.MiddleDerivativeBox001Cell003
import TwoAxisHelicoid.MiddleDerivativeBox001Cell004
import TwoAxisHelicoid.MiddleDerivativeBox001Cell005
import TwoAxisHelicoid.MiddleDerivativeBox001Cell006
import TwoAxisHelicoid.MiddleDerivativeBox001Cell007
import TwoAxisHelicoid.MiddleDerivativeBox001Cell008
import TwoAxisHelicoid.MiddleDerivativeBox001Cell009
import TwoAxisHelicoid.MiddleDerivativeBox001Cell010
import TwoAxisHelicoid.MiddleDerivativeBox001Cell011
import TwoAxisHelicoid.MiddleDerivativeBox001Cell012
import TwoAxisHelicoid.MiddleDerivativeBox001Cell013
import TwoAxisHelicoid.MiddleDerivativeBox001Cell014
import TwoAxisHelicoid.MiddleDerivativeBox001Cell015
import TwoAxisHelicoid.MiddleDerivativeBox001Cell016
import TwoAxisHelicoid.MiddleDerivativeBox001Cell017
import TwoAxisHelicoid.MiddleDerivativeBox001Cell018
import TwoAxisHelicoid.MiddleDerivativeBox001Cell019
import TwoAxisHelicoid.MiddleDerivativeBox001Cell020
import TwoAxisHelicoid.MiddleDerivativeBox001Cell021
import TwoAxisHelicoid.MiddleDerivativeBox001Cell022
import TwoAxisHelicoid.MiddleDerivativeBox001Cell023
import TwoAxisHelicoid.MiddleDerivativeBox001Cell024
import TwoAxisHelicoid.MiddleDerivativeBox001Cell025
import TwoAxisHelicoid.MiddleDerivativeBox001Cell026
import TwoAxisHelicoid.MiddleDerivativeBox001Cell027
import TwoAxisHelicoid.MiddleDerivativeBox001Cell028
import TwoAxisHelicoid.MiddleDerivativeBox001Cell029
import TwoAxisHelicoid.MiddleDerivativeBox001Cell030
import TwoAxisHelicoid.MiddleDerivativeBox001Cell031
import TwoAxisHelicoid.MiddleDerivativeBox001Cell032
import TwoAxisHelicoid.MiddleDerivativeBox001Cell033
import TwoAxisHelicoid.MiddleDerivativeBox001Cell034
import TwoAxisHelicoid.MiddleDerivativeBox001Cell035
import TwoAxisHelicoid.MiddleDerivativeBox001Cell036
import TwoAxisHelicoid.MiddleDerivativeBox001Cell037
import TwoAxisHelicoid.MiddleDerivativeBox001Cell038
import TwoAxisHelicoid.MiddleDerivativeBox001Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox001Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox001Cell000,middleDerivativeBox001Cell001,middleDerivativeBox001Cell002,middleDerivativeBox001Cell003,middleDerivativeBox001Cell004,middleDerivativeBox001Cell005,middleDerivativeBox001Cell006,middleDerivativeBox001Cell007,middleDerivativeBox001Cell008,middleDerivativeBox001Cell009,middleDerivativeBox001Cell010,middleDerivativeBox001Cell011,middleDerivativeBox001Cell012,middleDerivativeBox001Cell013,middleDerivativeBox001Cell014,middleDerivativeBox001Cell015,middleDerivativeBox001Cell016,middleDerivativeBox001Cell017,middleDerivativeBox001Cell018,middleDerivativeBox001Cell019,middleDerivativeBox001Cell020,middleDerivativeBox001Cell021,middleDerivativeBox001Cell022,middleDerivativeBox001Cell023,middleDerivativeBox001Cell024,middleDerivativeBox001Cell025,middleDerivativeBox001Cell026,middleDerivativeBox001Cell027,middleDerivativeBox001Cell028,middleDerivativeBox001Cell029,middleDerivativeBox001Cell030,middleDerivativeBox001Cell031,middleDerivativeBox001Cell032,middleDerivativeBox001Cell033,middleDerivativeBox001Cell034,middleDerivativeBox001Cell035,middleDerivativeBox001Cell036,middleDerivativeBox001Cell037,middleDerivativeBox001Cell038,middleDerivativeBox001Cell039]
theorem middleDerivativeBox001Cells_valid : ∀ i : Fin 40, (middleDerivativeBox001Cells i).Valid middleRangeSetup middleDerivativeParameters001 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox001Cell000_valid
  · exact middleDerivativeBox001Cell001_valid
  · exact middleDerivativeBox001Cell002_valid
  · exact middleDerivativeBox001Cell003_valid
  · exact middleDerivativeBox001Cell004_valid
  · exact middleDerivativeBox001Cell005_valid
  · exact middleDerivativeBox001Cell006_valid
  · exact middleDerivativeBox001Cell007_valid
  · exact middleDerivativeBox001Cell008_valid
  · exact middleDerivativeBox001Cell009_valid
  · exact middleDerivativeBox001Cell010_valid
  · exact middleDerivativeBox001Cell011_valid
  · exact middleDerivativeBox001Cell012_valid
  · exact middleDerivativeBox001Cell013_valid
  · exact middleDerivativeBox001Cell014_valid
  · exact middleDerivativeBox001Cell015_valid
  · exact middleDerivativeBox001Cell016_valid
  · exact middleDerivativeBox001Cell017_valid
  · exact middleDerivativeBox001Cell018_valid
  · exact middleDerivativeBox001Cell019_valid
  · exact middleDerivativeBox001Cell020_valid
  · exact middleDerivativeBox001Cell021_valid
  · exact middleDerivativeBox001Cell022_valid
  · exact middleDerivativeBox001Cell023_valid
  · exact middleDerivativeBox001Cell024_valid
  · exact middleDerivativeBox001Cell025_valid
  · exact middleDerivativeBox001Cell026_valid
  · exact middleDerivativeBox001Cell027_valid
  · exact middleDerivativeBox001Cell028_valid
  · exact middleDerivativeBox001Cell029_valid
  · exact middleDerivativeBox001Cell030_valid
  · exact middleDerivativeBox001Cell031_valid
  · exact middleDerivativeBox001Cell032_valid
  · exact middleDerivativeBox001Cell033_valid
  · exact middleDerivativeBox001Cell034_valid
  · exact middleDerivativeBox001Cell035_valid
  · exact middleDerivativeBox001Cell036_valid
  · exact middleDerivativeBox001Cell037_valid
  · exact middleDerivativeBox001Cell038_valid
  · exact middleDerivativeBox001Cell039_valid
theorem middleDerivativeBox001_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox001Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox001Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox001_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox001Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox001Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox001_partial_bounds {t a : ℝ} (htl : ((851/1000) : ℝ) ≤ t) (htu : t ≤ ((213/250) : ℝ))
    (hal : ((38824337804321/65970697666560) : ℝ) ≤ a) (hau : a ≤ ((38888762313761/65970697666560) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters001 middleDerivativeParameters001_valid middleDerivativeBox001Cells (1/20) middleDerivativeBox001Cells_valid middleDerivativeBox001_upperA middleDerivativeBox001_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox001_derivative {t : ℝ} (htl : ((851/1000) : ℝ) ≤ t) (htu : t ≤ ((213/250) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox001_enclosure htl htu
  have hp := middleDerivativeParameters001.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters001_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox001_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((213/250) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox001_derivative
