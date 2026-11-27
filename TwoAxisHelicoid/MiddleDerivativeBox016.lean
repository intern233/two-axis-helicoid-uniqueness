import TwoAxisHelicoid.MiddleVerticalBox016
import TwoAxisHelicoid.MiddleDerivativeBox016Cell000
import TwoAxisHelicoid.MiddleDerivativeBox016Cell001
import TwoAxisHelicoid.MiddleDerivativeBox016Cell002
import TwoAxisHelicoid.MiddleDerivativeBox016Cell003
import TwoAxisHelicoid.MiddleDerivativeBox016Cell004
import TwoAxisHelicoid.MiddleDerivativeBox016Cell005
import TwoAxisHelicoid.MiddleDerivativeBox016Cell006
import TwoAxisHelicoid.MiddleDerivativeBox016Cell007
import TwoAxisHelicoid.MiddleDerivativeBox016Cell008
import TwoAxisHelicoid.MiddleDerivativeBox016Cell009
import TwoAxisHelicoid.MiddleDerivativeBox016Cell010
import TwoAxisHelicoid.MiddleDerivativeBox016Cell011
import TwoAxisHelicoid.MiddleDerivativeBox016Cell012
import TwoAxisHelicoid.MiddleDerivativeBox016Cell013
import TwoAxisHelicoid.MiddleDerivativeBox016Cell014
import TwoAxisHelicoid.MiddleDerivativeBox016Cell015
import TwoAxisHelicoid.MiddleDerivativeBox016Cell016
import TwoAxisHelicoid.MiddleDerivativeBox016Cell017
import TwoAxisHelicoid.MiddleDerivativeBox016Cell018
import TwoAxisHelicoid.MiddleDerivativeBox016Cell019
import TwoAxisHelicoid.MiddleDerivativeBox016Cell020
import TwoAxisHelicoid.MiddleDerivativeBox016Cell021
import TwoAxisHelicoid.MiddleDerivativeBox016Cell022
import TwoAxisHelicoid.MiddleDerivativeBox016Cell023
import TwoAxisHelicoid.MiddleDerivativeBox016Cell024
import TwoAxisHelicoid.MiddleDerivativeBox016Cell025
import TwoAxisHelicoid.MiddleDerivativeBox016Cell026
import TwoAxisHelicoid.MiddleDerivativeBox016Cell027
import TwoAxisHelicoid.MiddleDerivativeBox016Cell028
import TwoAxisHelicoid.MiddleDerivativeBox016Cell029
import TwoAxisHelicoid.MiddleDerivativeBox016Cell030
import TwoAxisHelicoid.MiddleDerivativeBox016Cell031
import TwoAxisHelicoid.MiddleDerivativeBox016Cell032
import TwoAxisHelicoid.MiddleDerivativeBox016Cell033
import TwoAxisHelicoid.MiddleDerivativeBox016Cell034
import TwoAxisHelicoid.MiddleDerivativeBox016Cell035
import TwoAxisHelicoid.MiddleDerivativeBox016Cell036
import TwoAxisHelicoid.MiddleDerivativeBox016Cell037
import TwoAxisHelicoid.MiddleDerivativeBox016Cell038
import TwoAxisHelicoid.MiddleDerivativeBox016Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox016Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox016Cell000,middleDerivativeBox016Cell001,middleDerivativeBox016Cell002,middleDerivativeBox016Cell003,middleDerivativeBox016Cell004,middleDerivativeBox016Cell005,middleDerivativeBox016Cell006,middleDerivativeBox016Cell007,middleDerivativeBox016Cell008,middleDerivativeBox016Cell009,middleDerivativeBox016Cell010,middleDerivativeBox016Cell011,middleDerivativeBox016Cell012,middleDerivativeBox016Cell013,middleDerivativeBox016Cell014,middleDerivativeBox016Cell015,middleDerivativeBox016Cell016,middleDerivativeBox016Cell017,middleDerivativeBox016Cell018,middleDerivativeBox016Cell019,middleDerivativeBox016Cell020,middleDerivativeBox016Cell021,middleDerivativeBox016Cell022,middleDerivativeBox016Cell023,middleDerivativeBox016Cell024,middleDerivativeBox016Cell025,middleDerivativeBox016Cell026,middleDerivativeBox016Cell027,middleDerivativeBox016Cell028,middleDerivativeBox016Cell029,middleDerivativeBox016Cell030,middleDerivativeBox016Cell031,middleDerivativeBox016Cell032,middleDerivativeBox016Cell033,middleDerivativeBox016Cell034,middleDerivativeBox016Cell035,middleDerivativeBox016Cell036,middleDerivativeBox016Cell037,middleDerivativeBox016Cell038,middleDerivativeBox016Cell039]
theorem middleDerivativeBox016Cells_valid : ∀ i : Fin 40, (middleDerivativeBox016Cells i).Valid middleRangeSetup middleDerivativeParameters016 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox016Cell000_valid
  · exact middleDerivativeBox016Cell001_valid
  · exact middleDerivativeBox016Cell002_valid
  · exact middleDerivativeBox016Cell003_valid
  · exact middleDerivativeBox016Cell004_valid
  · exact middleDerivativeBox016Cell005_valid
  · exact middleDerivativeBox016Cell006_valid
  · exact middleDerivativeBox016Cell007_valid
  · exact middleDerivativeBox016Cell008_valid
  · exact middleDerivativeBox016Cell009_valid
  · exact middleDerivativeBox016Cell010_valid
  · exact middleDerivativeBox016Cell011_valid
  · exact middleDerivativeBox016Cell012_valid
  · exact middleDerivativeBox016Cell013_valid
  · exact middleDerivativeBox016Cell014_valid
  · exact middleDerivativeBox016Cell015_valid
  · exact middleDerivativeBox016Cell016_valid
  · exact middleDerivativeBox016Cell017_valid
  · exact middleDerivativeBox016Cell018_valid
  · exact middleDerivativeBox016Cell019_valid
  · exact middleDerivativeBox016Cell020_valid
  · exact middleDerivativeBox016Cell021_valid
  · exact middleDerivativeBox016Cell022_valid
  · exact middleDerivativeBox016Cell023_valid
  · exact middleDerivativeBox016Cell024_valid
  · exact middleDerivativeBox016Cell025_valid
  · exact middleDerivativeBox016Cell026_valid
  · exact middleDerivativeBox016Cell027_valid
  · exact middleDerivativeBox016Cell028_valid
  · exact middleDerivativeBox016Cell029_valid
  · exact middleDerivativeBox016Cell030_valid
  · exact middleDerivativeBox016Cell031_valid
  · exact middleDerivativeBox016Cell032_valid
  · exact middleDerivativeBox016Cell033_valid
  · exact middleDerivativeBox016Cell034_valid
  · exact middleDerivativeBox016Cell035_valid
  · exact middleDerivativeBox016Cell036_valid
  · exact middleDerivativeBox016Cell037_valid
  · exact middleDerivativeBox016Cell038_valid
  · exact middleDerivativeBox016Cell039_valid
theorem middleDerivativeBox016_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox016Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox016Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox016_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox016Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox016Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox016_partial_bounds {t a : ℝ} (htl : ((433/500) : ℝ) ≤ t) (htu : t ≤ ((867/1000) : ℝ))
    (hal : ((326162273349547/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((326699144261547/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters016 middleDerivativeParameters016_valid middleDerivativeBox016Cells (1/20) middleDerivativeBox016Cells_valid middleDerivativeBox016_upperA middleDerivativeBox016_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox016_derivative {t : ℝ} (htl : ((433/500) : ℝ) ≤ t) (htu : t ≤ ((867/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox016_enclosure htl htu
  have hp := middleDerivativeParameters016.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters016_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox016_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((867/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox016_derivative
