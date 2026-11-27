import TwoAxisHelicoid.MiddleVerticalBox025
import TwoAxisHelicoid.MiddleDerivativeBox025Cell000
import TwoAxisHelicoid.MiddleDerivativeBox025Cell001
import TwoAxisHelicoid.MiddleDerivativeBox025Cell002
import TwoAxisHelicoid.MiddleDerivativeBox025Cell003
import TwoAxisHelicoid.MiddleDerivativeBox025Cell004
import TwoAxisHelicoid.MiddleDerivativeBox025Cell005
import TwoAxisHelicoid.MiddleDerivativeBox025Cell006
import TwoAxisHelicoid.MiddleDerivativeBox025Cell007
import TwoAxisHelicoid.MiddleDerivativeBox025Cell008
import TwoAxisHelicoid.MiddleDerivativeBox025Cell009
import TwoAxisHelicoid.MiddleDerivativeBox025Cell010
import TwoAxisHelicoid.MiddleDerivativeBox025Cell011
import TwoAxisHelicoid.MiddleDerivativeBox025Cell012
import TwoAxisHelicoid.MiddleDerivativeBox025Cell013
import TwoAxisHelicoid.MiddleDerivativeBox025Cell014
import TwoAxisHelicoid.MiddleDerivativeBox025Cell015
import TwoAxisHelicoid.MiddleDerivativeBox025Cell016
import TwoAxisHelicoid.MiddleDerivativeBox025Cell017
import TwoAxisHelicoid.MiddleDerivativeBox025Cell018
import TwoAxisHelicoid.MiddleDerivativeBox025Cell019
import TwoAxisHelicoid.MiddleDerivativeBox025Cell020
import TwoAxisHelicoid.MiddleDerivativeBox025Cell021
import TwoAxisHelicoid.MiddleDerivativeBox025Cell022
import TwoAxisHelicoid.MiddleDerivativeBox025Cell023
import TwoAxisHelicoid.MiddleDerivativeBox025Cell024
import TwoAxisHelicoid.MiddleDerivativeBox025Cell025
import TwoAxisHelicoid.MiddleDerivativeBox025Cell026
import TwoAxisHelicoid.MiddleDerivativeBox025Cell027
import TwoAxisHelicoid.MiddleDerivativeBox025Cell028
import TwoAxisHelicoid.MiddleDerivativeBox025Cell029
import TwoAxisHelicoid.MiddleDerivativeBox025Cell030
import TwoAxisHelicoid.MiddleDerivativeBox025Cell031
import TwoAxisHelicoid.MiddleDerivativeBox025Cell032
import TwoAxisHelicoid.MiddleDerivativeBox025Cell033
import TwoAxisHelicoid.MiddleDerivativeBox025Cell034
import TwoAxisHelicoid.MiddleDerivativeBox025Cell035
import TwoAxisHelicoid.MiddleDerivativeBox025Cell036
import TwoAxisHelicoid.MiddleDerivativeBox025Cell037
import TwoAxisHelicoid.MiddleDerivativeBox025Cell038
import TwoAxisHelicoid.MiddleDerivativeBox025Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox025Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox025Cell000,middleDerivativeBox025Cell001,middleDerivativeBox025Cell002,middleDerivativeBox025Cell003,middleDerivativeBox025Cell004,middleDerivativeBox025Cell005,middleDerivativeBox025Cell006,middleDerivativeBox025Cell007,middleDerivativeBox025Cell008,middleDerivativeBox025Cell009,middleDerivativeBox025Cell010,middleDerivativeBox025Cell011,middleDerivativeBox025Cell012,middleDerivativeBox025Cell013,middleDerivativeBox025Cell014,middleDerivativeBox025Cell015,middleDerivativeBox025Cell016,middleDerivativeBox025Cell017,middleDerivativeBox025Cell018,middleDerivativeBox025Cell019,middleDerivativeBox025Cell020,middleDerivativeBox025Cell021,middleDerivativeBox025Cell022,middleDerivativeBox025Cell023,middleDerivativeBox025Cell024,middleDerivativeBox025Cell025,middleDerivativeBox025Cell026,middleDerivativeBox025Cell027,middleDerivativeBox025Cell028,middleDerivativeBox025Cell029,middleDerivativeBox025Cell030,middleDerivativeBox025Cell031,middleDerivativeBox025Cell032,middleDerivativeBox025Cell033,middleDerivativeBox025Cell034,middleDerivativeBox025Cell035,middleDerivativeBox025Cell036,middleDerivativeBox025Cell037,middleDerivativeBox025Cell038,middleDerivativeBox025Cell039]
theorem middleDerivativeBox025Cells_valid : ∀ i : Fin 40, (middleDerivativeBox025Cells i).Valid middleRangeSetup middleDerivativeParameters025 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox025Cell000_valid
  · exact middleDerivativeBox025Cell001_valid
  · exact middleDerivativeBox025Cell002_valid
  · exact middleDerivativeBox025Cell003_valid
  · exact middleDerivativeBox025Cell004_valid
  · exact middleDerivativeBox025Cell005_valid
  · exact middleDerivativeBox025Cell006_valid
  · exact middleDerivativeBox025Cell007_valid
  · exact middleDerivativeBox025Cell008_valid
  · exact middleDerivativeBox025Cell009_valid
  · exact middleDerivativeBox025Cell010_valid
  · exact middleDerivativeBox025Cell011_valid
  · exact middleDerivativeBox025Cell012_valid
  · exact middleDerivativeBox025Cell013_valid
  · exact middleDerivativeBox025Cell014_valid
  · exact middleDerivativeBox025Cell015_valid
  · exact middleDerivativeBox025Cell016_valid
  · exact middleDerivativeBox025Cell017_valid
  · exact middleDerivativeBox025Cell018_valid
  · exact middleDerivativeBox025Cell019_valid
  · exact middleDerivativeBox025Cell020_valid
  · exact middleDerivativeBox025Cell021_valid
  · exact middleDerivativeBox025Cell022_valid
  · exact middleDerivativeBox025Cell023_valid
  · exact middleDerivativeBox025Cell024_valid
  · exact middleDerivativeBox025Cell025_valid
  · exact middleDerivativeBox025Cell026_valid
  · exact middleDerivativeBox025Cell027_valid
  · exact middleDerivativeBox025Cell028_valid
  · exact middleDerivativeBox025Cell029_valid
  · exact middleDerivativeBox025Cell030_valid
  · exact middleDerivativeBox025Cell031_valid
  · exact middleDerivativeBox025Cell032_valid
  · exact middleDerivativeBox025Cell033_valid
  · exact middleDerivativeBox025Cell034_valid
  · exact middleDerivativeBox025Cell035_valid
  · exact middleDerivativeBox025Cell036_valid
  · exact middleDerivativeBox025Cell037_valid
  · exact middleDerivativeBox025Cell038_valid
  · exact middleDerivativeBox025Cell039_valid
theorem middleDerivativeBox025_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox025Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox025Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox025_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox025Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox025Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox025_partial_bounds {t a : ℝ} (htl : ((7/8) : ℝ) ≤ t) (htu : t ≤ ((219/250) : ℝ))
    (hal : ((327773133521409/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((328310004433409/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters025 middleDerivativeParameters025_valid middleDerivativeBox025Cells (1/20) middleDerivativeBox025Cells_valid middleDerivativeBox025_upperA middleDerivativeBox025_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox025_derivative {t : ℝ} (htl : ((7/8) : ℝ) ≤ t) (htu : t ≤ ((219/250) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox025_enclosure htl htu
  have hp := middleDerivativeParameters025.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters025_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox025_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((219/250) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox025_derivative
