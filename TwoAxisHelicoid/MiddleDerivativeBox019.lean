import TwoAxisHelicoid.MiddleVerticalBox019
import TwoAxisHelicoid.MiddleDerivativeBox019Cell000
import TwoAxisHelicoid.MiddleDerivativeBox019Cell001
import TwoAxisHelicoid.MiddleDerivativeBox019Cell002
import TwoAxisHelicoid.MiddleDerivativeBox019Cell003
import TwoAxisHelicoid.MiddleDerivativeBox019Cell004
import TwoAxisHelicoid.MiddleDerivativeBox019Cell005
import TwoAxisHelicoid.MiddleDerivativeBox019Cell006
import TwoAxisHelicoid.MiddleDerivativeBox019Cell007
import TwoAxisHelicoid.MiddleDerivativeBox019Cell008
import TwoAxisHelicoid.MiddleDerivativeBox019Cell009
import TwoAxisHelicoid.MiddleDerivativeBox019Cell010
import TwoAxisHelicoid.MiddleDerivativeBox019Cell011
import TwoAxisHelicoid.MiddleDerivativeBox019Cell012
import TwoAxisHelicoid.MiddleDerivativeBox019Cell013
import TwoAxisHelicoid.MiddleDerivativeBox019Cell014
import TwoAxisHelicoid.MiddleDerivativeBox019Cell015
import TwoAxisHelicoid.MiddleDerivativeBox019Cell016
import TwoAxisHelicoid.MiddleDerivativeBox019Cell017
import TwoAxisHelicoid.MiddleDerivativeBox019Cell018
import TwoAxisHelicoid.MiddleDerivativeBox019Cell019
import TwoAxisHelicoid.MiddleDerivativeBox019Cell020
import TwoAxisHelicoid.MiddleDerivativeBox019Cell021
import TwoAxisHelicoid.MiddleDerivativeBox019Cell022
import TwoAxisHelicoid.MiddleDerivativeBox019Cell023
import TwoAxisHelicoid.MiddleDerivativeBox019Cell024
import TwoAxisHelicoid.MiddleDerivativeBox019Cell025
import TwoAxisHelicoid.MiddleDerivativeBox019Cell026
import TwoAxisHelicoid.MiddleDerivativeBox019Cell027
import TwoAxisHelicoid.MiddleDerivativeBox019Cell028
import TwoAxisHelicoid.MiddleDerivativeBox019Cell029
import TwoAxisHelicoid.MiddleDerivativeBox019Cell030
import TwoAxisHelicoid.MiddleDerivativeBox019Cell031
import TwoAxisHelicoid.MiddleDerivativeBox019Cell032
import TwoAxisHelicoid.MiddleDerivativeBox019Cell033
import TwoAxisHelicoid.MiddleDerivativeBox019Cell034
import TwoAxisHelicoid.MiddleDerivativeBox019Cell035
import TwoAxisHelicoid.MiddleDerivativeBox019Cell036
import TwoAxisHelicoid.MiddleDerivativeBox019Cell037
import TwoAxisHelicoid.MiddleDerivativeBox019Cell038
import TwoAxisHelicoid.MiddleDerivativeBox019Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox019Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox019Cell000,middleDerivativeBox019Cell001,middleDerivativeBox019Cell002,middleDerivativeBox019Cell003,middleDerivativeBox019Cell004,middleDerivativeBox019Cell005,middleDerivativeBox019Cell006,middleDerivativeBox019Cell007,middleDerivativeBox019Cell008,middleDerivativeBox019Cell009,middleDerivativeBox019Cell010,middleDerivativeBox019Cell011,middleDerivativeBox019Cell012,middleDerivativeBox019Cell013,middleDerivativeBox019Cell014,middleDerivativeBox019Cell015,middleDerivativeBox019Cell016,middleDerivativeBox019Cell017,middleDerivativeBox019Cell018,middleDerivativeBox019Cell019,middleDerivativeBox019Cell020,middleDerivativeBox019Cell021,middleDerivativeBox019Cell022,middleDerivativeBox019Cell023,middleDerivativeBox019Cell024,middleDerivativeBox019Cell025,middleDerivativeBox019Cell026,middleDerivativeBox019Cell027,middleDerivativeBox019Cell028,middleDerivativeBox019Cell029,middleDerivativeBox019Cell030,middleDerivativeBox019Cell031,middleDerivativeBox019Cell032,middleDerivativeBox019Cell033,middleDerivativeBox019Cell034,middleDerivativeBox019Cell035,middleDerivativeBox019Cell036,middleDerivativeBox019Cell037,middleDerivativeBox019Cell038,middleDerivativeBox019Cell039]
theorem middleDerivativeBox019Cells_valid : ∀ i : Fin 40, (middleDerivativeBox019Cells i).Valid middleRangeSetup middleDerivativeParameters019 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox019Cell000_valid
  · exact middleDerivativeBox019Cell001_valid
  · exact middleDerivativeBox019Cell002_valid
  · exact middleDerivativeBox019Cell003_valid
  · exact middleDerivativeBox019Cell004_valid
  · exact middleDerivativeBox019Cell005_valid
  · exact middleDerivativeBox019Cell006_valid
  · exact middleDerivativeBox019Cell007_valid
  · exact middleDerivativeBox019Cell008_valid
  · exact middleDerivativeBox019Cell009_valid
  · exact middleDerivativeBox019Cell010_valid
  · exact middleDerivativeBox019Cell011_valid
  · exact middleDerivativeBox019Cell012_valid
  · exact middleDerivativeBox019Cell013_valid
  · exact middleDerivativeBox019Cell014_valid
  · exact middleDerivativeBox019Cell015_valid
  · exact middleDerivativeBox019Cell016_valid
  · exact middleDerivativeBox019Cell017_valid
  · exact middleDerivativeBox019Cell018_valid
  · exact middleDerivativeBox019Cell019_valid
  · exact middleDerivativeBox019Cell020_valid
  · exact middleDerivativeBox019Cell021_valid
  · exact middleDerivativeBox019Cell022_valid
  · exact middleDerivativeBox019Cell023_valid
  · exact middleDerivativeBox019Cell024_valid
  · exact middleDerivativeBox019Cell025_valid
  · exact middleDerivativeBox019Cell026_valid
  · exact middleDerivativeBox019Cell027_valid
  · exact middleDerivativeBox019Cell028_valid
  · exact middleDerivativeBox019Cell029_valid
  · exact middleDerivativeBox019Cell030_valid
  · exact middleDerivativeBox019Cell031_valid
  · exact middleDerivativeBox019Cell032_valid
  · exact middleDerivativeBox019Cell033_valid
  · exact middleDerivativeBox019Cell034_valid
  · exact middleDerivativeBox019Cell035_valid
  · exact middleDerivativeBox019Cell036_valid
  · exact middleDerivativeBox019Cell037_valid
  · exact middleDerivativeBox019Cell038_valid
  · exact middleDerivativeBox019Cell039_valid
theorem middleDerivativeBox019_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox019Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox019Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox019_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox019Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox019Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox019_partial_bounds {t a : ℝ} (htl : ((869/1000) : ℝ) ≤ t) (htu : t ≤ ((87/100) : ℝ))
    (hal : ((326696280934847/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((327233151846847/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters019 middleDerivativeParameters019_valid middleDerivativeBox019Cells (1/20) middleDerivativeBox019Cells_valid middleDerivativeBox019_upperA middleDerivativeBox019_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox019_derivative {t : ℝ} (htl : ((869/1000) : ℝ) ≤ t) (htu : t ≤ ((87/100) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox019_enclosure htl htu
  have hp := middleDerivativeParameters019.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters019_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox019_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((87/100) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox019_derivative
