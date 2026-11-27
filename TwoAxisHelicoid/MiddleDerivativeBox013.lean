import TwoAxisHelicoid.MiddleVerticalBox013
import TwoAxisHelicoid.MiddleDerivativeBox013Cell000
import TwoAxisHelicoid.MiddleDerivativeBox013Cell001
import TwoAxisHelicoid.MiddleDerivativeBox013Cell002
import TwoAxisHelicoid.MiddleDerivativeBox013Cell003
import TwoAxisHelicoid.MiddleDerivativeBox013Cell004
import TwoAxisHelicoid.MiddleDerivativeBox013Cell005
import TwoAxisHelicoid.MiddleDerivativeBox013Cell006
import TwoAxisHelicoid.MiddleDerivativeBox013Cell007
import TwoAxisHelicoid.MiddleDerivativeBox013Cell008
import TwoAxisHelicoid.MiddleDerivativeBox013Cell009
import TwoAxisHelicoid.MiddleDerivativeBox013Cell010
import TwoAxisHelicoid.MiddleDerivativeBox013Cell011
import TwoAxisHelicoid.MiddleDerivativeBox013Cell012
import TwoAxisHelicoid.MiddleDerivativeBox013Cell013
import TwoAxisHelicoid.MiddleDerivativeBox013Cell014
import TwoAxisHelicoid.MiddleDerivativeBox013Cell015
import TwoAxisHelicoid.MiddleDerivativeBox013Cell016
import TwoAxisHelicoid.MiddleDerivativeBox013Cell017
import TwoAxisHelicoid.MiddleDerivativeBox013Cell018
import TwoAxisHelicoid.MiddleDerivativeBox013Cell019
import TwoAxisHelicoid.MiddleDerivativeBox013Cell020
import TwoAxisHelicoid.MiddleDerivativeBox013Cell021
import TwoAxisHelicoid.MiddleDerivativeBox013Cell022
import TwoAxisHelicoid.MiddleDerivativeBox013Cell023
import TwoAxisHelicoid.MiddleDerivativeBox013Cell024
import TwoAxisHelicoid.MiddleDerivativeBox013Cell025
import TwoAxisHelicoid.MiddleDerivativeBox013Cell026
import TwoAxisHelicoid.MiddleDerivativeBox013Cell027
import TwoAxisHelicoid.MiddleDerivativeBox013Cell028
import TwoAxisHelicoid.MiddleDerivativeBox013Cell029
import TwoAxisHelicoid.MiddleDerivativeBox013Cell030
import TwoAxisHelicoid.MiddleDerivativeBox013Cell031
import TwoAxisHelicoid.MiddleDerivativeBox013Cell032
import TwoAxisHelicoid.MiddleDerivativeBox013Cell033
import TwoAxisHelicoid.MiddleDerivativeBox013Cell034
import TwoAxisHelicoid.MiddleDerivativeBox013Cell035
import TwoAxisHelicoid.MiddleDerivativeBox013Cell036
import TwoAxisHelicoid.MiddleDerivativeBox013Cell037
import TwoAxisHelicoid.MiddleDerivativeBox013Cell038
import TwoAxisHelicoid.MiddleDerivativeBox013Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox013Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox013Cell000,middleDerivativeBox013Cell001,middleDerivativeBox013Cell002,middleDerivativeBox013Cell003,middleDerivativeBox013Cell004,middleDerivativeBox013Cell005,middleDerivativeBox013Cell006,middleDerivativeBox013Cell007,middleDerivativeBox013Cell008,middleDerivativeBox013Cell009,middleDerivativeBox013Cell010,middleDerivativeBox013Cell011,middleDerivativeBox013Cell012,middleDerivativeBox013Cell013,middleDerivativeBox013Cell014,middleDerivativeBox013Cell015,middleDerivativeBox013Cell016,middleDerivativeBox013Cell017,middleDerivativeBox013Cell018,middleDerivativeBox013Cell019,middleDerivativeBox013Cell020,middleDerivativeBox013Cell021,middleDerivativeBox013Cell022,middleDerivativeBox013Cell023,middleDerivativeBox013Cell024,middleDerivativeBox013Cell025,middleDerivativeBox013Cell026,middleDerivativeBox013Cell027,middleDerivativeBox013Cell028,middleDerivativeBox013Cell029,middleDerivativeBox013Cell030,middleDerivativeBox013Cell031,middleDerivativeBox013Cell032,middleDerivativeBox013Cell033,middleDerivativeBox013Cell034,middleDerivativeBox013Cell035,middleDerivativeBox013Cell036,middleDerivativeBox013Cell037,middleDerivativeBox013Cell038,middleDerivativeBox013Cell039]
theorem middleDerivativeBox013Cells_valid : ∀ i : Fin 40, (middleDerivativeBox013Cells i).Valid middleRangeSetup middleDerivativeParameters013 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox013Cell000_valid
  · exact middleDerivativeBox013Cell001_valid
  · exact middleDerivativeBox013Cell002_valid
  · exact middleDerivativeBox013Cell003_valid
  · exact middleDerivativeBox013Cell004_valid
  · exact middleDerivativeBox013Cell005_valid
  · exact middleDerivativeBox013Cell006_valid
  · exact middleDerivativeBox013Cell007_valid
  · exact middleDerivativeBox013Cell008_valid
  · exact middleDerivativeBox013Cell009_valid
  · exact middleDerivativeBox013Cell010_valid
  · exact middleDerivativeBox013Cell011_valid
  · exact middleDerivativeBox013Cell012_valid
  · exact middleDerivativeBox013Cell013_valid
  · exact middleDerivativeBox013Cell014_valid
  · exact middleDerivativeBox013Cell015_valid
  · exact middleDerivativeBox013Cell016_valid
  · exact middleDerivativeBox013Cell017_valid
  · exact middleDerivativeBox013Cell018_valid
  · exact middleDerivativeBox013Cell019_valid
  · exact middleDerivativeBox013Cell020_valid
  · exact middleDerivativeBox013Cell021_valid
  · exact middleDerivativeBox013Cell022_valid
  · exact middleDerivativeBox013Cell023_valid
  · exact middleDerivativeBox013Cell024_valid
  · exact middleDerivativeBox013Cell025_valid
  · exact middleDerivativeBox013Cell026_valid
  · exact middleDerivativeBox013Cell027_valid
  · exact middleDerivativeBox013Cell028_valid
  · exact middleDerivativeBox013Cell029_valid
  · exact middleDerivativeBox013Cell030_valid
  · exact middleDerivativeBox013Cell031_valid
  · exact middleDerivativeBox013Cell032_valid
  · exact middleDerivativeBox013Cell033_valid
  · exact middleDerivativeBox013Cell034_valid
  · exact middleDerivativeBox013Cell035_valid
  · exact middleDerivativeBox013Cell036_valid
  · exact middleDerivativeBox013Cell037_valid
  · exact middleDerivativeBox013Cell038_valid
  · exact middleDerivativeBox013Cell039_valid
theorem middleDerivativeBox013_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox013Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox013Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox013_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox013Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox013Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox013_partial_bounds {t a : ℝ} (htl : ((863/1000) : ℝ) ≤ t) (htu : t ≤ ((108/125) : ℝ))
    (hal : ((325631202149053/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((326168073061053/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters013 middleDerivativeParameters013_valid middleDerivativeBox013Cells (1/20) middleDerivativeBox013Cells_valid middleDerivativeBox013_upperA middleDerivativeBox013_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox013_derivative {t : ℝ} (htl : ((863/1000) : ℝ) ≤ t) (htu : t ≤ ((108/125) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox013_enclosure htl htu
  have hp := middleDerivativeParameters013.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters013_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox013_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((108/125) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox013_derivative
