import TwoAxisHelicoid.MiddleVerticalBox008
import TwoAxisHelicoid.MiddleDerivativeBox008Cell000
import TwoAxisHelicoid.MiddleDerivativeBox008Cell001
import TwoAxisHelicoid.MiddleDerivativeBox008Cell002
import TwoAxisHelicoid.MiddleDerivativeBox008Cell003
import TwoAxisHelicoid.MiddleDerivativeBox008Cell004
import TwoAxisHelicoid.MiddleDerivativeBox008Cell005
import TwoAxisHelicoid.MiddleDerivativeBox008Cell006
import TwoAxisHelicoid.MiddleDerivativeBox008Cell007
import TwoAxisHelicoid.MiddleDerivativeBox008Cell008
import TwoAxisHelicoid.MiddleDerivativeBox008Cell009
import TwoAxisHelicoid.MiddleDerivativeBox008Cell010
import TwoAxisHelicoid.MiddleDerivativeBox008Cell011
import TwoAxisHelicoid.MiddleDerivativeBox008Cell012
import TwoAxisHelicoid.MiddleDerivativeBox008Cell013
import TwoAxisHelicoid.MiddleDerivativeBox008Cell014
import TwoAxisHelicoid.MiddleDerivativeBox008Cell015
import TwoAxisHelicoid.MiddleDerivativeBox008Cell016
import TwoAxisHelicoid.MiddleDerivativeBox008Cell017
import TwoAxisHelicoid.MiddleDerivativeBox008Cell018
import TwoAxisHelicoid.MiddleDerivativeBox008Cell019
import TwoAxisHelicoid.MiddleDerivativeBox008Cell020
import TwoAxisHelicoid.MiddleDerivativeBox008Cell021
import TwoAxisHelicoid.MiddleDerivativeBox008Cell022
import TwoAxisHelicoid.MiddleDerivativeBox008Cell023
import TwoAxisHelicoid.MiddleDerivativeBox008Cell024
import TwoAxisHelicoid.MiddleDerivativeBox008Cell025
import TwoAxisHelicoid.MiddleDerivativeBox008Cell026
import TwoAxisHelicoid.MiddleDerivativeBox008Cell027
import TwoAxisHelicoid.MiddleDerivativeBox008Cell028
import TwoAxisHelicoid.MiddleDerivativeBox008Cell029
import TwoAxisHelicoid.MiddleDerivativeBox008Cell030
import TwoAxisHelicoid.MiddleDerivativeBox008Cell031
import TwoAxisHelicoid.MiddleDerivativeBox008Cell032
import TwoAxisHelicoid.MiddleDerivativeBox008Cell033
import TwoAxisHelicoid.MiddleDerivativeBox008Cell034
import TwoAxisHelicoid.MiddleDerivativeBox008Cell035
import TwoAxisHelicoid.MiddleDerivativeBox008Cell036
import TwoAxisHelicoid.MiddleDerivativeBox008Cell037
import TwoAxisHelicoid.MiddleDerivativeBox008Cell038
import TwoAxisHelicoid.MiddleDerivativeBox008Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox008Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox008Cell000,middleDerivativeBox008Cell001,middleDerivativeBox008Cell002,middleDerivativeBox008Cell003,middleDerivativeBox008Cell004,middleDerivativeBox008Cell005,middleDerivativeBox008Cell006,middleDerivativeBox008Cell007,middleDerivativeBox008Cell008,middleDerivativeBox008Cell009,middleDerivativeBox008Cell010,middleDerivativeBox008Cell011,middleDerivativeBox008Cell012,middleDerivativeBox008Cell013,middleDerivativeBox008Cell014,middleDerivativeBox008Cell015,middleDerivativeBox008Cell016,middleDerivativeBox008Cell017,middleDerivativeBox008Cell018,middleDerivativeBox008Cell019,middleDerivativeBox008Cell020,middleDerivativeBox008Cell021,middleDerivativeBox008Cell022,middleDerivativeBox008Cell023,middleDerivativeBox008Cell024,middleDerivativeBox008Cell025,middleDerivativeBox008Cell026,middleDerivativeBox008Cell027,middleDerivativeBox008Cell028,middleDerivativeBox008Cell029,middleDerivativeBox008Cell030,middleDerivativeBox008Cell031,middleDerivativeBox008Cell032,middleDerivativeBox008Cell033,middleDerivativeBox008Cell034,middleDerivativeBox008Cell035,middleDerivativeBox008Cell036,middleDerivativeBox008Cell037,middleDerivativeBox008Cell038,middleDerivativeBox008Cell039]
theorem middleDerivativeBox008Cells_valid : ∀ i : Fin 40, (middleDerivativeBox008Cells i).Valid middleRangeSetup middleDerivativeParameters008 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox008Cell000_valid
  · exact middleDerivativeBox008Cell001_valid
  · exact middleDerivativeBox008Cell002_valid
  · exact middleDerivativeBox008Cell003_valid
  · exact middleDerivativeBox008Cell004_valid
  · exact middleDerivativeBox008Cell005_valid
  · exact middleDerivativeBox008Cell006_valid
  · exact middleDerivativeBox008Cell007_valid
  · exact middleDerivativeBox008Cell008_valid
  · exact middleDerivativeBox008Cell009_valid
  · exact middleDerivativeBox008Cell010_valid
  · exact middleDerivativeBox008Cell011_valid
  · exact middleDerivativeBox008Cell012_valid
  · exact middleDerivativeBox008Cell013_valid
  · exact middleDerivativeBox008Cell014_valid
  · exact middleDerivativeBox008Cell015_valid
  · exact middleDerivativeBox008Cell016_valid
  · exact middleDerivativeBox008Cell017_valid
  · exact middleDerivativeBox008Cell018_valid
  · exact middleDerivativeBox008Cell019_valid
  · exact middleDerivativeBox008Cell020_valid
  · exact middleDerivativeBox008Cell021_valid
  · exact middleDerivativeBox008Cell022_valid
  · exact middleDerivativeBox008Cell023_valid
  · exact middleDerivativeBox008Cell024_valid
  · exact middleDerivativeBox008Cell025_valid
  · exact middleDerivativeBox008Cell026_valid
  · exact middleDerivativeBox008Cell027_valid
  · exact middleDerivativeBox008Cell028_valid
  · exact middleDerivativeBox008Cell029_valid
  · exact middleDerivativeBox008Cell030_valid
  · exact middleDerivativeBox008Cell031_valid
  · exact middleDerivativeBox008Cell032_valid
  · exact middleDerivativeBox008Cell033_valid
  · exact middleDerivativeBox008Cell034_valid
  · exact middleDerivativeBox008Cell035_valid
  · exact middleDerivativeBox008Cell036_valid
  · exact middleDerivativeBox008Cell037_valid
  · exact middleDerivativeBox008Cell038_valid
  · exact middleDerivativeBox008Cell039_valid
theorem middleDerivativeBox008_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox008Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox008Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox008_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox008Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox008Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox008_partial_bounds {t a : ℝ} (htl : ((429/500) : ℝ) ≤ t) (htu : t ≤ ((859/1000) : ℝ))
    (hal : ((324752590410507/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((325289461322507/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters008 middleDerivativeParameters008_valid middleDerivativeBox008Cells (1/20) middleDerivativeBox008Cells_valid middleDerivativeBox008_upperA middleDerivativeBox008_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox008_derivative {t : ℝ} (htl : ((429/500) : ℝ) ≤ t) (htu : t ≤ ((859/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox008_enclosure htl htu
  have hp := middleDerivativeParameters008.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters008_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox008_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((859/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox008_derivative
