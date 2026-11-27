import TwoAxisHelicoid.MiddleVerticalBox007
import TwoAxisHelicoid.MiddleDerivativeBox007Cell000
import TwoAxisHelicoid.MiddleDerivativeBox007Cell001
import TwoAxisHelicoid.MiddleDerivativeBox007Cell002
import TwoAxisHelicoid.MiddleDerivativeBox007Cell003
import TwoAxisHelicoid.MiddleDerivativeBox007Cell004
import TwoAxisHelicoid.MiddleDerivativeBox007Cell005
import TwoAxisHelicoid.MiddleDerivativeBox007Cell006
import TwoAxisHelicoid.MiddleDerivativeBox007Cell007
import TwoAxisHelicoid.MiddleDerivativeBox007Cell008
import TwoAxisHelicoid.MiddleDerivativeBox007Cell009
import TwoAxisHelicoid.MiddleDerivativeBox007Cell010
import TwoAxisHelicoid.MiddleDerivativeBox007Cell011
import TwoAxisHelicoid.MiddleDerivativeBox007Cell012
import TwoAxisHelicoid.MiddleDerivativeBox007Cell013
import TwoAxisHelicoid.MiddleDerivativeBox007Cell014
import TwoAxisHelicoid.MiddleDerivativeBox007Cell015
import TwoAxisHelicoid.MiddleDerivativeBox007Cell016
import TwoAxisHelicoid.MiddleDerivativeBox007Cell017
import TwoAxisHelicoid.MiddleDerivativeBox007Cell018
import TwoAxisHelicoid.MiddleDerivativeBox007Cell019
import TwoAxisHelicoid.MiddleDerivativeBox007Cell020
import TwoAxisHelicoid.MiddleDerivativeBox007Cell021
import TwoAxisHelicoid.MiddleDerivativeBox007Cell022
import TwoAxisHelicoid.MiddleDerivativeBox007Cell023
import TwoAxisHelicoid.MiddleDerivativeBox007Cell024
import TwoAxisHelicoid.MiddleDerivativeBox007Cell025
import TwoAxisHelicoid.MiddleDerivativeBox007Cell026
import TwoAxisHelicoid.MiddleDerivativeBox007Cell027
import TwoAxisHelicoid.MiddleDerivativeBox007Cell028
import TwoAxisHelicoid.MiddleDerivativeBox007Cell029
import TwoAxisHelicoid.MiddleDerivativeBox007Cell030
import TwoAxisHelicoid.MiddleDerivativeBox007Cell031
import TwoAxisHelicoid.MiddleDerivativeBox007Cell032
import TwoAxisHelicoid.MiddleDerivativeBox007Cell033
import TwoAxisHelicoid.MiddleDerivativeBox007Cell034
import TwoAxisHelicoid.MiddleDerivativeBox007Cell035
import TwoAxisHelicoid.MiddleDerivativeBox007Cell036
import TwoAxisHelicoid.MiddleDerivativeBox007Cell037
import TwoAxisHelicoid.MiddleDerivativeBox007Cell038
import TwoAxisHelicoid.MiddleDerivativeBox007Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox007Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox007Cell000,middleDerivativeBox007Cell001,middleDerivativeBox007Cell002,middleDerivativeBox007Cell003,middleDerivativeBox007Cell004,middleDerivativeBox007Cell005,middleDerivativeBox007Cell006,middleDerivativeBox007Cell007,middleDerivativeBox007Cell008,middleDerivativeBox007Cell009,middleDerivativeBox007Cell010,middleDerivativeBox007Cell011,middleDerivativeBox007Cell012,middleDerivativeBox007Cell013,middleDerivativeBox007Cell014,middleDerivativeBox007Cell015,middleDerivativeBox007Cell016,middleDerivativeBox007Cell017,middleDerivativeBox007Cell018,middleDerivativeBox007Cell019,middleDerivativeBox007Cell020,middleDerivativeBox007Cell021,middleDerivativeBox007Cell022,middleDerivativeBox007Cell023,middleDerivativeBox007Cell024,middleDerivativeBox007Cell025,middleDerivativeBox007Cell026,middleDerivativeBox007Cell027,middleDerivativeBox007Cell028,middleDerivativeBox007Cell029,middleDerivativeBox007Cell030,middleDerivativeBox007Cell031,middleDerivativeBox007Cell032,middleDerivativeBox007Cell033,middleDerivativeBox007Cell034,middleDerivativeBox007Cell035,middleDerivativeBox007Cell036,middleDerivativeBox007Cell037,middleDerivativeBox007Cell038,middleDerivativeBox007Cell039]
theorem middleDerivativeBox007Cells_valid : ∀ i : Fin 40, (middleDerivativeBox007Cells i).Valid middleRangeSetup middleDerivativeParameters007 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox007Cell000_valid
  · exact middleDerivativeBox007Cell001_valid
  · exact middleDerivativeBox007Cell002_valid
  · exact middleDerivativeBox007Cell003_valid
  · exact middleDerivativeBox007Cell004_valid
  · exact middleDerivativeBox007Cell005_valid
  · exact middleDerivativeBox007Cell006_valid
  · exact middleDerivativeBox007Cell007_valid
  · exact middleDerivativeBox007Cell008_valid
  · exact middleDerivativeBox007Cell009_valid
  · exact middleDerivativeBox007Cell010_valid
  · exact middleDerivativeBox007Cell011_valid
  · exact middleDerivativeBox007Cell012_valid
  · exact middleDerivativeBox007Cell013_valid
  · exact middleDerivativeBox007Cell014_valid
  · exact middleDerivativeBox007Cell015_valid
  · exact middleDerivativeBox007Cell016_valid
  · exact middleDerivativeBox007Cell017_valid
  · exact middleDerivativeBox007Cell018_valid
  · exact middleDerivativeBox007Cell019_valid
  · exact middleDerivativeBox007Cell020_valid
  · exact middleDerivativeBox007Cell021_valid
  · exact middleDerivativeBox007Cell022_valid
  · exact middleDerivativeBox007Cell023_valid
  · exact middleDerivativeBox007Cell024_valid
  · exact middleDerivativeBox007Cell025_valid
  · exact middleDerivativeBox007Cell026_valid
  · exact middleDerivativeBox007Cell027_valid
  · exact middleDerivativeBox007Cell028_valid
  · exact middleDerivativeBox007Cell029_valid
  · exact middleDerivativeBox007Cell030_valid
  · exact middleDerivativeBox007Cell031_valid
  · exact middleDerivativeBox007Cell032_valid
  · exact middleDerivativeBox007Cell033_valid
  · exact middleDerivativeBox007Cell034_valid
  · exact middleDerivativeBox007Cell035_valid
  · exact middleDerivativeBox007Cell036_valid
  · exact middleDerivativeBox007Cell037_valid
  · exact middleDerivativeBox007Cell038_valid
  · exact middleDerivativeBox007Cell039_valid
theorem middleDerivativeBox007_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox007Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox007Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox007_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox007Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox007Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox007_partial_bounds {t a : ℝ} (htl : ((857/1000) : ℝ) ≤ t) (htu : t ≤ ((429/500) : ℝ))
    (hal : ((324577841919019/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((325114712831019/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters007 middleDerivativeParameters007_valid middleDerivativeBox007Cells (1/20) middleDerivativeBox007Cells_valid middleDerivativeBox007_upperA middleDerivativeBox007_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox007_derivative {t : ℝ} (htl : ((857/1000) : ℝ) ≤ t) (htu : t ≤ ((429/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox007_enclosure htl htu
  have hp := middleDerivativeParameters007.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters007_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox007_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((429/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox007_derivative
