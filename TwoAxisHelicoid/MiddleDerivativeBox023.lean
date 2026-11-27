import TwoAxisHelicoid.MiddleVerticalBox023
import TwoAxisHelicoid.MiddleDerivativeBox023Cell000
import TwoAxisHelicoid.MiddleDerivativeBox023Cell001
import TwoAxisHelicoid.MiddleDerivativeBox023Cell002
import TwoAxisHelicoid.MiddleDerivativeBox023Cell003
import TwoAxisHelicoid.MiddleDerivativeBox023Cell004
import TwoAxisHelicoid.MiddleDerivativeBox023Cell005
import TwoAxisHelicoid.MiddleDerivativeBox023Cell006
import TwoAxisHelicoid.MiddleDerivativeBox023Cell007
import TwoAxisHelicoid.MiddleDerivativeBox023Cell008
import TwoAxisHelicoid.MiddleDerivativeBox023Cell009
import TwoAxisHelicoid.MiddleDerivativeBox023Cell010
import TwoAxisHelicoid.MiddleDerivativeBox023Cell011
import TwoAxisHelicoid.MiddleDerivativeBox023Cell012
import TwoAxisHelicoid.MiddleDerivativeBox023Cell013
import TwoAxisHelicoid.MiddleDerivativeBox023Cell014
import TwoAxisHelicoid.MiddleDerivativeBox023Cell015
import TwoAxisHelicoid.MiddleDerivativeBox023Cell016
import TwoAxisHelicoid.MiddleDerivativeBox023Cell017
import TwoAxisHelicoid.MiddleDerivativeBox023Cell018
import TwoAxisHelicoid.MiddleDerivativeBox023Cell019
import TwoAxisHelicoid.MiddleDerivativeBox023Cell020
import TwoAxisHelicoid.MiddleDerivativeBox023Cell021
import TwoAxisHelicoid.MiddleDerivativeBox023Cell022
import TwoAxisHelicoid.MiddleDerivativeBox023Cell023
import TwoAxisHelicoid.MiddleDerivativeBox023Cell024
import TwoAxisHelicoid.MiddleDerivativeBox023Cell025
import TwoAxisHelicoid.MiddleDerivativeBox023Cell026
import TwoAxisHelicoid.MiddleDerivativeBox023Cell027
import TwoAxisHelicoid.MiddleDerivativeBox023Cell028
import TwoAxisHelicoid.MiddleDerivativeBox023Cell029
import TwoAxisHelicoid.MiddleDerivativeBox023Cell030
import TwoAxisHelicoid.MiddleDerivativeBox023Cell031
import TwoAxisHelicoid.MiddleDerivativeBox023Cell032
import TwoAxisHelicoid.MiddleDerivativeBox023Cell033
import TwoAxisHelicoid.MiddleDerivativeBox023Cell034
import TwoAxisHelicoid.MiddleDerivativeBox023Cell035
import TwoAxisHelicoid.MiddleDerivativeBox023Cell036
import TwoAxisHelicoid.MiddleDerivativeBox023Cell037
import TwoAxisHelicoid.MiddleDerivativeBox023Cell038
import TwoAxisHelicoid.MiddleDerivativeBox023Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox023Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox023Cell000,middleDerivativeBox023Cell001,middleDerivativeBox023Cell002,middleDerivativeBox023Cell003,middleDerivativeBox023Cell004,middleDerivativeBox023Cell005,middleDerivativeBox023Cell006,middleDerivativeBox023Cell007,middleDerivativeBox023Cell008,middleDerivativeBox023Cell009,middleDerivativeBox023Cell010,middleDerivativeBox023Cell011,middleDerivativeBox023Cell012,middleDerivativeBox023Cell013,middleDerivativeBox023Cell014,middleDerivativeBox023Cell015,middleDerivativeBox023Cell016,middleDerivativeBox023Cell017,middleDerivativeBox023Cell018,middleDerivativeBox023Cell019,middleDerivativeBox023Cell020,middleDerivativeBox023Cell021,middleDerivativeBox023Cell022,middleDerivativeBox023Cell023,middleDerivativeBox023Cell024,middleDerivativeBox023Cell025,middleDerivativeBox023Cell026,middleDerivativeBox023Cell027,middleDerivativeBox023Cell028,middleDerivativeBox023Cell029,middleDerivativeBox023Cell030,middleDerivativeBox023Cell031,middleDerivativeBox023Cell032,middleDerivativeBox023Cell033,middleDerivativeBox023Cell034,middleDerivativeBox023Cell035,middleDerivativeBox023Cell036,middleDerivativeBox023Cell037,middleDerivativeBox023Cell038,middleDerivativeBox023Cell039]
theorem middleDerivativeBox023Cells_valid : ∀ i : Fin 40, (middleDerivativeBox023Cells i).Valid middleRangeSetup middleDerivativeParameters023 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox023Cell000_valid
  · exact middleDerivativeBox023Cell001_valid
  · exact middleDerivativeBox023Cell002_valid
  · exact middleDerivativeBox023Cell003_valid
  · exact middleDerivativeBox023Cell004_valid
  · exact middleDerivativeBox023Cell005_valid
  · exact middleDerivativeBox023Cell006_valid
  · exact middleDerivativeBox023Cell007_valid
  · exact middleDerivativeBox023Cell008_valid
  · exact middleDerivativeBox023Cell009_valid
  · exact middleDerivativeBox023Cell010_valid
  · exact middleDerivativeBox023Cell011_valid
  · exact middleDerivativeBox023Cell012_valid
  · exact middleDerivativeBox023Cell013_valid
  · exact middleDerivativeBox023Cell014_valid
  · exact middleDerivativeBox023Cell015_valid
  · exact middleDerivativeBox023Cell016_valid
  · exact middleDerivativeBox023Cell017_valid
  · exact middleDerivativeBox023Cell018_valid
  · exact middleDerivativeBox023Cell019_valid
  · exact middleDerivativeBox023Cell020_valid
  · exact middleDerivativeBox023Cell021_valid
  · exact middleDerivativeBox023Cell022_valid
  · exact middleDerivativeBox023Cell023_valid
  · exact middleDerivativeBox023Cell024_valid
  · exact middleDerivativeBox023Cell025_valid
  · exact middleDerivativeBox023Cell026_valid
  · exact middleDerivativeBox023Cell027_valid
  · exact middleDerivativeBox023Cell028_valid
  · exact middleDerivativeBox023Cell029_valid
  · exact middleDerivativeBox023Cell030_valid
  · exact middleDerivativeBox023Cell031_valid
  · exact middleDerivativeBox023Cell032_valid
  · exact middleDerivativeBox023Cell033_valid
  · exact middleDerivativeBox023Cell034_valid
  · exact middleDerivativeBox023Cell035_valid
  · exact middleDerivativeBox023Cell036_valid
  · exact middleDerivativeBox023Cell037_valid
  · exact middleDerivativeBox023Cell038_valid
  · exact middleDerivativeBox023Cell039_valid
theorem middleDerivativeBox023_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox023Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox023Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox023_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox023Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox023Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox023_partial_bounds {t a : ℝ} (htl : ((873/1000) : ℝ) ≤ t) (htu : t ≤ ((437/500) : ℝ))
    (hal : ((327412870907139/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((327949741819139/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters023 middleDerivativeParameters023_valid middleDerivativeBox023Cells (1/20) middleDerivativeBox023Cells_valid middleDerivativeBox023_upperA middleDerivativeBox023_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox023_derivative {t : ℝ} (htl : ((873/1000) : ℝ) ≤ t) (htu : t ≤ ((437/500) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox023_enclosure htl htu
  have hp := middleDerivativeParameters023.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters023_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox023_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((437/500) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox023_derivative
