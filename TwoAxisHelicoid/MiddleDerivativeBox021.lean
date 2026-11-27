import TwoAxisHelicoid.MiddleVerticalBox021
import TwoAxisHelicoid.MiddleDerivativeBox021Cell000
import TwoAxisHelicoid.MiddleDerivativeBox021Cell001
import TwoAxisHelicoid.MiddleDerivativeBox021Cell002
import TwoAxisHelicoid.MiddleDerivativeBox021Cell003
import TwoAxisHelicoid.MiddleDerivativeBox021Cell004
import TwoAxisHelicoid.MiddleDerivativeBox021Cell005
import TwoAxisHelicoid.MiddleDerivativeBox021Cell006
import TwoAxisHelicoid.MiddleDerivativeBox021Cell007
import TwoAxisHelicoid.MiddleDerivativeBox021Cell008
import TwoAxisHelicoid.MiddleDerivativeBox021Cell009
import TwoAxisHelicoid.MiddleDerivativeBox021Cell010
import TwoAxisHelicoid.MiddleDerivativeBox021Cell011
import TwoAxisHelicoid.MiddleDerivativeBox021Cell012
import TwoAxisHelicoid.MiddleDerivativeBox021Cell013
import TwoAxisHelicoid.MiddleDerivativeBox021Cell014
import TwoAxisHelicoid.MiddleDerivativeBox021Cell015
import TwoAxisHelicoid.MiddleDerivativeBox021Cell016
import TwoAxisHelicoid.MiddleDerivativeBox021Cell017
import TwoAxisHelicoid.MiddleDerivativeBox021Cell018
import TwoAxisHelicoid.MiddleDerivativeBox021Cell019
import TwoAxisHelicoid.MiddleDerivativeBox021Cell020
import TwoAxisHelicoid.MiddleDerivativeBox021Cell021
import TwoAxisHelicoid.MiddleDerivativeBox021Cell022
import TwoAxisHelicoid.MiddleDerivativeBox021Cell023
import TwoAxisHelicoid.MiddleDerivativeBox021Cell024
import TwoAxisHelicoid.MiddleDerivativeBox021Cell025
import TwoAxisHelicoid.MiddleDerivativeBox021Cell026
import TwoAxisHelicoid.MiddleDerivativeBox021Cell027
import TwoAxisHelicoid.MiddleDerivativeBox021Cell028
import TwoAxisHelicoid.MiddleDerivativeBox021Cell029
import TwoAxisHelicoid.MiddleDerivativeBox021Cell030
import TwoAxisHelicoid.MiddleDerivativeBox021Cell031
import TwoAxisHelicoid.MiddleDerivativeBox021Cell032
import TwoAxisHelicoid.MiddleDerivativeBox021Cell033
import TwoAxisHelicoid.MiddleDerivativeBox021Cell034
import TwoAxisHelicoid.MiddleDerivativeBox021Cell035
import TwoAxisHelicoid.MiddleDerivativeBox021Cell036
import TwoAxisHelicoid.MiddleDerivativeBox021Cell037
import TwoAxisHelicoid.MiddleDerivativeBox021Cell038
import TwoAxisHelicoid.MiddleDerivativeBox021Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox021Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox021Cell000,middleDerivativeBox021Cell001,middleDerivativeBox021Cell002,middleDerivativeBox021Cell003,middleDerivativeBox021Cell004,middleDerivativeBox021Cell005,middleDerivativeBox021Cell006,middleDerivativeBox021Cell007,middleDerivativeBox021Cell008,middleDerivativeBox021Cell009,middleDerivativeBox021Cell010,middleDerivativeBox021Cell011,middleDerivativeBox021Cell012,middleDerivativeBox021Cell013,middleDerivativeBox021Cell014,middleDerivativeBox021Cell015,middleDerivativeBox021Cell016,middleDerivativeBox021Cell017,middleDerivativeBox021Cell018,middleDerivativeBox021Cell019,middleDerivativeBox021Cell020,middleDerivativeBox021Cell021,middleDerivativeBox021Cell022,middleDerivativeBox021Cell023,middleDerivativeBox021Cell024,middleDerivativeBox021Cell025,middleDerivativeBox021Cell026,middleDerivativeBox021Cell027,middleDerivativeBox021Cell028,middleDerivativeBox021Cell029,middleDerivativeBox021Cell030,middleDerivativeBox021Cell031,middleDerivativeBox021Cell032,middleDerivativeBox021Cell033,middleDerivativeBox021Cell034,middleDerivativeBox021Cell035,middleDerivativeBox021Cell036,middleDerivativeBox021Cell037,middleDerivativeBox021Cell038,middleDerivativeBox021Cell039]
theorem middleDerivativeBox021Cells_valid : ∀ i : Fin 40, (middleDerivativeBox021Cells i).Valid middleRangeSetup middleDerivativeParameters021 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox021Cell000_valid
  · exact middleDerivativeBox021Cell001_valid
  · exact middleDerivativeBox021Cell002_valid
  · exact middleDerivativeBox021Cell003_valid
  · exact middleDerivativeBox021Cell004_valid
  · exact middleDerivativeBox021Cell005_valid
  · exact middleDerivativeBox021Cell006_valid
  · exact middleDerivativeBox021Cell007_valid
  · exact middleDerivativeBox021Cell008_valid
  · exact middleDerivativeBox021Cell009_valid
  · exact middleDerivativeBox021Cell010_valid
  · exact middleDerivativeBox021Cell011_valid
  · exact middleDerivativeBox021Cell012_valid
  · exact middleDerivativeBox021Cell013_valid
  · exact middleDerivativeBox021Cell014_valid
  · exact middleDerivativeBox021Cell015_valid
  · exact middleDerivativeBox021Cell016_valid
  · exact middleDerivativeBox021Cell017_valid
  · exact middleDerivativeBox021Cell018_valid
  · exact middleDerivativeBox021Cell019_valid
  · exact middleDerivativeBox021Cell020_valid
  · exact middleDerivativeBox021Cell021_valid
  · exact middleDerivativeBox021Cell022_valid
  · exact middleDerivativeBox021Cell023_valid
  · exact middleDerivativeBox021Cell024_valid
  · exact middleDerivativeBox021Cell025_valid
  · exact middleDerivativeBox021Cell026_valid
  · exact middleDerivativeBox021Cell027_valid
  · exact middleDerivativeBox021Cell028_valid
  · exact middleDerivativeBox021Cell029_valid
  · exact middleDerivativeBox021Cell030_valid
  · exact middleDerivativeBox021Cell031_valid
  · exact middleDerivativeBox021Cell032_valid
  · exact middleDerivativeBox021Cell033_valid
  · exact middleDerivativeBox021Cell034_valid
  · exact middleDerivativeBox021Cell035_valid
  · exact middleDerivativeBox021Cell036_valid
  · exact middleDerivativeBox021Cell037_valid
  · exact middleDerivativeBox021Cell038_valid
  · exact middleDerivativeBox021Cell039_valid
theorem middleDerivativeBox021_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox021Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox021Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox021_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox021Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox021Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox021_partial_bounds {t a : ℝ} (htl : ((871/1000) : ℝ) ≤ t) (htu : t ≤ ((109/125) : ℝ))
    (hal : ((327053920769197/549755813888000) : ℝ) ≤ a) (hau : a ≤ ((327590791681197/549755813888000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters021 middleDerivativeParameters021_valid middleDerivativeBox021Cells (1/20) middleDerivativeBox021Cells_valid middleDerivativeBox021_upperA middleDerivativeBox021_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox021_derivative {t : ℝ} (htl : ((871/1000) : ℝ) ≤ t) (htu : t ≤ ((109/125) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox021_enclosure htl htu
  have hp := middleDerivativeParameters021.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters021_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox021_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((109/125) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox021_derivative
