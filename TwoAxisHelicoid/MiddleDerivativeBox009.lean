import TwoAxisHelicoid.MiddleVerticalBox009
import TwoAxisHelicoid.MiddleDerivativeBox009Cell000
import TwoAxisHelicoid.MiddleDerivativeBox009Cell001
import TwoAxisHelicoid.MiddleDerivativeBox009Cell002
import TwoAxisHelicoid.MiddleDerivativeBox009Cell003
import TwoAxisHelicoid.MiddleDerivativeBox009Cell004
import TwoAxisHelicoid.MiddleDerivativeBox009Cell005
import TwoAxisHelicoid.MiddleDerivativeBox009Cell006
import TwoAxisHelicoid.MiddleDerivativeBox009Cell007
import TwoAxisHelicoid.MiddleDerivativeBox009Cell008
import TwoAxisHelicoid.MiddleDerivativeBox009Cell009
import TwoAxisHelicoid.MiddleDerivativeBox009Cell010
import TwoAxisHelicoid.MiddleDerivativeBox009Cell011
import TwoAxisHelicoid.MiddleDerivativeBox009Cell012
import TwoAxisHelicoid.MiddleDerivativeBox009Cell013
import TwoAxisHelicoid.MiddleDerivativeBox009Cell014
import TwoAxisHelicoid.MiddleDerivativeBox009Cell015
import TwoAxisHelicoid.MiddleDerivativeBox009Cell016
import TwoAxisHelicoid.MiddleDerivativeBox009Cell017
import TwoAxisHelicoid.MiddleDerivativeBox009Cell018
import TwoAxisHelicoid.MiddleDerivativeBox009Cell019
import TwoAxisHelicoid.MiddleDerivativeBox009Cell020
import TwoAxisHelicoid.MiddleDerivativeBox009Cell021
import TwoAxisHelicoid.MiddleDerivativeBox009Cell022
import TwoAxisHelicoid.MiddleDerivativeBox009Cell023
import TwoAxisHelicoid.MiddleDerivativeBox009Cell024
import TwoAxisHelicoid.MiddleDerivativeBox009Cell025
import TwoAxisHelicoid.MiddleDerivativeBox009Cell026
import TwoAxisHelicoid.MiddleDerivativeBox009Cell027
import TwoAxisHelicoid.MiddleDerivativeBox009Cell028
import TwoAxisHelicoid.MiddleDerivativeBox009Cell029
import TwoAxisHelicoid.MiddleDerivativeBox009Cell030
import TwoAxisHelicoid.MiddleDerivativeBox009Cell031
import TwoAxisHelicoid.MiddleDerivativeBox009Cell032
import TwoAxisHelicoid.MiddleDerivativeBox009Cell033
import TwoAxisHelicoid.MiddleDerivativeBox009Cell034
import TwoAxisHelicoid.MiddleDerivativeBox009Cell035
import TwoAxisHelicoid.MiddleDerivativeBox009Cell036
import TwoAxisHelicoid.MiddleDerivativeBox009Cell037
import TwoAxisHelicoid.MiddleDerivativeBox009Cell038
import TwoAxisHelicoid.MiddleDerivativeBox009Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox009Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox009Cell000,middleDerivativeBox009Cell001,middleDerivativeBox009Cell002,middleDerivativeBox009Cell003,middleDerivativeBox009Cell004,middleDerivativeBox009Cell005,middleDerivativeBox009Cell006,middleDerivativeBox009Cell007,middleDerivativeBox009Cell008,middleDerivativeBox009Cell009,middleDerivativeBox009Cell010,middleDerivativeBox009Cell011,middleDerivativeBox009Cell012,middleDerivativeBox009Cell013,middleDerivativeBox009Cell014,middleDerivativeBox009Cell015,middleDerivativeBox009Cell016,middleDerivativeBox009Cell017,middleDerivativeBox009Cell018,middleDerivativeBox009Cell019,middleDerivativeBox009Cell020,middleDerivativeBox009Cell021,middleDerivativeBox009Cell022,middleDerivativeBox009Cell023,middleDerivativeBox009Cell024,middleDerivativeBox009Cell025,middleDerivativeBox009Cell026,middleDerivativeBox009Cell027,middleDerivativeBox009Cell028,middleDerivativeBox009Cell029,middleDerivativeBox009Cell030,middleDerivativeBox009Cell031,middleDerivativeBox009Cell032,middleDerivativeBox009Cell033,middleDerivativeBox009Cell034,middleDerivativeBox009Cell035,middleDerivativeBox009Cell036,middleDerivativeBox009Cell037,middleDerivativeBox009Cell038,middleDerivativeBox009Cell039]
theorem middleDerivativeBox009Cells_valid : ∀ i : Fin 40, (middleDerivativeBox009Cells i).Valid middleRangeSetup middleDerivativeParameters009 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox009Cell000_valid
  · exact middleDerivativeBox009Cell001_valid
  · exact middleDerivativeBox009Cell002_valid
  · exact middleDerivativeBox009Cell003_valid
  · exact middleDerivativeBox009Cell004_valid
  · exact middleDerivativeBox009Cell005_valid
  · exact middleDerivativeBox009Cell006_valid
  · exact middleDerivativeBox009Cell007_valid
  · exact middleDerivativeBox009Cell008_valid
  · exact middleDerivativeBox009Cell009_valid
  · exact middleDerivativeBox009Cell010_valid
  · exact middleDerivativeBox009Cell011_valid
  · exact middleDerivativeBox009Cell012_valid
  · exact middleDerivativeBox009Cell013_valid
  · exact middleDerivativeBox009Cell014_valid
  · exact middleDerivativeBox009Cell015_valid
  · exact middleDerivativeBox009Cell016_valid
  · exact middleDerivativeBox009Cell017_valid
  · exact middleDerivativeBox009Cell018_valid
  · exact middleDerivativeBox009Cell019_valid
  · exact middleDerivativeBox009Cell020_valid
  · exact middleDerivativeBox009Cell021_valid
  · exact middleDerivativeBox009Cell022_valid
  · exact middleDerivativeBox009Cell023_valid
  · exact middleDerivativeBox009Cell024_valid
  · exact middleDerivativeBox009Cell025_valid
  · exact middleDerivativeBox009Cell026_valid
  · exact middleDerivativeBox009Cell027_valid
  · exact middleDerivativeBox009Cell028_valid
  · exact middleDerivativeBox009Cell029_valid
  · exact middleDerivativeBox009Cell030_valid
  · exact middleDerivativeBox009Cell031_valid
  · exact middleDerivativeBox009Cell032_valid
  · exact middleDerivativeBox009Cell033_valid
  · exact middleDerivativeBox009Cell034_valid
  · exact middleDerivativeBox009Cell035_valid
  · exact middleDerivativeBox009Cell036_valid
  · exact middleDerivativeBox009Cell037_valid
  · exact middleDerivativeBox009Cell038_valid
  · exact middleDerivativeBox009Cell039_valid
theorem middleDerivativeBox009_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox009Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox009Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox009_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox009Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox009Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox009_partial_bounds {t a : ℝ} (htl : ((859/1000) : ℝ) ≤ t) (htu : t ≤ ((43/50) : ℝ))
    (hal : ((974782989612433/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((976393602348433/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters009 middleDerivativeParameters009_valid middleDerivativeBox009Cells (1/20) middleDerivativeBox009Cells_valid middleDerivativeBox009_upperA middleDerivativeBox009_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox009_derivative {t : ℝ} (htl : ((859/1000) : ℝ) ≤ t) (htu : t ≤ ((43/50) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox009_enclosure htl htu
  have hp := middleDerivativeParameters009.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters009_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox009_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((43/50) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox009_derivative
