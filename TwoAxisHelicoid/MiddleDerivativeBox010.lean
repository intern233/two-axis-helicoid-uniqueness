import TwoAxisHelicoid.MiddleVerticalBox010
import TwoAxisHelicoid.MiddleDerivativeBox010Cell000
import TwoAxisHelicoid.MiddleDerivativeBox010Cell001
import TwoAxisHelicoid.MiddleDerivativeBox010Cell002
import TwoAxisHelicoid.MiddleDerivativeBox010Cell003
import TwoAxisHelicoid.MiddleDerivativeBox010Cell004
import TwoAxisHelicoid.MiddleDerivativeBox010Cell005
import TwoAxisHelicoid.MiddleDerivativeBox010Cell006
import TwoAxisHelicoid.MiddleDerivativeBox010Cell007
import TwoAxisHelicoid.MiddleDerivativeBox010Cell008
import TwoAxisHelicoid.MiddleDerivativeBox010Cell009
import TwoAxisHelicoid.MiddleDerivativeBox010Cell010
import TwoAxisHelicoid.MiddleDerivativeBox010Cell011
import TwoAxisHelicoid.MiddleDerivativeBox010Cell012
import TwoAxisHelicoid.MiddleDerivativeBox010Cell013
import TwoAxisHelicoid.MiddleDerivativeBox010Cell014
import TwoAxisHelicoid.MiddleDerivativeBox010Cell015
import TwoAxisHelicoid.MiddleDerivativeBox010Cell016
import TwoAxisHelicoid.MiddleDerivativeBox010Cell017
import TwoAxisHelicoid.MiddleDerivativeBox010Cell018
import TwoAxisHelicoid.MiddleDerivativeBox010Cell019
import TwoAxisHelicoid.MiddleDerivativeBox010Cell020
import TwoAxisHelicoid.MiddleDerivativeBox010Cell021
import TwoAxisHelicoid.MiddleDerivativeBox010Cell022
import TwoAxisHelicoid.MiddleDerivativeBox010Cell023
import TwoAxisHelicoid.MiddleDerivativeBox010Cell024
import TwoAxisHelicoid.MiddleDerivativeBox010Cell025
import TwoAxisHelicoid.MiddleDerivativeBox010Cell026
import TwoAxisHelicoid.MiddleDerivativeBox010Cell027
import TwoAxisHelicoid.MiddleDerivativeBox010Cell028
import TwoAxisHelicoid.MiddleDerivativeBox010Cell029
import TwoAxisHelicoid.MiddleDerivativeBox010Cell030
import TwoAxisHelicoid.MiddleDerivativeBox010Cell031
import TwoAxisHelicoid.MiddleDerivativeBox010Cell032
import TwoAxisHelicoid.MiddleDerivativeBox010Cell033
import TwoAxisHelicoid.MiddleDerivativeBox010Cell034
import TwoAxisHelicoid.MiddleDerivativeBox010Cell035
import TwoAxisHelicoid.MiddleDerivativeBox010Cell036
import TwoAxisHelicoid.MiddleDerivativeBox010Cell037
import TwoAxisHelicoid.MiddleDerivativeBox010Cell038
import TwoAxisHelicoid.MiddleDerivativeBox010Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox010Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox010Cell000,middleDerivativeBox010Cell001,middleDerivativeBox010Cell002,middleDerivativeBox010Cell003,middleDerivativeBox010Cell004,middleDerivativeBox010Cell005,middleDerivativeBox010Cell006,middleDerivativeBox010Cell007,middleDerivativeBox010Cell008,middleDerivativeBox010Cell009,middleDerivativeBox010Cell010,middleDerivativeBox010Cell011,middleDerivativeBox010Cell012,middleDerivativeBox010Cell013,middleDerivativeBox010Cell014,middleDerivativeBox010Cell015,middleDerivativeBox010Cell016,middleDerivativeBox010Cell017,middleDerivativeBox010Cell018,middleDerivativeBox010Cell019,middleDerivativeBox010Cell020,middleDerivativeBox010Cell021,middleDerivativeBox010Cell022,middleDerivativeBox010Cell023,middleDerivativeBox010Cell024,middleDerivativeBox010Cell025,middleDerivativeBox010Cell026,middleDerivativeBox010Cell027,middleDerivativeBox010Cell028,middleDerivativeBox010Cell029,middleDerivativeBox010Cell030,middleDerivativeBox010Cell031,middleDerivativeBox010Cell032,middleDerivativeBox010Cell033,middleDerivativeBox010Cell034,middleDerivativeBox010Cell035,middleDerivativeBox010Cell036,middleDerivativeBox010Cell037,middleDerivativeBox010Cell038,middleDerivativeBox010Cell039]
theorem middleDerivativeBox010Cells_valid : ∀ i : Fin 40, (middleDerivativeBox010Cells i).Valid middleRangeSetup middleDerivativeParameters010 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox010Cell000_valid
  · exact middleDerivativeBox010Cell001_valid
  · exact middleDerivativeBox010Cell002_valid
  · exact middleDerivativeBox010Cell003_valid
  · exact middleDerivativeBox010Cell004_valid
  · exact middleDerivativeBox010Cell005_valid
  · exact middleDerivativeBox010Cell006_valid
  · exact middleDerivativeBox010Cell007_valid
  · exact middleDerivativeBox010Cell008_valid
  · exact middleDerivativeBox010Cell009_valid
  · exact middleDerivativeBox010Cell010_valid
  · exact middleDerivativeBox010Cell011_valid
  · exact middleDerivativeBox010Cell012_valid
  · exact middleDerivativeBox010Cell013_valid
  · exact middleDerivativeBox010Cell014_valid
  · exact middleDerivativeBox010Cell015_valid
  · exact middleDerivativeBox010Cell016_valid
  · exact middleDerivativeBox010Cell017_valid
  · exact middleDerivativeBox010Cell018_valid
  · exact middleDerivativeBox010Cell019_valid
  · exact middleDerivativeBox010Cell020_valid
  · exact middleDerivativeBox010Cell021_valid
  · exact middleDerivativeBox010Cell022_valid
  · exact middleDerivativeBox010Cell023_valid
  · exact middleDerivativeBox010Cell024_valid
  · exact middleDerivativeBox010Cell025_valid
  · exact middleDerivativeBox010Cell026_valid
  · exact middleDerivativeBox010Cell027_valid
  · exact middleDerivativeBox010Cell028_valid
  · exact middleDerivativeBox010Cell029_valid
  · exact middleDerivativeBox010Cell030_valid
  · exact middleDerivativeBox010Cell031_valid
  · exact middleDerivativeBox010Cell032_valid
  · exact middleDerivativeBox010Cell033_valid
  · exact middleDerivativeBox010Cell034_valid
  · exact middleDerivativeBox010Cell035_valid
  · exact middleDerivativeBox010Cell036_valid
  · exact middleDerivativeBox010Cell037_valid
  · exact middleDerivativeBox010Cell038_valid
  · exact middleDerivativeBox010Cell039_valid
theorem middleDerivativeBox010_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox010Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox010Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox010_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox010Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox010Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox010_partial_bounds {t a : ℝ} (htl : ((43/50) : ℝ) ≤ t) (htu : t ≤ ((861/1000) : ℝ))
    (hal : ((975309181602737/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((976919794338737/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters010 middleDerivativeParameters010_valid middleDerivativeBox010Cells (1/20) middleDerivativeBox010Cells_valid middleDerivativeBox010_upperA middleDerivativeBox010_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox010_derivative {t : ℝ} (htl : ((43/50) : ℝ) ≤ t) (htu : t ≤ ((861/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox010_enclosure htl htu
  have hp := middleDerivativeParameters010.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters010_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox010_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((861/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox010_derivative
