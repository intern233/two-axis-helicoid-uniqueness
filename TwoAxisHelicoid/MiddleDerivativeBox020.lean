import TwoAxisHelicoid.MiddleVerticalBox020
import TwoAxisHelicoid.MiddleDerivativeBox020Cell000
import TwoAxisHelicoid.MiddleDerivativeBox020Cell001
import TwoAxisHelicoid.MiddleDerivativeBox020Cell002
import TwoAxisHelicoid.MiddleDerivativeBox020Cell003
import TwoAxisHelicoid.MiddleDerivativeBox020Cell004
import TwoAxisHelicoid.MiddleDerivativeBox020Cell005
import TwoAxisHelicoid.MiddleDerivativeBox020Cell006
import TwoAxisHelicoid.MiddleDerivativeBox020Cell007
import TwoAxisHelicoid.MiddleDerivativeBox020Cell008
import TwoAxisHelicoid.MiddleDerivativeBox020Cell009
import TwoAxisHelicoid.MiddleDerivativeBox020Cell010
import TwoAxisHelicoid.MiddleDerivativeBox020Cell011
import TwoAxisHelicoid.MiddleDerivativeBox020Cell012
import TwoAxisHelicoid.MiddleDerivativeBox020Cell013
import TwoAxisHelicoid.MiddleDerivativeBox020Cell014
import TwoAxisHelicoid.MiddleDerivativeBox020Cell015
import TwoAxisHelicoid.MiddleDerivativeBox020Cell016
import TwoAxisHelicoid.MiddleDerivativeBox020Cell017
import TwoAxisHelicoid.MiddleDerivativeBox020Cell018
import TwoAxisHelicoid.MiddleDerivativeBox020Cell019
import TwoAxisHelicoid.MiddleDerivativeBox020Cell020
import TwoAxisHelicoid.MiddleDerivativeBox020Cell021
import TwoAxisHelicoid.MiddleDerivativeBox020Cell022
import TwoAxisHelicoid.MiddleDerivativeBox020Cell023
import TwoAxisHelicoid.MiddleDerivativeBox020Cell024
import TwoAxisHelicoid.MiddleDerivativeBox020Cell025
import TwoAxisHelicoid.MiddleDerivativeBox020Cell026
import TwoAxisHelicoid.MiddleDerivativeBox020Cell027
import TwoAxisHelicoid.MiddleDerivativeBox020Cell028
import TwoAxisHelicoid.MiddleDerivativeBox020Cell029
import TwoAxisHelicoid.MiddleDerivativeBox020Cell030
import TwoAxisHelicoid.MiddleDerivativeBox020Cell031
import TwoAxisHelicoid.MiddleDerivativeBox020Cell032
import TwoAxisHelicoid.MiddleDerivativeBox020Cell033
import TwoAxisHelicoid.MiddleDerivativeBox020Cell034
import TwoAxisHelicoid.MiddleDerivativeBox020Cell035
import TwoAxisHelicoid.MiddleDerivativeBox020Cell036
import TwoAxisHelicoid.MiddleDerivativeBox020Cell037
import TwoAxisHelicoid.MiddleDerivativeBox020Cell038
import TwoAxisHelicoid.MiddleDerivativeBox020Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox020Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox020Cell000,middleDerivativeBox020Cell001,middleDerivativeBox020Cell002,middleDerivativeBox020Cell003,middleDerivativeBox020Cell004,middleDerivativeBox020Cell005,middleDerivativeBox020Cell006,middleDerivativeBox020Cell007,middleDerivativeBox020Cell008,middleDerivativeBox020Cell009,middleDerivativeBox020Cell010,middleDerivativeBox020Cell011,middleDerivativeBox020Cell012,middleDerivativeBox020Cell013,middleDerivativeBox020Cell014,middleDerivativeBox020Cell015,middleDerivativeBox020Cell016,middleDerivativeBox020Cell017,middleDerivativeBox020Cell018,middleDerivativeBox020Cell019,middleDerivativeBox020Cell020,middleDerivativeBox020Cell021,middleDerivativeBox020Cell022,middleDerivativeBox020Cell023,middleDerivativeBox020Cell024,middleDerivativeBox020Cell025,middleDerivativeBox020Cell026,middleDerivativeBox020Cell027,middleDerivativeBox020Cell028,middleDerivativeBox020Cell029,middleDerivativeBox020Cell030,middleDerivativeBox020Cell031,middleDerivativeBox020Cell032,middleDerivativeBox020Cell033,middleDerivativeBox020Cell034,middleDerivativeBox020Cell035,middleDerivativeBox020Cell036,middleDerivativeBox020Cell037,middleDerivativeBox020Cell038,middleDerivativeBox020Cell039]
theorem middleDerivativeBox020Cells_valid : ∀ i : Fin 40, (middleDerivativeBox020Cells i).Valid middleRangeSetup middleDerivativeParameters020 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox020Cell000_valid
  · exact middleDerivativeBox020Cell001_valid
  · exact middleDerivativeBox020Cell002_valid
  · exact middleDerivativeBox020Cell003_valid
  · exact middleDerivativeBox020Cell004_valid
  · exact middleDerivativeBox020Cell005_valid
  · exact middleDerivativeBox020Cell006_valid
  · exact middleDerivativeBox020Cell007_valid
  · exact middleDerivativeBox020Cell008_valid
  · exact middleDerivativeBox020Cell009_valid
  · exact middleDerivativeBox020Cell010_valid
  · exact middleDerivativeBox020Cell011_valid
  · exact middleDerivativeBox020Cell012_valid
  · exact middleDerivativeBox020Cell013_valid
  · exact middleDerivativeBox020Cell014_valid
  · exact middleDerivativeBox020Cell015_valid
  · exact middleDerivativeBox020Cell016_valid
  · exact middleDerivativeBox020Cell017_valid
  · exact middleDerivativeBox020Cell018_valid
  · exact middleDerivativeBox020Cell019_valid
  · exact middleDerivativeBox020Cell020_valid
  · exact middleDerivativeBox020Cell021_valid
  · exact middleDerivativeBox020Cell022_valid
  · exact middleDerivativeBox020Cell023_valid
  · exact middleDerivativeBox020Cell024_valid
  · exact middleDerivativeBox020Cell025_valid
  · exact middleDerivativeBox020Cell026_valid
  · exact middleDerivativeBox020Cell027_valid
  · exact middleDerivativeBox020Cell028_valid
  · exact middleDerivativeBox020Cell029_valid
  · exact middleDerivativeBox020Cell030_valid
  · exact middleDerivativeBox020Cell031_valid
  · exact middleDerivativeBox020Cell032_valid
  · exact middleDerivativeBox020Cell033_valid
  · exact middleDerivativeBox020Cell034_valid
  · exact middleDerivativeBox020Cell035_valid
  · exact middleDerivativeBox020Cell036_valid
  · exact middleDerivativeBox020Cell037_valid
  · exact middleDerivativeBox020Cell038_valid
  · exact middleDerivativeBox020Cell039_valid
theorem middleDerivativeBox020_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox020Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox020Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox020_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox020Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox020Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox020_partial_bounds {t a : ℝ} (htl : ((87/100) : ℝ) ≤ t) (htu : t ≤ ((871/1000) : ℝ))
    (hal : ((980624811595613/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((982235424331613/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters020 middleDerivativeParameters020_valid middleDerivativeBox020Cells (1/20) middleDerivativeBox020Cells_valid middleDerivativeBox020_upperA middleDerivativeBox020_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox020_derivative {t : ℝ} (htl : ((87/100) : ℝ) ≤ t) (htu : t ≤ ((871/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox020_enclosure htl htu
  have hp := middleDerivativeParameters020.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters020_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox020_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((871/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox020_derivative
