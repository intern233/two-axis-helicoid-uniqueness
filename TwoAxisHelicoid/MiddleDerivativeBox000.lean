import TwoAxisHelicoid.MiddleVerticalBox000
import TwoAxisHelicoid.MiddleDerivativeBox000Cell000
import TwoAxisHelicoid.MiddleDerivativeBox000Cell001
import TwoAxisHelicoid.MiddleDerivativeBox000Cell002
import TwoAxisHelicoid.MiddleDerivativeBox000Cell003
import TwoAxisHelicoid.MiddleDerivativeBox000Cell004
import TwoAxisHelicoid.MiddleDerivativeBox000Cell005
import TwoAxisHelicoid.MiddleDerivativeBox000Cell006
import TwoAxisHelicoid.MiddleDerivativeBox000Cell007
import TwoAxisHelicoid.MiddleDerivativeBox000Cell008
import TwoAxisHelicoid.MiddleDerivativeBox000Cell009
import TwoAxisHelicoid.MiddleDerivativeBox000Cell010
import TwoAxisHelicoid.MiddleDerivativeBox000Cell011
import TwoAxisHelicoid.MiddleDerivativeBox000Cell012
import TwoAxisHelicoid.MiddleDerivativeBox000Cell013
import TwoAxisHelicoid.MiddleDerivativeBox000Cell014
import TwoAxisHelicoid.MiddleDerivativeBox000Cell015
import TwoAxisHelicoid.MiddleDerivativeBox000Cell016
import TwoAxisHelicoid.MiddleDerivativeBox000Cell017
import TwoAxisHelicoid.MiddleDerivativeBox000Cell018
import TwoAxisHelicoid.MiddleDerivativeBox000Cell019
import TwoAxisHelicoid.MiddleDerivativeBox000Cell020
import TwoAxisHelicoid.MiddleDerivativeBox000Cell021
import TwoAxisHelicoid.MiddleDerivativeBox000Cell022
import TwoAxisHelicoid.MiddleDerivativeBox000Cell023
import TwoAxisHelicoid.MiddleDerivativeBox000Cell024
import TwoAxisHelicoid.MiddleDerivativeBox000Cell025
import TwoAxisHelicoid.MiddleDerivativeBox000Cell026
import TwoAxisHelicoid.MiddleDerivativeBox000Cell027
import TwoAxisHelicoid.MiddleDerivativeBox000Cell028
import TwoAxisHelicoid.MiddleDerivativeBox000Cell029
import TwoAxisHelicoid.MiddleDerivativeBox000Cell030
import TwoAxisHelicoid.MiddleDerivativeBox000Cell031
import TwoAxisHelicoid.MiddleDerivativeBox000Cell032
import TwoAxisHelicoid.MiddleDerivativeBox000Cell033
import TwoAxisHelicoid.MiddleDerivativeBox000Cell034
import TwoAxisHelicoid.MiddleDerivativeBox000Cell035
import TwoAxisHelicoid.MiddleDerivativeBox000Cell036
import TwoAxisHelicoid.MiddleDerivativeBox000Cell037
import TwoAxisHelicoid.MiddleDerivativeBox000Cell038
import TwoAxisHelicoid.MiddleDerivativeBox000Cell039
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox000Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox000Cell000,middleDerivativeBox000Cell001,middleDerivativeBox000Cell002,middleDerivativeBox000Cell003,middleDerivativeBox000Cell004,middleDerivativeBox000Cell005,middleDerivativeBox000Cell006,middleDerivativeBox000Cell007,middleDerivativeBox000Cell008,middleDerivativeBox000Cell009,middleDerivativeBox000Cell010,middleDerivativeBox000Cell011,middleDerivativeBox000Cell012,middleDerivativeBox000Cell013,middleDerivativeBox000Cell014,middleDerivativeBox000Cell015,middleDerivativeBox000Cell016,middleDerivativeBox000Cell017,middleDerivativeBox000Cell018,middleDerivativeBox000Cell019,middleDerivativeBox000Cell020,middleDerivativeBox000Cell021,middleDerivativeBox000Cell022,middleDerivativeBox000Cell023,middleDerivativeBox000Cell024,middleDerivativeBox000Cell025,middleDerivativeBox000Cell026,middleDerivativeBox000Cell027,middleDerivativeBox000Cell028,middleDerivativeBox000Cell029,middleDerivativeBox000Cell030,middleDerivativeBox000Cell031,middleDerivativeBox000Cell032,middleDerivativeBox000Cell033,middleDerivativeBox000Cell034,middleDerivativeBox000Cell035,middleDerivativeBox000Cell036,middleDerivativeBox000Cell037,middleDerivativeBox000Cell038,middleDerivativeBox000Cell039]
theorem middleDerivativeBox000Cells_valid : ∀ i : Fin 40, (middleDerivativeBox000Cells i).Valid middleRangeSetup middleDerivativeParameters000 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox000Cell000_valid
  · exact middleDerivativeBox000Cell001_valid
  · exact middleDerivativeBox000Cell002_valid
  · exact middleDerivativeBox000Cell003_valid
  · exact middleDerivativeBox000Cell004_valid
  · exact middleDerivativeBox000Cell005_valid
  · exact middleDerivativeBox000Cell006_valid
  · exact middleDerivativeBox000Cell007_valid
  · exact middleDerivativeBox000Cell008_valid
  · exact middleDerivativeBox000Cell009_valid
  · exact middleDerivativeBox000Cell010_valid
  · exact middleDerivativeBox000Cell011_valid
  · exact middleDerivativeBox000Cell012_valid
  · exact middleDerivativeBox000Cell013_valid
  · exact middleDerivativeBox000Cell014_valid
  · exact middleDerivativeBox000Cell015_valid
  · exact middleDerivativeBox000Cell016_valid
  · exact middleDerivativeBox000Cell017_valid
  · exact middleDerivativeBox000Cell018_valid
  · exact middleDerivativeBox000Cell019_valid
  · exact middleDerivativeBox000Cell020_valid
  · exact middleDerivativeBox000Cell021_valid
  · exact middleDerivativeBox000Cell022_valid
  · exact middleDerivativeBox000Cell023_valid
  · exact middleDerivativeBox000Cell024_valid
  · exact middleDerivativeBox000Cell025_valid
  · exact middleDerivativeBox000Cell026_valid
  · exact middleDerivativeBox000Cell027_valid
  · exact middleDerivativeBox000Cell028_valid
  · exact middleDerivativeBox000Cell029_valid
  · exact middleDerivativeBox000Cell030_valid
  · exact middleDerivativeBox000Cell031_valid
  · exact middleDerivativeBox000Cell032_valid
  · exact middleDerivativeBox000Cell033_valid
  · exact middleDerivativeBox000Cell034_valid
  · exact middleDerivativeBox000Cell035_valid
  · exact middleDerivativeBox000Cell036_valid
  · exact middleDerivativeBox000Cell037_valid
  · exact middleDerivativeBox000Cell038_valid
  · exact middleDerivativeBox000Cell039_valid
theorem middleDerivativeBox000_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox000Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox000Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox000_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox000Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox000Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox000_partial_bounds {t a : ℝ} (htl : ((17/20) : ℝ) ≤ t) (htu : t ≤ ((851/1000) : ℝ))
    (hal : ((970090990727617/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((971701603463617/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters000 middleDerivativeParameters000_valid middleDerivativeBox000Cells (1/20) middleDerivativeBox000Cells_valid middleDerivativeBox000_upperA middleDerivativeBox000_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox000_derivative {t : ℝ} (htl : ((17/20) : ℝ) ≤ t) (htu : t ≤ ((851/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox000_enclosure htl htu
  have hp := middleDerivativeParameters000.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters000_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox000_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((851/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox000_derivative
