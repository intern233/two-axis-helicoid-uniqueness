import TwoAxisHelicoid.MiddleVerticalBox032
import TwoAxisHelicoid.MiddleDerivativeBox032BridgeGroup0
import TwoAxisHelicoid.MiddleDerivativeBox032BridgeGroup1
import TwoAxisHelicoid.MiddleDerivativeBox032BridgeGroup2
import TwoAxisHelicoid.MiddleDerivativeBox032BridgeGroup3
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeBox032Cells : Fin 40 → RangeDerivativeCell := ![middleDerivativeBox032Cell000,middleDerivativeBox032Cell001,middleDerivativeBox032Cell002,middleDerivativeBox032Cell003,middleDerivativeBox032Cell004,middleDerivativeBox032Cell005,middleDerivativeBox032Cell006,middleDerivativeBox032Cell007,middleDerivativeBox032Cell008,middleDerivativeBox032Cell009,middleDerivativeBox032Cell010,middleDerivativeBox032Cell011,middleDerivativeBox032Cell012,middleDerivativeBox032Cell013,middleDerivativeBox032Cell014,middleDerivativeBox032Cell015,middleDerivativeBox032Cell016,middleDerivativeBox032Cell017,middleDerivativeBox032Cell018,middleDerivativeBox032Cell019,middleDerivativeBox032Cell020,middleDerivativeBox032Cell021,middleDerivativeBox032Cell022,middleDerivativeBox032Cell023,middleDerivativeBox032Cell024,middleDerivativeBox032Cell025,middleDerivativeBox032Cell026,middleDerivativeBox032Cell027,middleDerivativeBox032Cell028,middleDerivativeBox032Cell029,middleDerivativeBox032Cell030,middleDerivativeBox032Cell031,middleDerivativeBox032Cell032,middleDerivativeBox032Cell033,middleDerivativeBox032Cell034,middleDerivativeBox032Cell035,middleDerivativeBox032Cell036,middleDerivativeBox032Cell037,middleDerivativeBox032Cell038,middleDerivativeBox032Cell039]
theorem middleDerivativeBox032Cells_valid : ∀ i : Fin 40, (middleDerivativeBox032Cells i).Valid middleRangeSetup middleDerivativeParameters032 (horizontalCellCenter 80 i) (horizontalCellRadius 80) (1/20) := by
  intro i
  fin_cases i
  · exact middleDerivativeBox032Cell000_valid
  · exact middleDerivativeBox032Cell001_valid
  · exact middleDerivativeBox032Cell002_valid
  · exact middleDerivativeBox032Cell003_valid
  · exact middleDerivativeBox032Cell004_valid
  · exact middleDerivativeBox032Cell005_valid
  · exact middleDerivativeBox032Cell006_valid
  · exact middleDerivativeBox032Cell007_valid
  · exact middleDerivativeBox032Cell008_valid
  · exact middleDerivativeBox032Cell009_valid
  · exact middleDerivativeBox032Cell010_valid
  · exact middleDerivativeBox032Cell011_valid
  · exact middleDerivativeBox032Cell012_valid
  · exact middleDerivativeBox032Cell013_valid
  · exact middleDerivativeBox032Cell014_valid
  · exact middleDerivativeBox032Cell015_valid
  · exact middleDerivativeBox032Cell016_valid
  · exact middleDerivativeBox032Cell017_valid
  · exact middleDerivativeBox032Cell018_valid
  · exact middleDerivativeBox032Cell019_valid
  · exact middleDerivativeBox032Cell020_valid
  · exact middleDerivativeBox032Cell021_valid
  · exact middleDerivativeBox032Cell022_valid
  · exact middleDerivativeBox032Cell023_valid
  · exact middleDerivativeBox032Cell024_valid
  · exact middleDerivativeBox032Cell025_valid
  · exact middleDerivativeBox032Cell026_valid
  · exact middleDerivativeBox032Cell027_valid
  · exact middleDerivativeBox032Cell028_valid
  · exact middleDerivativeBox032Cell029_valid
  · exact middleDerivativeBox032Cell030_valid
  · exact middleDerivativeBox032Cell031_valid
  · exact middleDerivativeBox032Cell032_valid
  · exact middleDerivativeBox032Cell033_valid
  · exact middleDerivativeBox032Cell034_valid
  · exact middleDerivativeBox032Cell035_valid
  · exact middleDerivativeBox032Cell036_valid
  · exact middleDerivativeBox032Cell037_valid
  · exact middleDerivativeBox032Cell038_valid
  · exact middleDerivativeBox032Cell039_valid
theorem middleDerivativeBox032_upperA : (combineHorizontalCells (fun i => (middleDerivativeBox032Cells i).outputA.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox032Cells i).outputA.toBall middleRangeSetup.config.prec)).radius < 0 := by decide +kernel
theorem middleDerivativeBox032_upperT : (combineHorizontalCells (fun i => (middleDerivativeBox032Cells i).outputT.toBall middleRangeSetup.config.prec)).center.re+(combineHorizontalCells (fun i => (middleDerivativeBox032Cells i).outputT.toBall middleRangeSetup.config.prec)).radius < -1 := by decide +kernel
theorem middleDerivativeBox032_partial_bounds {t a : ℝ} (htl : ((441/500) : ℝ) ≤ t) (htu : t ≤ ((883/1000) : ℝ))
    (hal : ((987133262649019/1649267441664000) : ℝ) ≤ a) (hau : a ≤ ((988743875385019/1649267441664000) : ℝ)) :
    horizontalPeriodDa t a < 0 ∧ horizontalPeriodDt t a < -1 := by
  simpa using range_derivative_partial_upper middleRangeSetup middleRangeSetup_valid (by decide : 0 < 40) middleDerivativeParameters032 middleDerivativeParameters032_valid middleDerivativeBox032Cells (1/20) middleDerivativeBox032Cells_valid middleDerivativeBox032_upperA middleDerivativeBox032_upperT (t := t) (a := a) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hal) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hau)
theorem middleDerivativeBox032_derivative {t : ℝ} (htl : ((441/500) : ℝ) ≤ t) (htu : t ≤ ((883/1000) : ℝ)) : deriv actualPeriodAlong t < -1 := by
  have ha := middleVerticalBox032_enclosure htl htu
  have hp := middleDerivativeParameters032.sound middleRangeSetup middleRangeSetup_valid middleDerivativeParameters032_valid (t := t) (a := verticalA t) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.1.le) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha.2.le)
  have hpartial := middleDerivativeBox032_partial_bounds htl htu ha.1.le ha.2.le
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((883/1000) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  exact actualPeriodAlong_deriv_lt_of_partial_bounds ht (lt_of_lt_of_le (by norm_num) hp.gt_lower) hpartial.1 hpartial.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeBox032_derivative
