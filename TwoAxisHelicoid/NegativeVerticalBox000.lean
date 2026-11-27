import TwoAxisHelicoid.NegativeVerticalBox000Data
import TwoAxisHelicoid.RangePeriodBounds
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem negativeVerticalBox000_enclosure {t : ℝ} (htl : ((9/10) : ℝ) ≤ t) (htu : t ≤ ((1441/1600) : ℝ)) :
    verticalA t ∈ Set.Ioo ((79277/131072) : ℝ) ((79329/131072) : ℝ) := by
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper := ⟨lt_of_lt_of_le (by norm_num) htl, htu.trans_lt ((by norm_num : ((1441/1600) : ℝ) < 100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have hpLower := negativeVerticalBox000LowerParameters.sound middleRangeSetup middleRangeSetup_valid negativeVerticalBox000LowerParameters_valid (t := t) (a := ((79277/131072) : ℝ)) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by norm_num) (by norm_num)
  have hgLower := negativeVerticalBox000LowerParameters.vertical_sound middleRangeSetup hpLower negativeVerticalBox000Lower negativeVerticalBox000Lower_valid
  have hpUpper := negativeVerticalBox000UpperParameters.sound middleRangeSetup middleRangeSetup_valid negativeVerticalBox000UpperParameters_valid (t := t) (a := ((79329/131072) : ℝ)) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl) (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by norm_num) (by norm_num)
  have hgUpper := negativeVerticalBox000UpperParameters.vertical_sound middleRangeSetup hpUpper negativeVerticalBox000Upper negativeVerticalBox000Upper_valid
  apply verticalA_mem_of_boundary_signs ht (by norm_num) (by norm_num)
  · exact lt_of_lt_of_le (by exact_mod_cast negativeVerticalBox000Lower_sign) (ComplexBall.re_bounds hgLower).1
  · exact lt_of_le_of_lt (ComplexBall.re_bounds hgUpper).2 (by exact_mod_cast negativeVerticalBox000Upper_sign)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.negativeVerticalBox000_enclosure
