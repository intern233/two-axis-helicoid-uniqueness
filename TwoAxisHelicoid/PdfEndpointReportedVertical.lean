import TwoAxisHelicoid.PdfVerticalRowSound
import TwoAxisHelicoid.PdfEndpointVerticalCut
import TwoAxisHelicoid.RangePeriodBounds

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- Original right-end attachment. The dyadic lower endpoint bounds
the real vertical function throughout the entire reported strip. -/
theorem original_right_endpoint_vertical_enclosure {t : ℝ} (lo : 7/5≤t) (hi : t≤141/100) :
    (63756382130020915978949311/1237940039285380274899124224:ℝ)≤(thetaG t (9/10)).re ∧
    (thetaG t (9/10)).re≤100 := by
  have left : ((7/5:ℚ):ℝ)≤t := by simpa only [Rat.cast_div,Rat.cast_ofNat] using lo
  have right : t≤((141/100:ℚ):ℝ) := by simpa only [Rat.cast_div,Rat.cast_ofNat] using hi
  have h := verticalCover_sound rightEndpointLowerCut (by norm_num) left right
    (lt_of_lt_of_le (by norm_num) lo) (by norm_num) (by norm_num)
  simpa only [reportedVertical,Bool.false_eq_true,ite_false,Rat.cast_div,Rat.cast_ofNat] using h

theorem original_right_cut_locates_branch {t : ℝ} (lo : 7/5≤t) (hi : t≤141/100) (admissible : t<ellipticVerticalUpper) :
    9/10<verticalA t ∧ verticalA t<1 := by
  have tp : 0<t := lt_of_lt_of_le (by norm_num) lo
  obtain ⟨interior,root⟩ := verticalA_spec ⟨tp,admissible⟩
  refine ⟨?_,interior.2⟩
  have lower := (original_right_endpoint_vertical_enclosure lo hi).1
  have zero : (thetaG t (verticalA t)).re=0 := by rw [root];rfl
  by_contra h
  have anti := (thetaG_strictAnti_unit_of_pos tp).antitoneOn interior
    (show (9/10:ℝ)∈Ioo (0:ℝ) 1 by constructor <;> norm_num) (le_of_not_gt h)
  change (thetaG t (9/10)).re≤(thetaG t (verticalA t)).re at anti
  linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_right_endpoint_vertical_enclosure
#print axioms TwoAxisHelicoid.PdfVertical.original_right_cut_locates_branch

