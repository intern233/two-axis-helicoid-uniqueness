import TwoAxisHelicoid.PdfHorizontalSimultaneousRows
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid.PdfHorizontal
open CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem positive_time_in_chord_domain {r : CheckedSignRow true (3/10000)} (hr : r∈positiveData)
    {t : ℝ} (ht : RealMem r.t t) : 0<t ∧ t≤7/5 := by
  have allRows : positiveData.all (fun s => decide (0<s.t.lower ∧ s.t.upper≤7/5))=true := by decide +kernel
  obtain ⟨lo,hi⟩ := of_decide_eq_true (List.all_eq_true.mp allRows r hr)
  have upper : (r.t.upper:ℝ)≤((7/5:ℚ):ℝ) := Rat.cast_le.mpr hi
  push_cast at upper
  exact ⟨(Rat.cast_pos.mpr lo).trans_le ht.1,ht.2.trans upper⟩

/-- Original complex output enclosures imply both the full real period
interval and the manuscript's positive margin, including both endpoints. -/
theorem original_rectangle_period_and_margin :
    existingRectangleReal.length=305 ∧ ∀ r∈existingRectangleReal, ∀ t a : ℝ,
      RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (thetaHorizontalPeriod t a) ∧ (3/10000:ℝ)<thetaHorizontalPeriod t a := by
  refine ⟨source_rectangles_both_columns.1,?_⟩
  intro r hr t a ht ha
  obtain ⟨tp,tu⟩ := positive_time_in_chord_domain (List.mem_filter.mp hr).1 ht
  obtain ⟨_,_,al,_,au,_⟩ := r.verified
  have ap := (Rat.cast_pos.mpr al).trans_le ha.1
  have ab : a<1 := ha.2.trans_lt (by exact_mod_cast au)
  have bound := (source_rectangles_both_columns.2 r hr t a ht ha).1
  rw [pdf_dual_horizontal_integral_chord tp tu ap ab,
    ← horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths tp tu ap ab] at bound
  have margin := positive_of_row_enclosure r bound
  push_cast at margin
  exact ⟨bound,margin⟩

theorem original_branch_period_and_margin :
    existingPositiveReal.length=345 ∧ ∀ r∈existingPositiveReal, ∀ t : ℝ, RealMem r.t t →
      RealMem r.hReal (actualPeriodAlong t) ∧ (3/10000:ℝ)<actualPeriodAlong t := by
  refine ⟨source_branch_both_columns.1,?_⟩
  intro r hr t ht
  obtain ⟨tp,tu⟩ := positive_time_in_chord_domain (List.mem_filter.mp hr).1 ht
  have tt : t<ellipticVerticalUpper := tu.trans_lt (lt_trans (by norm_num) ellipticVerticalUpper_location.1)
  have ha := (verticalA_spec ⟨tp,tt⟩).1
  have bound := (source_branch_both_columns.2 r hr t ht).1
  rw [pdf_dual_horizontal_integral_chord tp tu ha.1 ha.2,
    ← horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths tp tu ha.1 ha.2] at bound
  have margin := positive_of_row_enclosure r bound
  push_cast at margin
  exact ⟨bound,margin⟩

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.original_rectangle_period_and_margin
#print axioms TwoAxisHelicoid.PdfHorizontal.original_branch_period_and_margin

