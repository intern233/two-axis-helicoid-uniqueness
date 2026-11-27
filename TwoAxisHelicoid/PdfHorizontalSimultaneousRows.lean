import TwoAxisHelicoid.PdfHorizontalExistingRows

namespace TwoAxisHelicoid.PdfHorizontal
open CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- In the same 305 original rectangles both coordinates of the dual
integral lie in their respective reported intervals. -/
theorem source_rectangles_both_columns :
    existingRectangleReal.length=305 ∧ ∀ r∈existingRectangleReal, ∀ t a : ℝ,
      RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfDualHorizontalIntegral t a).re ∧ RealMem r.hImag (pdfDualHorizontalIntegral t a).im := by
  have inclusion : existingRectangleReal.all (fun r =>
    covers false r.toSignRow r.t.lower (horizontalExistingBlocks.filter (matchingRectangle r.toSignRow)))=true := by decide +kernel
  refine ⟨existing_rectangle_real.1,?_⟩
  intro r hr t a ht ha
  have member : r∈positiveData := (List.mem_filter.mp hr).1
  have hi : r∈existingRectangleImag := List.mem_filter.mpr ⟨member,List.all_eq_true.mp inclusion r hr⟩
  exact ⟨existing_rectangle_real.2 r hr t a ht ha,existing_rectangle_imag.2 r hi t a ht ha⟩

/-- On the actual vertical branch, both columns apply simultaneously
in 345 of the original positive-table time intervals. -/
theorem source_branch_both_columns :
    existingPositiveReal.length=345 ∧ ∀ r∈existingPositiveReal, ∀ t : ℝ, RealMem r.t t →
      RealMem r.hReal (pdfDualHorizontalIntegral t (verticalA t)).re ∧
        RealMem r.hImag (pdfDualHorizontalIntegral t (verticalA t)).im := by
  have inclusion : existingPositiveReal.all (fun r =>
    covers false r.toSignRow r.t.lower horizontalExistingBlocks)=true := by decide +kernel
  refine ⟨existing_real_rows.1,?_⟩
  intro r hr t ht
  have member : r∈positiveData := (List.mem_filter.mp hr).1
  have hi : r∈existingPositiveImag := List.mem_filter.mpr ⟨member,List.all_eq_true.mp inclusion r hr⟩
  exact ⟨existing_real_rows.2 r hr t ht,existing_imag_rows.2 r hi t ht⟩

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.source_rectangles_both_columns
#print axioms TwoAxisHelicoid.PdfHorizontal.source_branch_both_columns

