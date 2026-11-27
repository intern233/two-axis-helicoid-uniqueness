import TwoAxisHelicoid.PdfHorizontalBlocks1000

namespace TwoAxisHelicoid.PdfHorizontal
open CertificateData CertificateSemantics
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def horizontalPilotBlocks : List Block := [
  block1000]

private theorem blocks_sound : ∀ b∈horizontalPilotBlocks, b.Sound := by
  intro b hb
  simp only [horizontalPilotBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  subst b
  exact block1000_sound

private theorem rectangles_sound : ∀ b∈horizontalPilotBlocks, b.RectSound := by
  intro b hb
  simp only [horizontalPilotBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  subst b
  exact block1000_rectangle_sound

def pilotRectangleReal := positiveData.filter (fun r =>
  covers true r.toSignRow r.t.lower (horizontalPilotBlocks.filter (matchingRectangle r.toSignRow)))

theorem pilot_rectangle_real : pilotRectangleReal.length=40 ∧
    ∀ r∈pilotRectangleReal, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfDualHorizontalIntegral t a).re := by
  exact ⟨by decide +kernel,positive_rectangular_column_sound horizontalPilotBlocks rectangles_sound true⟩

def pilotRectangleImag := positiveData.filter (fun r =>
  covers false r.toSignRow r.t.lower (horizontalPilotBlocks.filter (matchingRectangle r.toSignRow)))

theorem pilot_rectangle_imag : pilotRectangleImag.length=40 ∧
    ∀ r∈pilotRectangleImag, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hImag (pdfDualHorizontalIntegral t a).im := by
  exact ⟨by decide +kernel,positive_rectangular_column_sound horizontalPilotBlocks rectangles_sound false⟩

def pilotPositiveReal := positiveData.filter (fun r => covers true r.toSignRow r.t.lower horizontalPilotBlocks)
def pilotPositiveImag := positiveData.filter (fun r => covers false r.toSignRow r.t.lower horizontalPilotBlocks)

theorem pilot_real_rows : pilotPositiveReal.length=40 ∧
    ∀ r∈pilotPositiveReal, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (pdfDualHorizontalIntegral t (verticalA t)).re := by
  exact ⟨by decide +kernel,positive_filtered_column_sound horizontalPilotBlocks blocks_sound true⟩

theorem pilot_imag_rows : pilotPositiveImag.length=40 ∧
    ∀ r∈pilotPositiveImag, ∀ t : ℝ, RealMem r.t t → RealMem r.hImag (pdfDualHorizontalIntegral t (verticalA t)).im := by
  exact ⟨by decide +kernel,positive_filtered_column_sound horizontalPilotBlocks blocks_sound false⟩

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.pilot_real_rows
#print axioms TwoAxisHelicoid.PdfHorizontal.pilot_imag_rows
#print axioms TwoAxisHelicoid.PdfHorizontal.pilot_rectangle_real
#print axioms TwoAxisHelicoid.PdfHorizontal.pilot_rectangle_imag
