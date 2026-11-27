import TwoAxisHelicoid.PdfRefinedChordQuadrature
import TwoAxisHelicoid.PdfHorizontalGroupedTransfer

namespace TwoAxisHelicoid.PdfVertical
open MeasureTheory

theorem refined_dual_output_encloses {box : HorizontalRectangle} {out : CGrid}
    {t a : ℝ} (ht : 0<t) (hu : t≤7/5) (ha : 0<a) (hb : a<1)
    (integral : out.Contains (∫ x : ℝ in (-1)..1, jacobiChordKernel t a (x:ℂ)))
    (realBound : containedInReported out.re box.reLo box.reHi=true)
    (imagBound : containedInReported out.im box.imLo box.imHi=true) :
    box.Encloses (sourceHorizontalIntegral true t a) := by
  change box.Encloses (pdfDualHorizontalIntegral t a)
  rw [pdf_dual_horizontal_integral_chord ht hu ha hb]
  obtain ⟨rl,ru⟩ := containedInReported_sound integral.1 realBound
  exact ⟨rl,ru,containedInReported_sound integral.2 imagBound⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.refined_dual_output_encloses

