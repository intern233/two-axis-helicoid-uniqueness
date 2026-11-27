import TwoAxisHelicoid.PdfAdaptiveP265Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP265Sound : adaptiveP265Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP265Params_ok (by decide +kernel) adaptiveP265Join28 adaptiveP265Join28_ok (by decide +kernel) adaptiveP265Output_ok ht hu ha hb
def adaptiveP265Rows : List SignRow := [positive_265.toSignRow, positive_266.toSignRow, positive_267.toSignRow, positive_268.toSignRow, positive_269.toSignRow, positive_270.toSignRow, positive_271.toSignRow, positive_272.toSignRow]
theorem adaptiveP265Rows_actual : ∀ r∈adaptiveP265Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP265Rows.all (adaptiveP265Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP265Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP265Rows_actual
