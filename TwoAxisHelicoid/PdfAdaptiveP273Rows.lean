import TwoAxisHelicoid.PdfAdaptiveP273Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP273Sound : adaptiveP273Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP273Params_ok (by decide +kernel) adaptiveP273Join13 adaptiveP273Join13_ok (by decide +kernel) adaptiveP273Output_ok ht hu ha hb
def adaptiveP273Rows : List SignRow := [positive_273.toSignRow]
theorem adaptiveP273Rows_actual : ∀ r∈adaptiveP273Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP273Rows.all (adaptiveP273Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP273Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP273Rows_actual
