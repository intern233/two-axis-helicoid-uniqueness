import TwoAxisHelicoid.PdfAdaptiveP395Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP395Sound : adaptiveP395Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP395Params_ok (by decide +kernel) adaptiveP395Join16 adaptiveP395Join16_ok (by decide +kernel) adaptiveP395Output_ok ht hu ha hb
def adaptiveP395Rows : List SignRow := [positive_395.toSignRow, positive_396.toSignRow, positive_397.toSignRow, positive_398.toSignRow, positive_399.toSignRow, positive_400.toSignRow, positive_401.toSignRow, positive_402.toSignRow]
theorem adaptiveP395Rows_actual : ∀ r∈adaptiveP395Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP395Rows.all (adaptiveP395Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP395Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP395Rows_actual
