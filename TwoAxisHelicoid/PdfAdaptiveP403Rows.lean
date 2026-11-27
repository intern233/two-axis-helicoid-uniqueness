import TwoAxisHelicoid.PdfAdaptiveP403Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP403Sound : adaptiveP403Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP403Params_ok (by decide +kernel) adaptiveP403Join30 adaptiveP403Join30_ok (by decide +kernel) adaptiveP403Output_ok ht hu ha hb
def adaptiveP403Rows : List SignRow := [positive_403.toSignRow, positive_411.toSignRow, positive_412.toSignRow, positive_413.toSignRow]
theorem adaptiveP403Rows_actual : ∀ r∈adaptiveP403Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP403Rows.all (adaptiveP403Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP403Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP403Rows_actual
