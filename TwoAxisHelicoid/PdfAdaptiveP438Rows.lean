import TwoAxisHelicoid.PdfAdaptiveP438Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP438Sound : adaptiveP438Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP438Params_ok (by decide +kernel) adaptiveP438Join12 adaptiveP438Join12_ok (by decide +kernel) adaptiveP438Output_ok ht hu ha hb
def adaptiveP438Rows : List SignRow := [positive_438.toSignRow, positive_439.toSignRow, positive_440.toSignRow, positive_441.toSignRow]
theorem adaptiveP438Rows_actual : ∀ r∈adaptiveP438Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP438Rows.all (adaptiveP438Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP438Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP438Rows_actual
