import TwoAxisHelicoid.PdfAdaptiveP313Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP313Sound : adaptiveP313Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP313Params_ok (by decide +kernel) adaptiveP313Join42 adaptiveP313Join42_ok (by decide +kernel) adaptiveP313Output_ok ht hu ha hb
def adaptiveP313Rows : List SignRow := [positive_313.toSignRow, positive_314.toSignRow, positive_315.toSignRow, positive_316.toSignRow, positive_317.toSignRow, positive_318.toSignRow, positive_319.toSignRow, positive_320.toSignRow, positive_321.toSignRow, positive_322.toSignRow, positive_323.toSignRow, positive_324.toSignRow, positive_325.toSignRow, positive_326.toSignRow, positive_327.toSignRow, positive_328.toSignRow]
theorem adaptiveP313Rows_actual : ∀ r∈adaptiveP313Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP313Rows.all (adaptiveP313Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP313Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP313Rows_actual
