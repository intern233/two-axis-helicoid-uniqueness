import TwoAxisHelicoid.PdfAdaptiveP329Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP329Sound : adaptiveP329Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP329Params_ok (by decide +kernel) adaptiveP329Join46 adaptiveP329Join46_ok (by decide +kernel) adaptiveP329Output_ok ht hu ha hb
def adaptiveP329Rows : List SignRow := [positive_329.toSignRow, positive_330.toSignRow, positive_331.toSignRow, positive_332.toSignRow, positive_333.toSignRow, positive_334.toSignRow, positive_335.toSignRow, positive_336.toSignRow, positive_337.toSignRow, positive_338.toSignRow, positive_339.toSignRow, positive_340.toSignRow, positive_341.toSignRow, positive_342.toSignRow, positive_343.toSignRow, positive_344.toSignRow]
theorem adaptiveP329Rows_actual : ∀ r∈adaptiveP329Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP329Rows.all (adaptiveP329Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP329Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP329Rows_actual
