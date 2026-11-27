import TwoAxisHelicoid.PdfAdaptiveP296Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP296Sound : adaptiveP296Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP296Params_ok (by decide +kernel) adaptiveP296Join42 adaptiveP296Join42_ok (by decide +kernel) adaptiveP296Output_ok ht hu ha hb
def adaptiveP296Rows : List SignRow := [positive_296.toSignRow, positive_297.toSignRow, positive_299.toSignRow, positive_300.toSignRow, positive_301.toSignRow, positive_302.toSignRow, positive_303.toSignRow, positive_304.toSignRow, positive_305.toSignRow, positive_306.toSignRow, positive_307.toSignRow, positive_308.toSignRow, positive_309.toSignRow, positive_310.toSignRow, positive_311.toSignRow, positive_312.toSignRow]
theorem adaptiveP296Rows_actual : ∀ r∈adaptiveP296Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP296Rows.all (adaptiveP296Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP296Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP296Rows_actual
