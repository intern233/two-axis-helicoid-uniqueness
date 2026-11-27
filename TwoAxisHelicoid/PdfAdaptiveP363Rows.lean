import TwoAxisHelicoid.PdfAdaptiveP363Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP363Sound : adaptiveP363Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP363Params_ok (by decide +kernel) adaptiveP363Join42 adaptiveP363Join42_ok (by decide +kernel) adaptiveP363Output_ok ht hu ha hb
def adaptiveP363Rows : List SignRow := [positive_363.toSignRow, positive_364.toSignRow, positive_365.toSignRow, positive_366.toSignRow, positive_367.toSignRow, positive_368.toSignRow, positive_369.toSignRow, positive_370.toSignRow, positive_371.toSignRow, positive_372.toSignRow, positive_373.toSignRow, positive_374.toSignRow, positive_375.toSignRow, positive_376.toSignRow, positive_377.toSignRow, positive_378.toSignRow]
theorem adaptiveP363Rows_actual : ∀ r∈adaptiveP363Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP363Rows.all (adaptiveP363Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP363Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP363Rows_actual
