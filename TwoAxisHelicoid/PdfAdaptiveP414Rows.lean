import TwoAxisHelicoid.PdfAdaptiveP414Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP414Sound : adaptiveP414Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP414Params_ok (by decide +kernel) adaptiveP414Join62 adaptiveP414Join62_ok (by decide +kernel) adaptiveP414Output_ok ht hu ha hb
def adaptiveP414Rows : List SignRow := [positive_414.toSignRow, positive_415.toSignRow, positive_416.toSignRow, positive_417.toSignRow, positive_418.toSignRow, positive_419.toSignRow, positive_420.toSignRow, positive_421.toSignRow, positive_422.toSignRow, positive_423.toSignRow, positive_424.toSignRow, positive_425.toSignRow]
theorem adaptiveP414Rows_actual : ∀ r∈adaptiveP414Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP414Rows.all (adaptiveP414Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP414Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP414Rows_actual
