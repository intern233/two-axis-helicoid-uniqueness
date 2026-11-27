import TwoAxisHelicoid.PdfAdaptiveP186Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP186Sound : adaptiveP186Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP186Params_ok (by decide +kernel) adaptiveP186Join19 adaptiveP186Join19_ok (by decide +kernel) adaptiveP186Output_ok ht hu ha hb
def adaptiveP186Rows : List SignRow := [positive_186.toSignRow, positive_187.toSignRow, positive_188.toSignRow, positive_189.toSignRow, positive_190.toSignRow, positive_191.toSignRow, positive_192.toSignRow, positive_193.toSignRow]
theorem adaptiveP186Rows_actual : ∀ r∈adaptiveP186Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP186Rows.all (adaptiveP186Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP186Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP186Rows_actual
