import TwoAxisHelicoid.PdfAdaptiveP345Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP345Sound : adaptiveP345Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP345Params_ok (by decide +kernel) adaptiveP345Join46 adaptiveP345Join46_ok (by decide +kernel) adaptiveP345Output_ok ht hu ha hb
def adaptiveP345Rows : List SignRow := [positive_345.toSignRow, positive_346.toSignRow, positive_347.toSignRow, positive_348.toSignRow, positive_349.toSignRow, positive_360.toSignRow, positive_361.toSignRow, positive_362.toSignRow]
theorem adaptiveP345Rows_actual : ∀ r∈adaptiveP345Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP345Rows.all (adaptiveP345Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP345Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP345Rows_actual
