import TwoAxisHelicoid.PdfAdaptiveP379Path
import TwoAxisHelicoid.PdfAdaptiveHorizontalRectangle

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

theorem adaptiveP379Sound : adaptiveP379Box.Sound := by
  intro t a ht hu ha hb
  exact adaptive_horizontal_on_box adaptiveP379Params_ok (by decide +kernel) adaptiveP379Join70 adaptiveP379Join70_ok (by decide +kernel) adaptiveP379Output_ok ht hu ha hb
def adaptiveP379Rows : List SignRow := [positive_379.toSignRow, positive_380.toSignRow, positive_381.toSignRow, positive_382.toSignRow, positive_383.toSignRow, positive_384.toSignRow, positive_385.toSignRow, positive_386.toSignRow, positive_387.toSignRow, positive_388.toSignRow, positive_389.toSignRow, positive_390.toSignRow, positive_391.toSignRow, positive_392.toSignRow, positive_393.toSignRow, positive_394.toSignRow]
theorem adaptiveP379Rows_actual : ∀ r∈adaptiveP379Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : adaptiveP379Rows.all (adaptiveP379Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound adaptiveP379Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptiveP379Rows_actual
