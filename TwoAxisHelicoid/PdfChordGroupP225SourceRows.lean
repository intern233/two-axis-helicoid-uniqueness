import TwoAxisHelicoid.PdfChordGroupP225
import TwoAxisHelicoid.PdfHorizontalGroupedTransfer

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def meshP225SourceRows : List SignRow := [positive_225.toSignRow, positive_226.toSignRow, positive_227.toSignRow, positive_228.toSignRow, positive_229.toSignRow, positive_230.toSignRow, positive_231.toSignRow, positive_232.toSignRow]

theorem meshP225SourceRows_actual : ∀ s∈meshP225SourceRows, ∀ t a : ℝ, RealMem s.t t → RealMem s.a a →
    RealMem s.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem s.hImag (sourceHorizontalIntegral true t a).im := by
  have allRows : meshP225SourceRows.all (meshP225.coversRow true)=true := by decide +kernel
  have proof := HorizontalRectangle.sound_of_check meshP225 meshP225_checked
  intro s hs t a ht ha
  exact HorizontalRectangle.row_sound proof (List.all_eq_true.mp allRows s hs) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.meshP225SourceRows_actual
