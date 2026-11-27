import TwoAxisHelicoid.PdfPrimalR008Q00
import TwoAxisHelicoid.PdfPrimalR008Q10

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_008 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_008.a a) : thetaHorizontalPeriod t a≤(endpoint_008.hUpper:ℝ) := by
  have r : ((49/50):ℝ)≤a ∧ a≤((99/100):ℝ) := by simpa [endpoint_008,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200
  · have v := @rightPrimalR008Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_008] using v
  · have v := @rightPrimalR008Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_008] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_008
