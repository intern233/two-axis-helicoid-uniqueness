import TwoAxisHelicoid.PdfPrimalR004Q00
import TwoAxisHelicoid.PdfPrimalR004Q10

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_004 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_004.a a) : thetaHorizontalPeriod t a≤(endpoint_004.hUpper:ℝ) := by
  have r : ((47/50):ℝ)≤a ∧ a≤((19/20):ℝ) := by simpa [endpoint_004,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200
  · have v := @rightPrimalR004Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_004] using v
  · have v := @rightPrimalR004Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_004] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_004
