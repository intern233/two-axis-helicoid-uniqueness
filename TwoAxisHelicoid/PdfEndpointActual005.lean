import TwoAxisHelicoid.PdfPrimalR005Q00
import TwoAxisHelicoid.PdfPrimalR005Q10

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_005 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_005.a a) : thetaHorizontalPeriod t a≤(endpoint_005.hUpper:ℝ) := by
  have r : ((19/20):ℝ)≤a ∧ a≤((24/25):ℝ) := by simpa [endpoint_005,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200
  · have v := @rightPrimalR005Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_005] using v
  · have v := @rightPrimalR005Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_005] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_005
