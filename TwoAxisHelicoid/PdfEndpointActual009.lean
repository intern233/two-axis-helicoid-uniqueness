import TwoAxisHelicoid.PdfPrimalR009Q00
import TwoAxisHelicoid.PdfPrimalR009Q01
import TwoAxisHelicoid.PdfPrimalR009Q10
import TwoAxisHelicoid.PdfPrimalR009Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_009 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_009.a a) : thetaHorizontalPeriod t a≤(endpoint_009.hUpper:ℝ) := by
  have r : ((99/100):ℝ)≤a ∧ a≤(1:ℝ) := by simpa [endpoint_009,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((199/200):ℝ)
  · have v := @rightPrimalR009Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_009] using v
  · have v := @rightPrimalR009Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_009] using v
  · have v := @rightPrimalR009Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_009] using v
  · have v := @rightPrimalR009Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_009] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_009
