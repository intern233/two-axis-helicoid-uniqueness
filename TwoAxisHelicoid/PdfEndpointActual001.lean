import TwoAxisHelicoid.PdfPrimalR001Q00
import TwoAxisHelicoid.PdfPrimalR001Q01
import TwoAxisHelicoid.PdfPrimalR001Q10
import TwoAxisHelicoid.PdfPrimalR001Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_001 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_001.a a) : thetaHorizontalPeriod t a≤(endpoint_001.hUpper:ℝ) := by
  have r : ((91/100):ℝ)≤a ∧ a≤((23/25):ℝ) := by simpa [endpoint_001,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((183/200):ℝ)
  · have v := @rightPrimalR001Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_001] using v
  · have v := @rightPrimalR001Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_001] using v
  · have v := @rightPrimalR001Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_001] using v
  · have v := @rightPrimalR001Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_001] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_001
