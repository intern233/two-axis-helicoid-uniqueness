import TwoAxisHelicoid.PdfPrimalR000Q00
import TwoAxisHelicoid.PdfPrimalR000Q01
import TwoAxisHelicoid.PdfPrimalR000Q10
import TwoAxisHelicoid.PdfPrimalR000Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_000 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_000.a a) : thetaHorizontalPeriod t a≤(endpoint_000.hUpper:ℝ) := by
  have r : ((9/10):ℝ)≤a ∧ a≤((91/100):ℝ) := by simpa [endpoint_000,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((181/200):ℝ)
  · have v := @rightPrimalR000Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_000] using v
  · have v := @rightPrimalR000Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_000] using v
  · have v := @rightPrimalR000Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_000] using v
  · have v := @rightPrimalR000Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_000] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_000
