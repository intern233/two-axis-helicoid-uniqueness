import TwoAxisHelicoid.PdfPrimalR003Q00
import TwoAxisHelicoid.PdfPrimalR003Q01
import TwoAxisHelicoid.PdfPrimalR003Q10
import TwoAxisHelicoid.PdfPrimalR003Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_003 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_003.a a) : thetaHorizontalPeriod t a≤(endpoint_003.hUpper:ℝ) := by
  have r : ((93/100):ℝ)≤a ∧ a≤((47/50):ℝ) := by simpa [endpoint_003,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((187/200):ℝ)
  · have v := @rightPrimalR003Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_003] using v
  · have v := @rightPrimalR003Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_003] using v
  · have v := @rightPrimalR003Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_003] using v
  · have v := @rightPrimalR003Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_003] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_003
