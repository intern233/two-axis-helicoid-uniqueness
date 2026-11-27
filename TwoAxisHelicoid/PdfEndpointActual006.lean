import TwoAxisHelicoid.PdfPrimalR006Q00
import TwoAxisHelicoid.PdfPrimalR006Q01
import TwoAxisHelicoid.PdfPrimalR006Q10
import TwoAxisHelicoid.PdfPrimalR006Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_006 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_006.a a) : thetaHorizontalPeriod t a≤(endpoint_006.hUpper:ℝ) := by
  have r : ((24/25):ℝ)≤a ∧ a≤((97/100):ℝ) := by simpa [endpoint_006,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((193/200):ℝ)
  · have v := @rightPrimalR006Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_006] using v
  · have v := @rightPrimalR006Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_006] using v
  · have v := @rightPrimalR006Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_006] using v
  · have v := @rightPrimalR006Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_006] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_006
