import TwoAxisHelicoid.PdfPrimalR002Q00
import TwoAxisHelicoid.PdfPrimalR002Q01
import TwoAxisHelicoid.PdfPrimalR002Q10
import TwoAxisHelicoid.PdfPrimalR002Q11

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem right_original_horizontal_002 {t a : ℝ} (tl : (7/5:ℝ)≤t) (tu : t≤141/100) (input : RealMem endpoint_002.a a) : thetaHorizontalPeriod t a≤(endpoint_002.hUpper:ℝ) := by
  have r : ((23/25):ℝ)≤a ∧ a≤((93/100):ℝ) := by simpa [endpoint_002,RealMem] using input
  change thetaHorizontalPeriod t a≤_
  by_cases ts : t≤281/200 <;> by_cases aBelow : a≤((37/40):ℝ)
  · have v := @rightPrimalR002Q00_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_002] using v
  · have v := @rightPrimalR002Q01_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_002] using v
  · have v := @rightPrimalR002Q10_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_002] using v
  · have v := @rightPrimalR002Q11_period_bound t a (by linarith) (by linarith) (by linarith [r.1]) (by linarith [r.2])
    simpa [endpoint_002] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_original_horizontal_002
