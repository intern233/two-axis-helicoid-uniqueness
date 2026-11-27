import TwoAxisHelicoid.CompactHorizontalRightSums
import TwoAxisHelicoid.CompactRootStripAll
import TwoAxisHelicoid.PdfHorizontalIntegral

namespace TwoAxisHelicoid
open Set

/-- At this endpoint the two reported rational bounds hold for the whole closed
abscissa box passed to the original complex-path integral. -/
theorem compact_root_right_horizontal_path {a : ℝ} (al : (4409686737855254420087965714223/7427640235712281649394745344000:ℝ)≤a) (au : a≤(4409686737855254420087965726223/7427640235712281649394745344000:ℝ)) :
    (pdfPrimalHorizontalIntegral (173245538877/200000000000:ℝ) a).re ∈ Icc (-46097756206738198339541754847764846153863912105/12554203470773361527671578846415332832204710888928069025792:ℝ) (-46097752840118437589784117229895587882833140393/12554203470773361527671578846415332832204710888928069025792:ℝ) ∧
    (pdfPrimalHorizontalIntegral (173245538877/200000000000:ℝ) a).im = 0 := by
  rw [pdf_primal_horizontal_integral_real (by norm_num : 0<(173245538877/200000000000:ℝ)) a, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_,rfl⟩
  have sum := compactHorizontalRightSum0_32 al au
  have strip := @PdfVertical.compact_original_root_strip (173245538877/200000000000:ℝ) a
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  have disc := PdfVertical.compact_root_theta_sampling (by norm_num) strip
  change |(1/32:ℝ)*horizontalSamplePrefix (173245538877/200000000000:ℝ) a 32 32-thetaHorizontalPeriod (173245538877/200000000000:ℝ) a|≤1/10^20 at disc
  push_cast at sum
  rw [show horizontalSamplePrefix (173245538877/200000000000:ℝ) a 32 0 = 0 by simp [horizontalSamplePrefix],sub_zero] at sum
  obtain ⟨l,u⟩ := abs_le.mp disc
  constructor <;> linarith [sum.1,sum.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_root_right_horizontal_path
