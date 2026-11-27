import TwoAxisHelicoid.CompactHorizontalLeftSums
import TwoAxisHelicoid.CompactRootStripAll
import TwoAxisHelicoid.PdfHorizontalIntegral

namespace TwoAxisHelicoid
open Set

/-- At this endpoint the two reported rational bounds hold for the whole closed
abscissa box passed to the original complex-path integral. -/
theorem compact_root_left_horizontal_path {a : ℝ} (al : (1469895579284285760424119244853/2475880078570760549798248448000:ℝ)≤a) (au : a≤(1469895579284285760424119248853/2475880078570760549798248448000:ℝ)) :
    (pdfPrimalHorizontalIntegral (54139230899/62500000000:ℝ) a).re ∈ Icc (317389346370953943564367760022705118429661074717/50216813883093446110686315385661331328818843555712276103168:ℝ) (317389359837432925716169499539170879672030303517/50216813883093446110686315385661331328818843555712276103168:ℝ) ∧
    (pdfPrimalHorizontalIntegral (54139230899/62500000000:ℝ) a).im = 0 := by
  rw [pdf_primal_horizontal_integral_real (by norm_num : 0<(54139230899/62500000000:ℝ)) a, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_,rfl⟩
  have sum := compactHorizontalLeftSum0_32 al au
  have strip := @PdfVertical.compact_original_root_strip (54139230899/62500000000:ℝ) a
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  have disc := PdfVertical.compact_root_theta_sampling (by norm_num) strip
  change |(1/32:ℝ)*horizontalSamplePrefix (54139230899/62500000000:ℝ) a 32 32-thetaHorizontalPeriod (54139230899/62500000000:ℝ) a|≤1/10^20 at disc
  push_cast at sum
  rw [show horizontalSamplePrefix (54139230899/62500000000:ℝ) a 32 0 = 0 by simp [horizontalSamplePrefix],sub_zero] at sum
  obtain ⟨l,u⟩ := abs_le.mp disc
  constructor <;> linarith [sum.1,sum.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_root_left_horizontal_path
