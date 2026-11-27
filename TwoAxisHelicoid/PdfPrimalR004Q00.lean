import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR004Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR004Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1785037662609044773230485,1804027424977295185616892,true⟩,⟨0,0,true⟩⟩, ⟨(-227877148418214674586183),(-189897623681782569300869),true⟩, ⟨3250415572557090840451568,3365397344654807879932565,true⟩⟩
theorem rightPrimalR004Q00P_ok : rightPrimalR004Q00P.encloses (primalThetaParameters rightPrimalR004Q00T (Grid.ofRats (47/50) (19/20))) := by decide +kernel

def rightPrimalR004Q00U : ℕ → ℚ
  | 0 => (-2471/1000)
  | 1 => (-2159/1000)
  | 2 => (-873/500)
  | 3 => (-1451/1000)
  | 4 => (-1401/1000)
  | 5 => (-203/125)
  | 6 => (-401/200)
  | 7 => (-469/200)
  | _ => 0
theorem rightPrimalR004Q00Sample0 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 0 (rightPrimalR004Q00U 0)=true := by decide +kernel
theorem rightPrimalR004Q00Sample1 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 1 (rightPrimalR004Q00U 1)=true := by decide +kernel
theorem rightPrimalR004Q00Sample2 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 2 (rightPrimalR004Q00U 2)=true := by decide +kernel
theorem rightPrimalR004Q00Sample3 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 3 (rightPrimalR004Q00U 3)=true := by decide +kernel
theorem rightPrimalR004Q00Sample4 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 4 (rightPrimalR004Q00U 4)=true := by decide +kernel
theorem rightPrimalR004Q00Sample5 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 5 (rightPrimalR004Q00U 5)=true := by decide +kernel
theorem rightPrimalR004Q00Sample6 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 6 (rightPrimalR004Q00U 6)=true := by decide +kernel
theorem rightPrimalR004Q00Sample7 : primalSampleCheck rightPrimalR004Q00T rightPrimalR004Q00P 7 (rightPrimalR004Q00U 7)=true := by decide +kernel

theorem rightPrimalR004Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((47/50):ℝ)≤a) (au : a≤((19/20):ℝ)) : thetaHorizontalPeriod t a≤(((-37233978647365851779223361019/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR004Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR004Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR004Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR004Q00Sample0
    · exact rightPrimalR004Q00Sample1
    · exact rightPrimalR004Q00Sample2
    · exact rightPrimalR004Q00Sample3
    · exact rightPrimalR004Q00Sample4
    · exact rightPrimalR004Q00Sample5
    · exact rightPrimalR004Q00Sample6
    · exact rightPrimalR004Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR004Q00_period_bound
