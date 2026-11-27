import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR000Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR000Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1709078613136318001614789,1718573494320477567548961,true⟩,⟨0,0,true⟩⟩, ⟨(-379795247363668217818059),(-360805484995417805436185),true⟩, ⟨3325018814125395000237427,3386397022750527195562254,true⟩⟩
theorem rightPrimalR000Q00P_ok : rightPrimalR000Q00P.encloses (primalThetaParameters rightPrimalR000Q00T (Grid.ofRats (9/10) (181/200))) := by decide +kernel

def rightPrimalR000Q00U : ℕ → ℚ
  | 0 => (-2503/1000)
  | 1 => (-2117/1000)
  | 2 => (-171/100)
  | 3 => (-371/250)
  | 4 => (-191/125)
  | 5 => (-917/500)
  | 6 => (-56/25)
  | 7 => (-2519/1000)
  | _ => 0
theorem rightPrimalR000Q00Sample0 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 0 (rightPrimalR000Q00U 0)=true := by decide +kernel
theorem rightPrimalR000Q00Sample1 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 1 (rightPrimalR000Q00U 1)=true := by decide +kernel
theorem rightPrimalR000Q00Sample2 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 2 (rightPrimalR000Q00U 2)=true := by decide +kernel
theorem rightPrimalR000Q00Sample3 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 3 (rightPrimalR000Q00U 3)=true := by decide +kernel
theorem rightPrimalR000Q00Sample4 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 4 (rightPrimalR000Q00U 4)=true := by decide +kernel
theorem rightPrimalR000Q00Sample5 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 5 (rightPrimalR000Q00U 5)=true := by decide +kernel
theorem rightPrimalR000Q00Sample6 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 6 (rightPrimalR000Q00U 6)=true := by decide +kernel
theorem rightPrimalR000Q00Sample7 : primalSampleCheck rightPrimalR000Q00T rightPrimalR000Q00P 7 (rightPrimalR000Q00U 7)=true := by decide +kernel

theorem rightPrimalR000Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((9/10):ℝ)≤a) (au : a≤((181/200):ℝ)) : thetaHorizontalPeriod t a≤(((-38221261534559097372905182055/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR000Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR000Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR000Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR000Q00Sample0
    · exact rightPrimalR000Q00Sample1
    · exact rightPrimalR000Q00Sample2
    · exact rightPrimalR000Q00Sample3
    · exact rightPrimalR000Q00Sample4
    · exact rightPrimalR000Q00Sample5
    · exact rightPrimalR000Q00Sample6
    · exact rightPrimalR000Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR000Q00_period_bound
