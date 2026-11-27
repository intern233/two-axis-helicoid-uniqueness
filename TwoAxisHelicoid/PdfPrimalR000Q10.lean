import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR000Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR000Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1709078613136318001614789,1718573494320477567548961,true⟩,⟨0,0,true⟩⟩, ⟨(-379795247363668217818059),(-360805484995417805436185),true⟩, ⟨3320264605922442468683491,3381429898400956028936730,true⟩⟩
theorem rightPrimalR000Q10P_ok : rightPrimalR000Q10P.encloses (primalThetaParameters rightPrimalR000Q10T (Grid.ofRats (9/10) (181/200))) := by decide +kernel

def rightPrimalR000Q10U : ℕ → ℚ
  | 0 => (-2501/1000)
  | 1 => (-2121/1000)
  | 2 => (-1719/1000)
  | 3 => (-187/125)
  | 4 => (-77/50)
  | 5 => (-1841/1000)
  | 6 => (-2241/1000)
  | 7 => (-629/250)
  | _ => 0
theorem rightPrimalR000Q10Sample0 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 0 (rightPrimalR000Q10U 0)=true := by decide +kernel
theorem rightPrimalR000Q10Sample1 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 1 (rightPrimalR000Q10U 1)=true := by decide +kernel
theorem rightPrimalR000Q10Sample2 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 2 (rightPrimalR000Q10U 2)=true := by decide +kernel
theorem rightPrimalR000Q10Sample3 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 3 (rightPrimalR000Q10U 3)=true := by decide +kernel
theorem rightPrimalR000Q10Sample4 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 4 (rightPrimalR000Q10U 4)=true := by decide +kernel
theorem rightPrimalR000Q10Sample5 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 5 (rightPrimalR000Q10U 5)=true := by decide +kernel
theorem rightPrimalR000Q10Sample6 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 6 (rightPrimalR000Q10U 6)=true := by decide +kernel
theorem rightPrimalR000Q10Sample7 : primalSampleCheck rightPrimalR000Q10T rightPrimalR000Q10P 7 (rightPrimalR000Q10U 7)=true := by decide +kernel

theorem rightPrimalR000Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((9/10):ℝ)≤a) (au : a≤((181/200):ℝ)) : thetaHorizontalPeriod t a≤(((-38221261534559097372905182055/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR000Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR000Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR000Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR000Q10Sample0
    · exact rightPrimalR000Q10Sample1
    · exact rightPrimalR000Q10Sample2
    · exact rightPrimalR000Q10Sample3
    · exact rightPrimalR000Q10Sample4
    · exact rightPrimalR000Q10Sample5
    · exact rightPrimalR000Q10Sample6
    · exact rightPrimalR000Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR000Q10_period_bound
