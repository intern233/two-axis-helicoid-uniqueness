import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR000Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR000Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1718573494320408848066751,1728068375504568414000954,true⟩,⟨0,0,true⟩⟩, ⟨(-360805484995486524914074),(-341815722627236112532261),true⟩, ⟨3317969050666725634094561,3379141969013404759577441,true⟩⟩
theorem rightPrimalR000Q01P_ok : rightPrimalR000Q01P.encloses (primalThetaParameters rightPrimalR000Q01T (Grid.ofRats (181/200) (91/100))) := by decide +kernel

def rightPrimalR000Q01U : ℕ → ℚ
  | 0 => (-627/250)
  | 1 => (-533/250)
  | 2 => (-431/250)
  | 3 => (-1491/1000)
  | 4 => (-61/40)
  | 5 => (-911/500)
  | 6 => (-1113/500)
  | 7 => (-2511/1000)
  | _ => 0
theorem rightPrimalR000Q01Sample0 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 0 (rightPrimalR000Q01U 0)=true := by decide +kernel
theorem rightPrimalR000Q01Sample1 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 1 (rightPrimalR000Q01U 1)=true := by decide +kernel
theorem rightPrimalR000Q01Sample2 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 2 (rightPrimalR000Q01U 2)=true := by decide +kernel
theorem rightPrimalR000Q01Sample3 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 3 (rightPrimalR000Q01U 3)=true := by decide +kernel
theorem rightPrimalR000Q01Sample4 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 4 (rightPrimalR000Q01U 4)=true := by decide +kernel
theorem rightPrimalR000Q01Sample5 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 5 (rightPrimalR000Q01U 5)=true := by decide +kernel
theorem rightPrimalR000Q01Sample6 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 6 (rightPrimalR000Q01U 6)=true := by decide +kernel
theorem rightPrimalR000Q01Sample7 : primalSampleCheck rightPrimalR000Q01T rightPrimalR000Q01P 7 (rightPrimalR000Q01U 7)=true := by decide +kernel

theorem rightPrimalR000Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((181/200):ℝ)≤a) (au : a≤((91/100):ℝ)) : thetaHorizontalPeriod t a≤(((-38221261534559097372905182055/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR000Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR000Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR000Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR000Q01Sample0
    · exact rightPrimalR000Q01Sample1
    · exact rightPrimalR000Q01Sample2
    · exact rightPrimalR000Q01Sample3
    · exact rightPrimalR000Q01Sample4
    · exact rightPrimalR000Q01Sample5
    · exact rightPrimalR000Q01Sample6
    · exact rightPrimalR000Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR000Q01_period_bound
